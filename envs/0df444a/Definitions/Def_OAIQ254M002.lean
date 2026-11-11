-- Prove2me | Definitions.Def_OAIQ254M002
-- name    : OAIQ254M002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:49:34.802262+00:00
-- url     : https://prove2.me/theorems/588dba8d-d54c-4a8a-9f6d-3e53eeac6c13
-- title:
--   Definitions bundle OAIQ254M002 of the split of OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 703 declarations of OpenAI's Lean: 296 definitions, 3 inductive types or structures, 19 instances and 385 theorems. The definitions and types are `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkLog`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.Data`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.Tags`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionRates.SelectedLabels`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionRates.Slot`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionRates.capacity`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionRates.denominator`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionRates.groupCount`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionRates.initialCount`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionRates.selectionRate`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.CIndex`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.CWords`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.Index`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.InitialIndex`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.InitialWords`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.Parts`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.Words`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.ZeroWords`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.cTensor`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.fromState`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.grouped`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.groupedMap`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.history`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.indexEquiv`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.initialTensor`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.joinParts`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.map`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.partsMap`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.partsTensor`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.stateWord`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.toState`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.zeroTensor`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.Columns`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.Middles`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.Rows`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.ZeroColumns`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.ZeroMiddles`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.ZeroRows`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.columnsFintype`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.combineMatrixMaps` and 259 more.
--
--   **Sources.** They come from these modules of lean/OAI/LinearAlgebra, in whole or in part: `MatrixFields_Arithmetic_CommonDimensions`, `MatrixFields_Arithmetic_MatrixMapDecidable`, `MatrixFields_Certificates_CertificatesReplay`, `MatrixFields_Construction_ActiveSums`, `MatrixFields_Construction_ExactStatisticWords`, `MatrixFields_Construction_FinalState`, `MatrixFields_Construction_GroupAssignmentRetention`, `MatrixFields_Construction_InitialState`, `MatrixFields_Construction_JointCanonicalMixed`, `MatrixFields_Construction_JointCoarseReorder`, `MatrixFields_Construction_JointMaskedAssignment`, `MatrixFields_Construction_OrderedLimits`, `MatrixFields_Construction_PairMarginals`, `MatrixFields_Construction_ShapeEncoding`, `MatrixFields_Construction_Subdivision`, `MatrixFields_Construction_ZeroFinish`, `MatrixFields_Entropy_InitialEntropy`, `MatrixFields_Entropy_InitialLeafRates`, `MatrixFields_Entropy_ParametersHalfLaws`, `MatrixFields_Entropy_StageCLaw`, `MatrixFields_Entropy_TerminalRates`, `MatrixFields_Entropy_TerminalStatisticLaws`, `MatrixFields_Entropy_ZeroLeafRates`, `MatrixFields_Extraction_ConstructionLabels`, `MatrixFields_Extraction_GroupPairWindows`, `MatrixFields_Extraction_GroupSelection`, `MatrixFields_Extraction_JointPairClassWindows`, `MatrixFields_Histories_CWShapePhysicalPermutation`, `MatrixFields_Histories_GroupOrbitCount`, `MatrixFields_Histories_GroupOrbitTransport`, `MatrixFields_Histories_HistoryChildLaws`, `MatrixFields_Histories_HistoryGroupCore`, `MatrixFields_Histories_HistoryIteration`, `MatrixFields_Histories_HistoryPositions`, `MatrixFields_Histories_HistoryRecoveryBudget`, `MatrixFields_Histories_HistorySums`, `MatrixFields_Histories_InheritedMaskMargins`, `MatrixFields_Histories_InverseLinearRecovery`, `MatrixFields_Histories_ScheduledPositivity`, `MatrixFields_Parameters_ComplementSums`, `MatrixFields_Parameters_GroupSelectionParameters`, `MatrixFields_Parameters_NativeCapacity`, `MatrixFields_Parameters_ParametersCompatibility`, `MatrixFields_Parameters_ParametersHalfComplement`, `MatrixFields_Parameters_ParametersWeights`, `MatrixFields_Parameters_PopulationCounts`, `MatrixFields_Parameters_StageCCapacity`, `MatrixFields_Parameters_TerminalPopulations`, `MatrixFields_Tensors_CWCompleteStatistics`, `MatrixFields_Tensors_CWStageCPlacements`, `MatrixFields_Tensors_CWStageCStatistics`, `MatrixFields_Tensors_CWWordDimensionParameters`, `MatrixFields_Tensors_CWZeroGeometry`, `MatrixFields_Tensors_TerminalRelabel`.
--
--   **Imports.** It imports the bundles `OAIQ254M000` and `OAIQ254M001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ254M007`, `OAIQ254M008`, `OAIQ254M009`, `OAIQ254M010` and `OAIQ254M011`; the statements `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkLog_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.eventually_nonempty`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.nativeH0_enclosed`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.roundedMarginal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U0_0_4Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U0_1_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U1_0_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U1_1_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_2_5Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4U0_0_4Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U0_1_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U0_4_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U1_0_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U1_3_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_2_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_3_1Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_4_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U1_1_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_6_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_1_5Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_2_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Ttotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Ttotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_1_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_2_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_3_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_2_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1S2_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeLBBall_sound`; the proofs of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkLog_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.eventually_nonempty`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.nativeH0_enclosed`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.roundedMarginal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.eventually_exists_selection_of_word_support`, `OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.uniformDegree_log_upper_of_word_support`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U0_0_4Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U0_1_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U1_0_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U1_1_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_2_5Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4U0_0_4Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U0_1_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U0_4_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U1_0_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U1_3_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_2_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_3_1Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_4_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U1_1_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_6_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_1_5Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_2_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Ttotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U0_2_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U0_2_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U1_1_2Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U1_2_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_0_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_0_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_1_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_2_0ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_2_0EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Ttotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_1_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U0_2_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U0_2_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U1_1_2Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U1_2_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_0_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_0_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_1_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_2_0ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_2_0EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_2_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_3_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_2_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1S2_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I0_sound`.
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
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_TerminalRelabel
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K A B C D E F : Type*} [CommSemiring K]

theorem matrixCoefficients_product [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (x : (A × D) × (B × E)) (y : (B × E) × (C × F)) (z : (C × F) × (A × D)) :
    product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)
      ((x.1.1, x.2.1), (x.1.2, x.2.2))
      ((y.1.1, y.2.1), (y.1.2, y.2.2))
      ((z.1.1, z.2.1), (z.1.2, z.2.2)) =
      matrixCoefficients (A × D) (B × E) (C × F) x y z := by
  simp only [product, matrixCoefficients, Prod.ext_iff]
  split_ifs <;> simp_all

end Tensor






end MatrixMultiplication.Foundation

end




section




noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.TerminalRelabel

variable {K I A B C I' A' B' C' : Type*} [CommSemiring K]

theorem directSum_matrix_pullback
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq I'] [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
    (eI : I' ≃ I) (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) :
    Tensor.pullback (taggedPair eI eA eB) (taggedPair eI eB eC) (taggedPair eI eC eA)
      (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
        Tensor.directSum (fun _ : I' => Tensor.matrixCoefficients (K := K) A' B' C') := by
  funext x y z
  simp only [Tensor.pullback, taggedPair, Tensor.directSum, Tensor.matrixCoefficients,
    eI.injective.eq_iff, eA.injective.eq_iff, eB.injective.eq_iff, eC.injective.eq_iff]

theorem directSum_matrix_restrict_equiv
    [Fintype I] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq I'] [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
    (eI : I' ≃ I) (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) :
    Tensor.restrict
      (fun x s => if s = taggedPair eI eA eB x then (1 : K) else 0)
      (fun y s => if s = taggedPair eI eB eC y then (1 : K) else 0)
      (fun z s => if s = taggedPair eI eC eA z then (1 : K) else 0)
      (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
        Tensor.directSum (fun _ : I' => Tensor.matrixCoefficients (K := K) A' B' C') := by
  rw [← Tensor.pullback_eq_restrict]
  exact directSum_matrix_pullback eI eA eB eC

theorem exists_directSum_matrix_restrict_equiv
    [Fintype I] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq I'] [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
    (eI : I' ≃ I) (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) :
    ∃ (a : (I' × (A' × B')) → (I × (A × B)) → K)
      (b : (I' × (B' × C')) → (I × (B × C)) → K)
      (c : (I' × (C' × A')) → (I × (C × A)) → K),
      Tensor.restrict a b c
        (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
          Tensor.directSum (fun _ : I' => Tensor.matrixCoefficients (K := K) A' B' C') :=
  ⟨_, _, _, directSum_matrix_restrict_equiv eI eA eB eC⟩

theorem directSum_matrix_restrict_of_card_eq
    (I A B C : Type*) [Fintype I] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {L a b c : ℕ} (hI : Fintype.card I = L) (hA : Fintype.card A = a)
    (hB : Fintype.card B = b) (hC : Fintype.card C = c) :
    ∃ (aa : (Fin L × (Fin a × Fin b)) → (I × (A × B)) → K)
      (bb : (Fin L × (Fin b × Fin c)) → (I × (B × C)) → K)
      (cc : (Fin L × (Fin c × Fin a)) → (I × (C × A)) → K),
      Tensor.restrict aa bb cc
        (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
          Tensor.directSum (fun _ : Fin L =>
            Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c)) :=
  exists_directSum_matrix_restrict_equiv
    (Fintype.equivFinOfCardEq hI).symm (Fintype.equivFinOfCardEq hA).symm
    (Fintype.equivFinOfCardEq hB).symm (Fintype.equivFinOfCardEq hC).symm

theorem directSum_matrix_restrict_fin
    (I A B C : Type*) [Fintype I] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    ∃ (a : (Fin (Fintype.card I) × (Fin (Fintype.card A) × Fin (Fintype.card B))) →
        (I × (A × B)) → K)
      (b : (Fin (Fintype.card I) × (Fin (Fintype.card B) × Fin (Fintype.card C))) →
        (I × (B × C)) → K)
      (c : (Fin (Fintype.card I) × (Fin (Fintype.card C) × Fin (Fintype.card A))) →
        (I × (C × A)) → K),
      Tensor.restrict a b c
        (Tensor.directSum (fun _ : I => Tensor.matrixCoefficients (K := K) A B C)) =
          Tensor.directSum (fun _ : Fin (Fintype.card I) =>
            Tensor.matrixCoefficients (K := K)
              (Fin (Fintype.card A)) (Fin (Fintype.card B)) (Fin (Fintype.card C))) :=
  directSum_matrix_restrict_of_card_eq I A B C rfl rfl rfl rfl

end MatrixMultiplication.TerminalRelabel

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_CommonDimensions
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CommonDimensions

variable {K H : Type*} [CommSemiring K] [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
theorem matrix_familyProduct (A B C : H → Type*)
    [∀ h, DecidableEq (A h)] [∀ h, DecidableEq (B h)] [∀ h, DecidableEq (C h)] :
    Tensor.pullback (pairWords A B) (pairWords B C) (pairWords C A)
      (familyProduct (fun h => Tensor.matrixCoefficients (K := K) (A h) (B h) (C h))) =
      Tensor.matrixCoefficients (∀ h, A h) (∀ h, B h) (∀ h, C h) := by
  classical
  funext x y z
  simp only [Tensor.pullback, pairWords, familyProduct, Tensor.matrixCoefficients,
    Equiv.coe_fn_mk]
  by_cases matched : x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1
  · simp [matched.1, matched.2.1, matched.2.2]
  · have mismatch : ¬ ∀ index : H,
        x.2 index = y.1 index ∧ y.2 index = z.1 index ∧ z.2 index = x.1 index := by
      intro pointwise
      exact matched ⟨funext (fun index => (pointwise index).1),
        funext (fun index => (pointwise index).2.1),
        funext (fun index => (pointwise index).2.2)⟩
    obtain ⟨index, mismatch⟩ := not_forall.mp mismatch
    simp only [matched, ite_false, if_false]
    apply Finset.prod_eq_zero (Finset.mem_univ index)
    simp only [mismatch, ite_false, if_false]

theorem matrix_familyProduct_restrict (A B C : H → Type*)
    [∀ h, Fintype (A h)] [∀ h, Fintype (B h)] [∀ h, Fintype (C h)]
    [∀ h, DecidableEq (A h)] [∀ h, DecidableEq (B h)] [∀ h, DecidableEq (C h)] :
    ∃ (a : ((∀ h, A h) × (∀ h, B h)) → (∀ h, A h × B h) → K)
      (b : ((∀ h, B h) × (∀ h, C h)) → (∀ h, B h × C h) → K)
      (c : ((∀ h, C h) × (∀ h, A h)) → (∀ h, C h × A h) → K),
      Tensor.restrict a b c
        (familyProduct (fun h => Tensor.matrixCoefficients (K := K) (A h) (B h) (C h))) =
        Tensor.matrixCoefficients (∀ h, A h) (∀ h, B h) (∀ h, C h) := by
  classical
  refine ⟨(fun x s => if s = pairWords A B x then 1 else 0),
    (fun y s => if s = pairWords B C y then 1 else 0),
    (fun z s => if s = pairWords C A z then 1 else 0), ?_⟩
  rw [← Tensor.pullback_eq_restrict]
  exact matrix_familyProduct A B C

end MatrixMultiplication.CommonDimensions

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_ParametersWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

theorem statisticWeight_kappa (i : Fin 6) :
    statisticWeight (kappa i) = 4 - statisticWeight i := by
  revert i
  decide +kernel

theorem splitSignature_complement (parents : List Shape) (data : List ℤ)
    (s u : Shape) (h : ∀ i, u i ≤ s i) :
    splitSignature parents data s (complement s u) = splitSignature parents data s u := by
  funext i
  simp only [splitSignature, complement, Nat.sub_sub_self (h i), min_comm]

theorem splitWeight_complement (parents : List Shape) (data : List ℤ)
    (s u : Shape) (h : ∀ i, u i ≤ s i) :
    splitWeight parents data s (complement s u) = splitWeight parents data s u := by
  simp only [splitWeight, splitSignature_complement parents data s u h]

theorem splitLaw_complement (parents : List Shape) (data : List ℤ)
    (s u : Shape) (h : ∀ i, u i ≤ s i)
    (hu : u ∈ below s) (hc : complement s u ∈ below s) :
    splitLaw parents data s (complement s u) = splitLaw parents data s u := by
  simp only [splitLaw, hu, hc, ite_true, if_true, splitWeight_complement parents data s u h]

theorem splitLaw_outside_support (parents : List Shape) (data : List ℤ)
    (s u : Shape) (hu : u ∉ below s) : splitLaw parents data s u = 0 := by
  simp only [splitLaw, hu, ite_false, if_false]

theorem zeroPairLaw_outside_support (t : Shape) (i j : Fin 6)
    (h : statisticWeight i + statisticWeight j ≠ shapeMax t) :
    zeroPairLaw t i j = 0 := by
  simp only [zeroPairLaw, h, ite_false, if_false]

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_StageCLaw
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.canonicalChildShape_branchShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.decode_encodePhysicalShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.decode_encodeShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodePhysicalShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodeShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodeShape_total _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.physicalShape_complement _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.physicalShape_source _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

theorem zero_table_arguments_bounded : ∀ n ∈ tablez, |n| ≤ 160000 := by decide +kernel

theorem stageA_support_complement : ∀ s ∈ positiveInitial, ∀ u ∈ below s,
    complement s u ∈ below s ∧ ∀ i, u i ≤ s i := by decide +kernel

theorem stageALaw_complement (s u : Shape) (hs : s ∈ positiveInitial) (hu : u ∈ below s) :
    stageALaw s (complement s u) = stageALaw s u := by
  obtain ⟨hc, hb⟩ := stageA_support_complement s hs u hu
  exact splitLaw_complement _ _ s u hb hu hc

theorem stageBLaw_complement (s u : Shape) (hs : s ∈ positiveSecond) (hu : u ∈ below s) :
    stageBLaw s (complement s u) = stageBLaw s u := by
  obtain ⟨hc, hb⟩ := stageB_support_complement s hs u hu
  exact splitLaw_complement _ _ s u hb hu hc

theorem littleLaw_normalized (t u : Shape) (w : Fin 3) :
    ∑ i : Fin 6, littleLaw t u w i = 1 := by
  by_cases h : u w = 2
  · simp only [littleLaw, h, ite_true, if_true]
    calc
      _ = ∑ i : Fin 6, ((if i = 2 then 1 - binaryParameter t u else 0) +
          (if i = 3 then binaryParameter t u else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = 2
        · subst i
          simp [show (2 : Fin 6) ≠ 3 by decide]
        · simp [hi]
      _ = 1 := by simp [Finset.sum_add_distrib]
  · simp [littleLaw, h]

theorem orderedPairWeight_positive (t : Shape) (i j : Fin 6) :
    0 < weight (orderedPairInteger t i j) := by
  apply weight_positive_of_argument_bound
  exact assigned_argument_bound _ tablez zero_table_arguments_bounded _

theorem orderedPairs_nonempty : ∀ t ∈ zeroSecond, orderedPairs t ≠ [] := by decide +kernel

theorem orderedPairs_support (t : Shape) (ij : PairSlot) (h : ij ∈ orderedPairs t) :
    statisticWeight ij.1 + statisticWeight ij.2 = shapeMax t := by
  simp only [orderedPairs, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨i, _, j, _, he⟩ := h
  split_ifs at he with hs
  · cases Option.some.inj he
    exact hs

theorem zeroPairLaw_normalized (t : Shape) (ht : t ∈ zeroSecond) :
    ((orderedPairs t).map (fun ij => zeroPairLaw t ij.1 ij.2)).sum = 1 := by
  have he : (orderedPairs t).map (fun ij => zeroPairLaw t ij.1 ij.2) =
      (orderedPairs t).map (fun ij => weight (orderedPairInteger t ij.1 ij.2) /
        ((orderedPairs t).map (fun p => weight (orderedPairInteger t p.1 p.2))).sum) := by
    apply List.map_congr_left
    intro ij hij
    simp only [zeroPairLaw, orderedPairs_support t ij hij, ite_true, if_true]
  rw [he, list_sum_map_div, div_self]
  exact ne_of_gt (list_sum_map_positive _ _ (orderedPairs_nonempty t ht)
    (fun p _ => orderedPairWeight_positive t p.1 p.2))

end MatrixMultiplication.AllFieldParameters

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators

theorem positive_four_shapes : ∀ u ∈ shapes 4, positive u = true →
    u = shape 1 1 2 ∨ u = shape 1 2 1 ∨ u = shape 2 1 1 := by
  decide +kernel

theorem stageC_children_geometry : ∀ u ∈ shapes 4, positive u = true →
    ∀ v ∈ below u,
      complement u v ∈ below u ∧
      (∀ i, v i ≤ u i) ∧
      (∃ i, v i = 0) ∧ (∃ i, complement u v i = 0) := by
  decide +kernel

end MatrixMultiplication.AllFieldHistory

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_CertificatesReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

namespace MatrixMultiplication.AllFieldCertificates.Replay

def checkLog (two a b : Ball) (w : LogWitness) : Bool :=
  decide (0 < a.lower ∧ 0 < w.denominator ∧ w.denominator ≤ w.numerator ∧
    w.numerator ≤ 2 * w.denominator ∧
    a.center = (w.numerator : ℚ) / w.denominator * (2 : ℚ) ^ w.exponent) &&
  contains (logResult two a w) b

end MatrixMultiplication.AllFieldCertificates.Replay

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointPairClassWindows
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [Fintype J]
  [DecidableEq I]

theorem samePopulation_card_mul (w : I → A) :
    Fintype.card {v : I → A // ∀ a, wordPopulation v a = wordPopulation w a} *
      (∏ a, (wordPopulation w a).factorial) = (Fintype.card I).factorial := by
  classical
  let G := DomMulAct (Equiv.Perm I)
  let : Fintype G := Fintype.ofEquiv (Equiv.Perm I) DomMulAct.mk
  let eOrbit : {v : I → A // ∀ a, wordPopulation v a = wordPopulation w a} ≃
      MulAction.orbit G w :=
    Equiv.subtypeEquivRight fun v => by
      rw [samePopulation_iff_permutation, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨e, he⟩
        exact ⟨DomMulAct.mk e, he⟩
      · rintro ⟨g, hg⟩
        exact ⟨DomMulAct.mk.symm g, hg⟩
  let eStab : MulAction.stabilizer G w ≃
      {e : Equiv.Perm I // w ∘ e = w} :=
    Equiv.subtypeEquiv DomMulAct.mk.symm fun _ => DomMulAct.mem_stabilizer_iff
  have hstab : Fintype.card (MulAction.stabilizer G w) =
      ∏ a, (wordPopulation w a).factorial := by
    rw [Fintype.card_congr eStab]
    exact DomMulAct.stabilizer_card w
  have hgroup : Fintype.card G = (Fintype.card I).factorial :=
    (Fintype.card_congr DomMulAct.mk.symm).trans Fintype.card_perm
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G w
  rw [← Fintype.card_congr eOrbit, hstab, hgroup] at h
  exact h

theorem exactWords_card (counts : A → ℕ) :
    Fintype.card (ExactWords counts) = Nat.multinomial Finset.univ counts := by
  classical
  obtain ⟨w⟩ := exactWords_nonempty counts
  let e : ExactWords counts ≃
      {v : Fin (∑ a, counts a) → A // ∀ a,
        wordPopulation v a = wordPopulation w.val a} :=
    Equiv.subtypeEquivRight fun v => by simp only [w.property]
  have h := samePopulation_card_mul w.val
  rw [← Fintype.card_congr e] at h
  simp only [w.property, Fintype.card_fin] at h
  exact Nat.eq_div_of_mul_eq_left
    (ne_of_gt (Nat.prod_factorial_pos Finset.univ counts)) h

end MatrixMultiplication.Foundation





end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_ShapeEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators

theorem complement_bounded {u v : Shape} (hu : ShapeBounded u) :
    ShapeBounded (complement u v) := fun i => (Nat.sub_le (u i) (v i)).trans (hu i)

theorem complement_total {u v : Shape} (h : ∀ i, v i ≤ u i) :
    shapeTotal (complement u v) = shapeTotal u - shapeTotal v := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [shapeTotal, complement]
  omega

theorem stageC_complement_spec (u : Shape) (hu : u ∈ shapes 4) (hpos : positive u = true)
    (i : Fin 4) : ShapeBounded (complement u (stageCAtom u i)) ∧
      shapeTotal (complement u (stageCAtom u i)) = 2 := by
  have hi := stageCAtom_mem u hu hpos i
  obtain ⟨_, hchild⟩ := stageC_shape_spec u hu hpos i
  exact ⟨complement_bounded (mem_shapes_bounded hu (by omega)),
    by rw [complement_total (below_le hi), mem_shapes_total hu, hchild]⟩

end MatrixMultiplication.AllFieldHistory

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_ComplementSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

theorem stageA_children_nodup : ∀ s ∈ positiveInitial, (below s).Nodup := by decide +kernel

theorem stageB_children_nodup : ∀ s ∈ positiveSecond, (below s).Nodup := by decide +kernel

theorem ordered_pairs_nodup : ∀ t ∈ zeroSecond, (orderedPairs t).Nodup := by decide +kernel

end MatrixMultiplication.AllFieldParameters

noncomputable section

namespace MatrixMultiplication.AllFieldParameters

theorem complement_involution_of_le (s u : Shape) (hu : ∀ i, u i ≤ s i) :
    complement s (complement s u) = u := by
  funext i
  exact Nat.sub_sub_self (hu i)

theorem stageA_complement_sum (s : Shape) (hs : s ∈ positiveInitial)
    (h : Shape → ℝ) :
    ((below s).map (fun u => (stageALaw s u : ℝ) * h (complement s u))).sum =
      ((below s).map (fun u => (stageALaw s u : ℝ) * h u)).sum := by
  apply list_weighted_involution_sum (below s) (complement s)
    (stageA_children_nodup s hs)
  · intro u hu
    exact (stageA_support_complement s hs u hu).1
  · intro u hu
    exact complement_involution_of_le s u (stageA_support_complement s hs u hu).2
  · intro u hu
    rw [stageALaw_complement s u hs hu]

theorem stageB_complement_sum (s : Shape) (hs : s ∈ positiveSecond)
    (h : Shape → ℝ) :
    ((below s).map (fun u => (stageBLaw s u : ℝ) * h (complement s u))).sum =
      ((below s).map (fun u => (stageBLaw s u : ℝ) * h u)).sum := by
  apply list_weighted_involution_sum (below s) (complement s)
    (stageB_children_nodup s hs)
  · intro u hu
    exact (stageB_support_complement s hs u hu).1
  · intro u hu
    exact complement_involution_of_le s u (stageB_support_complement s hs u hu).2
  · intro u hu
    rw [stageBLaw_complement s u hs hu]

end MatrixMultiplication.AllFieldParameters

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_ParametersCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

def statisticLaw (d : ℚ) (k : Fin 5) (i : Fin 6) : ℚ :=
  if k.val = 2 then
    if i = 2 then 1 - d else if i = 3 then d else 0
  else if i = singletonSlot k.val then 1 else 0

theorem statisticLaw_complement (d : ℚ) (k : Fin 5) (i : Fin 6) :
    statisticLaw d k (kappa i) = statisticLaw d (statisticComplement k) i := by
  fin_cases k <;> fin_cases i <;> rfl

theorem statisticLaw_outside_support (d : ℚ) (k : Fin 5) (i : Fin 6)
    (h : statisticWeight i ≠ k.val) : statisticLaw d k i = 0 := by
  fin_cases k <;> fin_cases i
  all_goals first | rfl | exact False.elim (h (by decide))

theorem littleLaw_eq_statisticLaw (t u : Shape) (w : Fin 3) (hw : u w < 5) (i : Fin 6) :
    littleLaw t u w i = statisticLaw (binaryParameter t u) ⟨u w, hw⟩ i := rfl

theorem littleLaw_outside_support (t u : Shape) (w : Fin 3) (hw : u w < 5) (i : Fin 6)
    (h : statisticWeight i ≠ u w) : littleLaw t u w i = 0 :=
  statisticLaw_outside_support _ ⟨u w, hw⟩ i h

theorem littleLaw_complement (t u : Shape) (w v : Fin 3)
    (hw : u w < 5) (hv : u v < 5) (hsum : u w + u v = 4) (i : Fin 6) :
    littleLaw t u w (kappa i) = littleLaw t u v i := by
  rw [littleLaw_eq_statisticLaw t u w hw, littleLaw_eq_statisticLaw t u v hv]
  have hk : (⟨u v, hv⟩ : Fin 5) = statisticComplement ⟨u w, hw⟩ := by
    apply Fin.ext
    simp only [statisticComplement]
    omega
  rw [hk]
  exact statisticLaw_complement _ _ _

theorem child_statistic_weight_bounded : ∀ t ∈ positiveSecond, ∀ u ∈ below t,
    ∀ w : Fin 3, u w < 5 := by decide +kernel

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ParametersHalfLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.canonicalChildShape_branchShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.decode_encodePhysicalShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.decode_encodeShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodePhysicalShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodeShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodeShape_total _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.physicalShape_complement _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.physicalShape_source _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

theorem orderedPairs_mem_iff (t : Shape) (i j : Fin 6) :
    (i,j) ∈ orderedPairs t ↔ statisticWeight i + statisticWeight j = shapeMax t := by
  constructor
  · exact orderedPairs_support t (i,j)
  · intro h
    apply List.mem_flatMap.mpr
    refine ⟨i, by simp, ?_⟩
    apply List.mem_filterMap.mpr
    exact ⟨j, by simp, by simp [h]⟩

theorem zeroPairLaw_nonnegative (t : Shape) (i j : Fin 6) : 0 ≤ zeroPairLaw t i j := by
  unfold zeroPairLaw
  split_ifs
  · exact div_nonneg (orderedPairWeight_positive t i j).le
      (list_sum_map_nonnegative _ _ (fun ij _ => (orderedPairWeight_positive t ij.1 ij.2).le))
  · exact le_rfl

theorem zeroPairLaw_full_normalized (t : Shape) (ht : t ∈ zeroSecond) :
    ∑ ij : PairSlot, zeroPairLaw t ij.1 ij.2 = 1 := by
  calc
    _ = ∑ ij ∈ (orderedPairs t).toFinset, zeroPairLaw t ij.1 ij.2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro ij _ hij
      have hs : statisticWeight ij.1 + statisticWeight ij.2 ≠ shapeMax t := by
        intro h
        exact hij (List.mem_toFinset.mpr ((orderedPairs_mem_iff t ij.1 ij.2).mpr h))
      simp [zeroPairLaw, hs]
    _ = ((orderedPairs t).map (fun ij => zeroPairLaw t ij.1 ij.2)).sum :=
      List.sum_toFinset _ (ordered_pairs_nodup t ht)
    _ = 1 := zeroPairLaw_normalized t ht

theorem sum_pair_mixture {A : Type*} (xs : List A) (mass : A → ℚ)
    (left right : A → Fin 6 → ℚ)
    (hl : ∀ x ∈ xs, ∑ i, left x i = 1)
    (hr : ∀ x ∈ xs, ∑ i, right x i = 1) :
    (∑ ij : PairSlot, (xs.map fun x => mass x * left x ij.1 * right x ij.2).sum) =
      (xs.map mass).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hleft := hl x (by simp)
    have hright := hr x (by simp)
    have hhead : (∑ ij : PairSlot, mass x * left x ij.1 * right x ij.2) = mass x := by
      simp [Fintype.sum_prod_type, ← Finset.mul_sum, hleft, hright]
    have htail := ih (fun y hy => hl y (by simp [hy])) (fun y hy => hr y (by simp [hy]))
    simpa only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, hhead] using
      congrArg (fun q : ℚ => mass x + q) htail

theorem positiveHalfLaw_normalized (t : Shape) (ht : t ∈ positiveSecond) (w : Fin 3) :
    ∑ ij : PairSlot, positiveHalfLaw t w ij = 1 := by
  unfold positiveHalfLaw
  rw [sum_pair_mixture _ _ _ _ (fun u _ => littleLaw_normalized t u w)
    (fun u _ => littleLaw_normalized t (complement t u) w)]
  exact stageBLaw_normalized t ht

def kappaEquiv : Fin 6 ≃ Fin 6 where
  toFun := kappa
  invFun := kappa
  left_inv := kappa_involution
  right_inv := kappa_involution

theorem sum_pair_kappa (f : PairSlot → ℚ) :
    (∑ ij : PairSlot, f (kappa ij.1, kappa ij.2)) = ∑ ij, f ij :=
  (Equiv.prodCongr kappaEquiv kappaEquiv).sum_comp f

theorem halfLaw_normalized (t : Shape) (ht : t ∈ shapes 8) (w : Fin 3) :
    ∑ ij : PairSlot, halfLaw t w ij = 1 := by
  by_cases hp : positive t = true
  · simp only [halfLaw, hp, ite_true, if_true]
    exact positiveHalfLaw_normalized t (List.mem_filter.mpr ⟨ht, hp⟩) w
  · have hz : t ∈ zeroSecond := by simp [zeroSecond, ht, hp]
    simp only [halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
    by_cases hw : t w = 0
    · simp [hw]
    · simp only [hw, ite_false, if_false]
      by_cases hm : w = halfMaxAxis t
      · simpa only [hm, ite_true, if_true] using zeroPairLaw_full_normalized t hz
      · simp only [hm, ite_false, if_false]
        rw [sum_pair_kappa (fun ij => zeroPairLaw t ij.1 ij.2)]
        exact zeroPairLaw_full_normalized t hz

theorem positiveHalfLaw_outside_support (t : Shape) (ht : t ∈ positiveSecond)
    (w : Fin 3) (ij : PairSlot)
    (h : statisticWeight ij.1 + statisticWeight ij.2 ≠ t w) :
    positiveHalfLaw t w ij = 0 := by
  unfold positiveHalfLaw
  have he : (below t).map (fun u => stageBLaw t u * littleLaw t u w ij.1 *
      littleLaw t (complement t u) w ij.2) = (below t).map (fun _ => (0 : ℚ)) := by
    apply List.map_congr_left
    intro u hu
    obtain ⟨hc, hb⟩ := stageB_support_complement t ht u hu
    by_cases hi : statisticWeight ij.1 = u w
    · have hj : statisticWeight ij.2 ≠ complement t u w := by
        intro hj
        apply h
        rw [hi, hj]
        change u w + (t w - u w) = t w
        have hw := hb w
        omega
      rw [littleLaw_outside_support t (complement t u) w
        (child_statistic_weight_bounded t ht (complement t u) hc w) ij.2 hj, mul_zero]
    · rw [littleLaw_outside_support t u w
        (child_statistic_weight_bounded t ht u hu w) ij.1 hi, mul_zero, zero_mul]
  rw [he]
  simp

theorem halfMaxAxis_spec : ∀ t ∈ shapes 8, t (halfMaxAxis t) = shapeMax t := by
  decide +kernel

theorem zero_other_axis_spec : ∀ t ∈ zeroSecond, ∀ w : Fin 3,
    t w ≠ 0 → w ≠ halfMaxAxis t → t w + shapeMax t = 8 := by decide +kernel

theorem statisticWeight_le_four (i : Fin 6) : statisticWeight i ≤ 4 := by
  revert i
  decide +kernel

theorem halfLaw_outside_support (t : Shape) (ht : t ∈ shapes 8)
    (w : Fin 3) (ij : PairSlot)
    (h : statisticWeight ij.1 + statisticWeight ij.2 ≠ t w) :
    halfLaw t w ij = 0 := by
  by_cases hp : positive t = true
  · simp only [halfLaw, hp, ite_true, if_true]
    exact positiveHalfLaw_outside_support t (List.mem_filter.mpr ⟨ht, hp⟩) w ij h
  · have hz : t ∈ zeroSecond := by simp [zeroSecond, ht, hp]
    simp only [halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
    by_cases hw : t w = 0
    · have hij : ij ≠ (0,0) := by
        intro hij
        apply h
        rw [hij, hw]
        rfl
      rw [ite_eq_left hw, ite_eq_right hij]
    · simp only [hw, ite_false, if_false]
      by_cases hm : w = halfMaxAxis t
      · have hs : statisticWeight ij.1 + statisticWeight ij.2 ≠ shapeMax t := by
          simpa only [hm, halfMaxAxis_spec t ht] using h
        simp [hm, zeroPairLaw, hs]
      · have hs : statisticWeight (kappa ij.1) + statisticWeight (kappa ij.2) ≠
            shapeMax t := by
          have htotal := zero_other_axis_spec t hz w hw hm
          have hi := statisticWeight_le_four ij.1
          have hj := statisticWeight_le_four ij.2
          simp only [statisticWeight_kappa]
          omega
        simp [hm, zeroPairLaw, hs]

theorem zero_nonzero_axes_distinguished : ∀ t ∈ zeroSecond, ∀ w v : Fin 3,
    t w ≠ 0 → t v ≠ 0 → w ≠ v →
      (w = halfMaxAxis t ↔ v ≠ halfMaxAxis t) := by decide +kernel

theorem halfLaw_zero_complement (t : Shape) (ht : t ∈ zeroSecond)
    (w v : Fin 3) (hw : t w ≠ 0) (hv : t v ≠ 0) (hwv : w ≠ v) (ij : PairSlot) :
    halfLaw t w (kappa ij.1, kappa ij.2) = halfLaw t v ij := by
  have hp : positive t ≠ true := by
    have h := (List.mem_filter.mp ht).2
    simpa using h
  have hm := zero_nonzero_axes_distinguished t ht w v hw hv hwv
  by_cases ha : w = halfMaxAxis t
  · have hb : v ≠ halfMaxAxis t := hm.mp ha
    have hmax : t (halfMaxAxis t) ≠ 0 := by simpa only [ha] using hw
    simp [halfLaw, hp, hv, ha, hb, hmax]
  · have hb : v = halfMaxAxis t := by
      by_contra hne
      exact ha (hm.mpr hne)
    have hmax : t (halfMaxAxis t) ≠ 0 := by simpa only [hb] using hv
    simp [halfLaw, hp, hw, ha, hb, hmax, kappa_involution]

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_PopulationCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldPopulationCounts

open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem denominator_pos (w : I → ℚ) : 0 < denominator w := by
  exact Finset.prod_pos fun i _ => (w i).den_pos

theorem count_zero_iff (w : I → ℚ) (hw : ∀ i, 0 ≤ w i)
    {m : ℕ} (hm : 0 < m) (i : I) : count w m i = 0 ↔ w i = 0 := by
  have hD : (denominator w : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (denominator_pos w))
  have hM : (m : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have h : (count w m i : ℚ) = 0 ↔ w i = 0 := by
    rw [count_cast w hw]
    simp only [mul_eq_zero, hM, hD, false_or]
  simpa only [Nat.cast_eq_zero] using h

theorem count_pos_iff (w : I → ℚ) (hw : ∀ i, 0 ≤ w i)
    {m : ℕ} (hm : 0 < m) (i : I) : 0 < count w m i ↔ 0 < w i := by
  rw [Nat.pos_iff_ne_zero, ne_eq, count_zero_iff w hw hm]
  constructor
  · intro h
    exact lt_of_le_of_ne (hw i) (Ne.symm h)
  · exact ne_of_gt

end

end MatrixMultiplication.AllFieldPopulationCounts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InverseLinearRecovery
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial




section
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.InverseLinearRecovery

def RecoveredBy {K X Y Z : Type*} [CommSemiring K]
    [Fintype X] [Fintype Y] [Fintype Z]
    (Q H : Tensor K X Y Z) (L : ℕ) : Prop :=
  ∃ (a : X → (MaskRectangles L × X) → K)
    (b : Y → (MaskRectangles L × Y) → K)
    (c : Z → (MaskRectangles L × Z) → K),
    Tensor.restrict a b c (Tensor.directSum (fun _ : MaskRectangles L => H)) = Q

end MatrixMultiplication.InverseLinearRecovery

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InheritedMaskMargins
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCanonicalization.positionEquiv_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCanonicalization.positionEquiv_symm_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.InheritedMasks

open MatrixMultiplication.Foundation
open scoped BigOperators

section ClassWords

variable {C : Type*} (P A : C → Type*)
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

omit [∀ c, DecidableEq (P c)] [∀ c, Fintype (A c)] in
theorem sameClassOrbit_iff (w v : ClassWords P A) :
    SameClassOrbit P A w v ↔
      ∀ c a, wordPopulation (v c) a = wordPopulation (w c) a := by
  constructor
  · rintro ⟨e, he⟩ c a
    rw [← he c]
    exact wordPopulation_reindex (w c) (e c) a
  · intro h
    have he : ∀ c, ∃ e : Equiv.Perm (P c), w c ∘ e = v c :=
      fun c => (samePopulation_iff_permutation (w c) (v c)).mp (h c)
    choose e he using he
    exact ⟨e, he⟩

noncomputable def profile (w : ClassWords P A) : Profile P A :=
  fun c a => ⟨wordPopulation (w c) a,
    Nat.lt_succ_of_le (Fintype.card_subtype_le _)⟩

omit [∀ c, DecidableEq (P c)] [∀ c, Fintype (A c)] in
theorem profile_eq_iff (w v : ClassWords P A) :
    profile P A w = profile P A v ↔ SameClassOrbit P A w v := by
  rw [sameClassOrbit_iff]
  constructor
  · intro h c a
    have hh := congrArg (fun f : Profile P A => (f c a).val) h
    exact hh.symm
  · intro h
    funext c a
    apply Fin.ext
    exact (h c a).symm

end ClassWords

section EmpiricalWindows

variable {P A B : Type*} [Fintype P] [DecidableEq P]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq P] [Fintype A] [Fintype B] in
theorem wordPopulation_equiv (w : P → A) (e : A ≃ B) (a : A) :
    wordPopulation (e ∘ w) (e a) = wordPopulation w a := by
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun i => e.injective.eq_iff

omit [DecidableEq P] [Fintype A] [Fintype B] in
theorem typeWindow_equiv (ν : A → ℝ) (η : ℝ) (w : P → A) (e : A ≃ B) :
    typeWindow (ν ∘ e.symm) η (e ∘ w) ↔ typeWindow ν η w := by
  constructor
  · intro h a
    have hh := h (e a)
    simpa [empiricalLaw, wordPopulation_equiv] using hh
  · intro h b
    obtain ⟨a, rfl⟩ := e.surjective b
    simpa [empiricalLaw, wordPopulation_equiv] using h a

end EmpiricalWindows

end MatrixMultiplication.InheritedMasks

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.PermutationMatching
open MatrixMultiplication.InheritedMasks

namespace MatrixMultiplication.HistorySymmetry

variable {C : Type*} {P X Y : C → Type*}

section Coefficients

variable {K : Type*} [CommSemiring K] [Fintype C] [∀ c, Fintype (P c)]
    {XL YL ZL XR YR ZR : C → Type*}

def pairClassProduct
    (TL : ∀ c, Tensor K (XL c) (YL c) (ZL c))
    (TR : ∀ c, Tensor K (XR c) (YR c) (ZR c)) :
    Tensor K (CompleteWordPair P XL XR) (CompleteWordPair P YL YR) (CompleteWordPair P ZL ZR) :=
  fun x y z => classProduct TL x.left y.left z.left * classProduct TR x.right y.right z.right

end Coefficients

section Windows

variable [Fintype C] [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
    {SL SR : C → Type*} [∀ c, Fintype (SL c)] [∀ c, Fintype (SR c)]
    [∀ c, DecidableEq (SL c)] [∀ c, DecidableEq (SR c)]

def childWindows (sl : ∀ c, X c → SL c) (sr : ∀ c, Y c → SR c)
    (νl : ∀ c, SL c → ℝ) (νr : ∀ c, SR c → ℝ) (ηl ηr : C → ℝ)
    (w : CompleteWordPair P X Y) : Prop :=
  ∀ c, typeWindow (νl c) (ηl c) (sl c ∘ w.left c) ∧
    typeWindow (νr c) (ηr c) (sr c ∘ w.right c)

end Windows

end MatrixMultiplication.HistorySymmetry

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_ExactStatisticWords
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCanonicalization.positionEquiv_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCanonicalization.positionEquiv_symm_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.LeafVolumes

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {F U : Type*} [CommSemiring F] [DecidableEq U]

def zeroXMatching : Tensor F Unit U U := fun _ y z => if y = z then 1 else 0

theorem zeroXMatching_matrixCoefficients :
    Tensor.pullback (fun _ : Unit × Unit => ())
      (fun y : Unit × U => y.2) (fun z : U × Unit => z.1)
      (zeroXMatching (F := F) (U := U)) =
    Tensor.matrixCoefficients Unit Unit U := by
  funext x y z
  simp [Tensor.pullback, zeroXMatching, Tensor.matrixCoefficients]

theorem matchingPower_leaf {X Y Z : Type*} [DecidableEq Y]
    (T : Tensor F X Y Z) (x₀ : X) (e : Y ≃ Z)
    (hmatch : ∀ y z, T x₀ y (e z) = if y = z then 1 else 0)
    (n : ℕ) (p : (Fin n → Y) → Prop) [DecidablePred p] :
    Tensor.pullback (fun _ : Unit => fun _ : Fin n => x₀)
      (Subtype.val : {w // p w} → (Fin n → Y))
      (fun w : {w // p w} => fun i => e (w.val i)) (Tensor.power T n) =
      zeroXMatching (F := F) (U := {w // p w}) := by
  funext x y z
  simp only [Tensor.pullback, Tensor.power, hmatch, zeroXMatching,
    Fintype.prod_boole, ← funext_iff, Subtype.ext_iff]

theorem matchingPower_matrixCoefficients {X Y Z : Type*} [DecidableEq Y]
    (T : Tensor F X Y Z) (x₀ : X) (e : Y ≃ Z)
    (hmatch : ∀ y z, T x₀ y (e z) = if y = z then 1 else 0)
    (n : ℕ) (p : (Fin n → Y) → Prop) [DecidablePred p] :
    Tensor.pullback (fun _ : Unit × Unit => fun _ : Fin n => x₀)
      (fun y : Unit × {w // p w} => y.2.val)
      (fun z : {w // p w} × Unit => fun i => e (z.1.val i))
      (Tensor.power T n) =
      Tensor.matrixCoefficients Unit Unit {w // p w} := by
  have h := matchingPower_leaf T x₀ e hmatch n p
  have hp := congrArg (Tensor.pullback (fun _ : Unit × Unit => ())
    (fun y : Unit × {w // p w} => y.2)
    (fun z : {w // p w} × Unit => z.1)) h
  rw [zeroXMatching_matrixCoefficients] at hp
  exact hp

section ExactLabeledWords

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem labelings_card {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → A) (b : A → ℕ) :
    Fintype.card (∀ i, Fin (b (w i))) =
      ∏ a, b a ^ wordPopulation w a := by
  classical
  simp only [Fintype.card_pi, Fintype.card_fin]
  calc
    (∏ i, b (w i)) = ∏ s : Σ a, {i // w i = a}, b s.1 := by
      rw [← (Equiv.sigmaFiberEquiv w).prod_comp (fun i => b (w i))]
      apply Finset.prod_congr rfl
      intro s _
      exact congrArg b s.2.property
    _ = ∏ a, b a ^ wordPopulation w a := by
      simp [Fintype.prod_sigma, wordPopulation]

end ExactLabeledWords

end MatrixMultiplication.LeafVolumes





noncomputable section

namespace MatrixMultiplication.ExactStatisticWords

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {A U : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]

abbrev Words (statistic : U → A) (counts : A → ℕ) :=
  {w : Fin (∑ a, counts a) → U //
    ∀ a, wordPopulation (statistic ∘ w) a = counts a}

def statisticWord (statistic : U → A) (counts : A → ℕ)
    (w : Words statistic counts) : ExactWords counts :=
  ⟨statistic ∘ w.val, w.property⟩

def fiberEquiv (statistic : U → A) (counts : A → ℕ) (w : ExactWords counts) :
    {v : Words statistic counts // statisticWord statistic counts v = w} ≃
      {v : Fin (∑ a, counts a) → U // ∀ i, statistic (v i) = w.val i} where
  toFun v := ⟨v.val.val, fun i => congrFun (congrArg Subtype.val v.property) i⟩
  invFun v := by
    have heq : statistic ∘ v.val = w.val := funext v.property
    let v' : Words statistic counts := ⟨v.val, fun a => by
      rw [heq]
      exact w.property a⟩
    exact ⟨v', Subtype.ext heq⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv v := by
    apply Subtype.ext
    rfl

omit [DecidableEq U] in
theorem card (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, Fintype.card {u : U // statistic u = a} = b a) :
    Fintype.card (Words statistic counts) =
      Nat.multinomial Finset.univ counts * ∏ a, b a ^ counts a := by
  classical
  have hfiber (w : ExactWords counts) :
      Fintype.card {v : Words statistic counts // statisticWord statistic counts v = w} =
        ∏ a, b a ^ counts a := by
    let e : {v : Fin (∑ a, counts a) → U // ∀ i, statistic (v i) = w.val i} ≃
        (∀ i : Fin (∑ a, counts a), {u : U // statistic u = w.val i}) :=
      { toFun := fun v i => ⟨v.val i, v.property i⟩
        invFun := fun v => ⟨fun i => (v i).val, fun i => (v i).property⟩
        left_inv := by intro v; rfl
        right_inv := by intro v; rfl }
    rw [Fintype.card_congr (fiberEquiv statistic counts w),
      Fintype.card_congr e, Fintype.card_pi]
    simp only [hb]
    have h := LeafVolumes.labelings_card w.val b
    simpa only [Fintype.card_pi, Fintype.card_fin, w.property] using h
  calc
    Fintype.card (Words statistic counts) =
        Fintype.card (Σ w : ExactWords counts,
          {v : Words statistic counts // statisticWord statistic counts v = w}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv (statisticWord statistic counts))).symm
    _ = Nat.multinomial Finset.univ counts * ∏ a, b a ^ counts a := by
      simp only [Fintype.card_sigma, hfiber, Finset.sum_const, Finset.card_univ,
        smul_eq_mul, exactWords_card]

omit [DecidableEq U] in
theorem card_of_supported (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, 0 < counts a → Fintype.card {u : U // statistic u = a} = b a) :
    Fintype.card (Words statistic counts) =
      Nat.multinomial Finset.univ counts * ∏ a, b a ^ counts a := by
  rw [card statistic counts (fun a => Fintype.card {u : U // statistic u = a})
    (fun _ => rfl)]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  by_cases ha : counts a = 0
  · simp [ha]
  · rw [hb a (Nat.pos_of_ne_zero ha)]

omit [DecidableEq U] in
theorem card_pos_of_supported (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, 0 < counts a → Fintype.card {u : U // statistic u = a} = b a)
    (hpos : ∀ a, 0 < counts a → 0 < b a) :
    0 < Fintype.card (Words statistic counts) := by
  rw [card_of_supported statistic counts b hb]
  apply Nat.mul_pos (Nat.multinomial_pos Finset.univ counts)
  apply Finset.prod_pos
  intro a _
  by_cases ha : counts a = 0
  · simp [ha]
  · exact pow_pos (hpos a (Nat.pos_of_ne_zero ha)) _

end MatrixMultiplication.ExactStatisticWords

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointMaskedAssignment
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section






namespace MatrixMultiplication.JointCanonicalization

open MatrixMultiplication.Foundation JointPopulation InheritedMasks
open PermutationMatching HistorySymmetry
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ)

variable (L R : H → Type*)

section Windows

variable {SL SR : H → Type*}
    [∀ h, Fintype (SL h)] [∀ h, Fintype (SR h)]
    [∀ h, DecidableEq (SL h)] [∀ h, DecidableEq (SR h)]
    (sl : ∀ c : ClassKey (H := H), L c.1 → SL c.1)
    (sr : ∀ c : ClassKey (H := H), R c.1 → SR c.1)
    (νl : ∀ c : ClassKey (H := H), SL c.1 → ℝ)
    (νr : ∀ c : ClassKey (H := H), SR c.1 → ℝ)
    (ηl ηr : ClassKey (H := H) → ℝ)

def activeLaw {S : H → Type*} (ν : ∀ c : ClassKey (H := H), S c.1 → ℝ)
    (c : ClassKey (H := H)) : S c.1 → ℝ :=
  fun a => if 0 < counts c.1 c.2 then ν c a else 0

def activeWidth (η : ClassKey (H := H) → ℝ) (c : ClassKey (H := H)) : ℝ :=
  if 0 < counts c.1 c.2 then η c else 0

end Windows

section Coefficients

variable {F : Type*} [CommSemiring F]
    (T : ∀ h, Tensor F (L h × R h) (L h × R h) (L h × R h))
    (coarse : Fin 3 → ∀ h, L h × R h → Fin 17)

def sourceTensor : Tensor F (RawPairs counts L R) (RawPairs counts L R)
    (RawPairs counts L R) := classProduct T

def block (c : ClassKey (H := H)) :
    Tensor F (L c.1 × R c.1) (L c.1 × R c.1) (L c.1 × R c.1) :=
  fun x y z => if coarse 0 c.1 x = c.2.1 ∧ coarse 1 c.1 y = c.2.2.1 ∧
      coarse 2 c.1 z = c.2.2.2 then T c.1 x y z else 0

def canonicalBase : Tensor F (CanonicalPairs counts L R) (CanonicalPairs counts L R)
    (CanonicalPairs counts L R) :=
  fun x y z => ∏ c, ∏ j, block L R T coarse c
    (x.left c j, x.right c j) (y.left c j, y.right c j) (z.left c j, z.right c j)

section ChildWindows

variable {SL SR : H → Type*}
    [∀ h, Fintype (SL h)] [∀ h, Fintype (SR h)]
    [∀ h, DecidableEq (SL h)] [∀ h, DecidableEq (SR h)]
    (sl : Fin 3 → ∀ c : ClassKey (H := H), L c.1 → SL c.1)
    (sr : Fin 3 → ∀ c : ClassKey (H := H), R c.1 → SR c.1)
    (νl : Fin 3 → ∀ c : ClassKey (H := H), SL c.1 → ℝ)
    (νr : Fin 3 → ∀ c : ClassKey (H := H), SR c.1 → ℝ)
    (ηl ηr : Fin 3 → ClassKey (H := H) → ℝ)

def canonicalIdeal : Tensor F (CanonicalPairs counts L R) (CanonicalPairs counts L R)
    (CanonicalPairs counts L R) :=
  ExactRecovery.delete (canonicalBase counts L R T coarse)
    (childWindows (sl 0) (sr 0) (activeLaw counts (νl 0)) (activeLaw counts (νr 0))
      (activeWidth counts (ηl 0)) (activeWidth counts (ηr 0)))
    (childWindows (sl 1) (sr 1) (activeLaw counts (νl 1)) (activeLaw counts (νr 1))
      (activeWidth counts (ηl 1)) (activeWidth counts (ηr 1)))
    (childWindows (sl 2) (sr 2) (activeLaw counts (νl 2)) (activeLaw counts (νr 2))
      (activeWidth counts (ηl 2)) (activeWidth counts (ηr 2)))

end ChildWindows

end Coefficients

end MatrixMultiplication.JointCanonicalization






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWCompleteStatistics
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.branchPositionEquiv_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodePhysicalShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodeShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.fourStatistic_append _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.initialExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section




namespace MatrixMultiplication.CWLeafRestrictions

open MatrixMultiplication.Foundation

theorem tensor_middle_zero_matching (F : Type*) [CommRing F] (q : ℕ)
    (x z : Fin (q + 2)) :
    FieldCW.tensor F q x 0 (complement q z) = if x = z then 1 else 0 := by
  rw [FieldCW.tensor_cyclic F q x 0 (complement q z)]
  have h := tensor_zero_matching F q (complement q z) (complement q x)
  simpa only [complement_involution, Equiv.apply_eq_iff_eq, eq_comm] using h

theorem tensor_last_zero_matching (F : Type*) [CommRing F] (q : ℕ)
    (x y : Fin (q + 2)) :
    FieldCW.tensor F q x (complement q y) 0 = if x = y then 1 else 0 := by
  rw [FieldCW.tensor_cyclic F q x (complement q y) 0,
    FieldCW.tensor_cyclic F q (complement q y) 0 x]
  exact tensor_zero_matching F q x y

theorem zeroX_leaf (F : Type*) [CommRing F] (q n : ℕ)
    (p : (Fin n → Fin (q + 2)) → Prop) [DecidablePred p] :
    Tensor.pullback (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin (q + 2)))
      (fun y : Unit × {w // p w} => y.2.val)
      (fun z : {w // p w} × Unit => fun i => complement q (z.1.val i))
      (Tensor.power (FieldCW.tensor F q) n) =
      Tensor.matrixCoefficients Unit Unit {w // p w} :=
  LeafVolumes.matchingPower_matrixCoefficients (FieldCW.tensor F q) 0
    (complement q) (tensor_zero_matching F q) n p

theorem zeroY_leaf (F : Type*) [CommRing F] (q n : ℕ)
    (p : (Fin n → Fin (q + 2)) → Prop) [DecidablePred p] :
    Tensor.pullback (fun x : {w // p w} × Unit => x.1.val)
      (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin (q + 2)))
      (fun z : Unit × {w // p w} => fun i => complement q (z.2.val i))
      (Tensor.power (FieldCW.tensor F q) n) =
      Tensor.matrixCoefficients {w // p w} Unit Unit := by
  funext x y z
  simp only [Tensor.pullback, Tensor.power, tensor_middle_zero_matching,
    Fintype.prod_boole, ← funext_iff, Tensor.matrixCoefficients]
  simp [Subtype.ext_iff, eq_comm]

theorem zeroZ_leaf (F : Type*) [CommRing F] (q n : ℕ)
    (p : (Fin n → Fin (q + 2)) → Prop) [DecidablePred p] :
    Tensor.pullback (fun x : Unit × {w // p w} => x.2.val)
      (fun y : {w // p w} × Unit => fun i => complement q (y.1.val i))
      (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin (q + 2)))
      (Tensor.power (FieldCW.tensor F q) n) =
      Tensor.matrixCoefficients Unit {w // p w} Unit := by
  funext x y z
  simp only [Tensor.pullback, Tensor.power, tensor_last_zero_matching,
    Fintype.prod_boole, ← funext_iff, Tensor.matrixCoefficients]
  simp [Subtype.ext_iff]

end MatrixMultiplication.CWLeafRestrictions





namespace MatrixMultiplication.CWLeafStatistics

open MatrixMultiplication.Foundation

theorem statistic_weight : ∀ x : Fin 7 × Fin 7,
    AllFieldParameters.statisticWeight (pairStatistic x) = weight x.1 + weight x.2 := by
  decide +kernel

theorem pair_multiplicity : ∀ i : Fin 6,
    Fintype.card {x : Fin 7 × Fin 7 // pairStatistic x = i} =
      AllFieldParameters.multiplicity i := by
  decide +kernel

theorem complement_statistic : ∀ x : Fin 7 × Fin 7,
    pairStatistic (CWLeafRestrictions.complement 5 x.1,
      CWLeafRestrictions.complement 5 x.2) =
      AllFieldParameters.kappa (pairStatistic x) := by
  decide +kernel

theorem ordered_pair_multiplicity (i j : Fin 6) :
    Fintype.card {x : (Fin 7 × Fin 7) × (Fin 7 × Fin 7) //
      pairStatistic x.1 = i ∧ pairStatistic x.2 = j} =
      AllFieldParameters.multiplicity i * AllFieldParameters.multiplicity j := by
  let e : {x : (Fin 7 × Fin 7) × (Fin 7 × Fin 7) //
      pairStatistic x.1 = i ∧ pairStatistic x.2 = j} ≃
      {x : Fin 7 × Fin 7 // pairStatistic x = i} ×
        {x : Fin 7 × Fin 7 // pairStatistic x = j} :=
    { toFun := fun x => (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
      invFun := fun x => ⟨(x.1.val, x.2.val), x.1.property, x.2.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, pair_multiplicity, pair_multiplicity]

end MatrixMultiplication.CWLeafStatistics





noncomputable section






namespace MatrixMultiplication.CWStrands

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {F : Type*} [CommRing F]

theorem weight_sum_elim {P Q : Type*} [Fintype P] [Fintype Q]
    (x : P → Fin 7) (y : Q → Fin 7) :
    weight (Sum.elim x y) = weight x + weight y := by
  simp [weight, Fintype.sum_sum_type]

theorem strand_sum_elim {P Q : Type*} [Fintype P] [Fintype Q]
    (x : (P → Fin 7) × (Q → Fin 7))
    (y : (P → Fin 7) × (Q → Fin 7))
    (z : (P → Fin 7) × (Q → Fin 7)) :
    strand (F := F) (P ⊕ Q) (Sum.elim x.1 x.2) (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) =
      Tensor.product (strand P) (strand Q) x y z := by
  simp [strand, Tensor.product, Fintype.prod_sum_type]

theorem shape_split {P Q : Type*} [Fintype P] [Fintype Q]
    (u v : Fin 3 → ℕ)
    (x : (P → Fin 7) × (Q → Fin 7))
    (y : (P → Fin 7) × (Q → Fin 7))
    (z : (P → Fin 7) × (Q → Fin 7)) :
    (if weight x.1 = u 0 ∧ weight y.1 = u 1 ∧ weight z.1 = u 2 then
      shapeTensor (F := F) (P ⊕ Q) (u + v) (Sum.elim x.1 x.2) (Sum.elim y.1 y.2)
        (Sum.elim z.1 z.2) else 0) =
      Tensor.product (shapeTensor P u) (shapeTensor Q v) x y z := by
  classical
  simp only [shapeTensor, weight_sum_elim, Pi.add_apply, strand_sum_elim,
    Tensor.product]
  by_cases hx : weight x.1 = u 0
  · by_cases hy : weight y.1 = u 1
    · by_cases hz : weight z.1 = u 2
      · simp [hx, hy, hz, mul_ite]
      · simp [hz]
    · simp [hy]
  · simp [hx]

end MatrixMultiplication.CWStrands






namespace MatrixMultiplication.JointCanonicalCW

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization
open CWStrands HistorySymmetry InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [CommRing F]
    (counts : H → Shape → ℕ) (leftLength rightLength : H → ℕ)
    (parentShape : H → Fin 3 → ℕ)
    (hleft : ∀ h, leftLength h ≤ 8)

def parentTensor (h : H) : Tensor F
    (Left leftLength h × Right rightLength h)
    (Left leftLength h × Right rightLength h)
    (Left leftLength h × Right rightLength h) :=
  fun x y z => shapeTensor (Fin (leftLength h) ⊕ Fin (rightLength h)) (parentShape h)
    (Sum.elim x.1 x.2) (Sum.elim y.1 y.2) (Sum.elim z.1 z.2)

def leftTensor (c : ClassKey (H := H)) :
    Tensor F (Left leftLength c.1) (Left leftLength c.1) (Left leftLength c.1) :=
  shapeTensor (Fin (leftLength c.1)) (shapeNat c.2)

def rightTensor (c : ClassKey (H := H)) :
    Tensor F (Right rightLength c.1) (Right rightLength c.1) (Right rightLength c.1) :=
  shapeTensor (Fin (rightLength c.1)) (parentShape c.1 - shapeNat c.2)

omit [Fintype H] [DecidableEq H] in
theorem block_eq_product (h : H) (u : Shape)
    (hu : ∀ s, shapeNat u s ≤ parentShape h s) :
    block (Left leftLength) (Right rightLength)
      (parentTensor leftLength rightLength parentShape)
      (coarse leftLength rightLength hleft) (h, u) =
      Tensor.product (leftTensor (F := F) leftLength (h, u))
        (rightTensor rightLength parentShape (h, u)) := by
  have hadd : shapeNat u + (parentShape h - shapeNat u) = parentShape h := by
    funext s
    exact Nat.add_sub_of_le (hu s)
  funext x y z
  have hs := shape_split (F := F) (P := Fin (leftLength h))
    (Q := Fin (rightLength h)) (shapeNat u) (parentShape h - shapeNat u) x y z
  rw [hadd] at hs
  simpa [block, parentTensor, coarse, CWCoarseIndices.coarseIndex,
    Fin.ext_iff, leftTensor, rightTensor, shapeNat, shapeSide,
    Fin.isValue, ↓reduceIte] using hs

omit [DecidableEq H] in
theorem canonicalBase_eq_children
    (hsupport : ∀ h u, 0 < counts h u → ∀ s, shapeNat u s ≤ parentShape h s) :
    canonicalBase counts (Left leftLength) (Right rightLength)
      (parentTensor leftLength rightLength parentShape)
      (coarse leftLength rightLength hleft) =
      pairClassProduct (leftTensor (F := F) leftLength)
        (rightTensor rightLength parentShape) := by
  funext x y z
  unfold canonicalBase
  have hf : (∏ c : ClassKey (H := H), ∏ j : ClassPositions counts c,
      block (Left leftLength) (Right rightLength)
        (parentTensor leftLength rightLength parentShape)
        (coarse leftLength rightLength hleft) c
        (x.left c j, x.right c j) (y.left c j, y.right c j) (z.left c j, z.right c j)) =
      ∏ c : ClassKey (H := H), ∏ j : ClassPositions counts c,
        (leftTensor (F := F) leftLength c (x.left c j) (y.left c j) (z.left c j) *
          rightTensor rightLength parentShape c (x.right c j) (y.right c j) (z.right c j)) := by
    apply Finset.prod_congr rfl
    intro c _
    apply Finset.prod_congr rfl
    intro j _
    have hc : 0 < counts c.1 c.2 := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
    rw [block_eq_product leftLength rightLength parentShape hleft c.1 c.2
      (hsupport c.1 c.2 hc)]
    rfl
  rw [hf]
  simp only [pairClassProduct, classProduct, Finset.prod_mul_distrib]

end MatrixMultiplication.JointCanonicalCW






namespace MatrixMultiplication.CWShapeLeaves

open MatrixMultiplication.Foundation CWStrands CWLeafRestrictions
open scoped BigOperators

theorem complement_word_weight {P : Type*} [Fintype P] (w : P → Fin 7) :
    weight (fun i => complement 5 (w i)) + weight w = 2 * Fintype.card P := by
  calc
    weight (fun i => complement 5 (w i)) + weight w =
        ∑ i, (CWLeafStatistics.weight (complement 5 (w i)) + CWLeafStatistics.weight (w i)) := by
      simp [weight, Finset.sum_add_distrib]
    _ = ∑ _i : P, 2 := Finset.sum_congr rfl (fun i _ => CWLeafStatistics.complement_weight (w i))
    _ = 2 * Fintype.card P := by simp [Nat.mul_comm]

theorem zeroX_shape_leaf (F : Type*) [CommRing F] (n a b : ℕ)
    (hab : a + b = 2 * n)
    (p : (Fin n → Fin 7) → Prop) [DecidablePred p]
    (hp : ∀ w, p w → weight w = a) :
    Tensor.pullback (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin 7))
      (fun y : Unit × {w // p w} => y.2.val)
      (fun z : {w // p w} × Unit => fun i => complement 5 (z.1.val i))
      (shapeTensor (F := F) (Fin n) (Matrix.vecCons (0) (Matrix.vecCons (a) (Matrix.vecCons (b) Matrix.vecEmpty)))) =
      Tensor.matrixCoefficients Unit Unit {w // p w} := by
  funext x y z
  have hy : weight y.2.val = a := hp _ y.2.property
  have hz : weight (fun i => complement 5 (z.1.val i)) = b := by
    have hw := complement_word_weight z.1.val
    have hzw : weight z.1.val = a := hp _ z.1.property
    simp only [Fintype.card_fin] at hw
    omega
  have hzero : weight (fun _ : Fin n => (0 : Fin 7)) = 0 := by
    simp [weight, CWLeafStatistics.weight]
  have hleaf := congrFun (congrFun (congrFun (zeroX_leaf F 5 n p) x) y) z
  simpa [Tensor.pullback, shapeTensor, hzero, hy, hz, strand, Tensor.power] using hleaf

theorem zeroY_shape_leaf (F : Type*) [CommRing F] (n a b : ℕ)
    (hab : a + b = 2 * n)
    (p : (Fin n → Fin 7) → Prop) [DecidablePred p]
    (hp : ∀ w, p w → weight w = a) :
    Tensor.pullback (fun x : {w // p w} × Unit => x.1.val)
      (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin 7))
      (fun z : Unit × {w // p w} => fun i => complement 5 (z.2.val i))
      (shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (0) (Matrix.vecCons (b) Matrix.vecEmpty)))) =
      Tensor.matrixCoefficients {w // p w} Unit Unit := by
  funext x y z
  have hx : weight x.1.val = a := hp _ x.1.property
  have hz : weight (fun i => complement 5 (z.2.val i)) = b := by
    have hw := complement_word_weight z.2.val
    have hzw : weight z.2.val = a := hp _ z.2.property
    simp only [Fintype.card_fin] at hw
    omega
  have hzero : weight (fun _ : Fin n => (0 : Fin 7)) = 0 := by
    simp [weight, CWLeafStatistics.weight]
  have hleaf := congrFun (congrFun (congrFun (zeroY_leaf F 5 n p) x) y) z
  simpa [Tensor.pullback, shapeTensor, hzero, hx, hz, strand, Tensor.power] using hleaf

theorem zeroZ_shape_leaf (F : Type*) [CommRing F] (n a b : ℕ)
    (hab : a + b = 2 * n)
    (p : (Fin n → Fin 7) → Prop) [DecidablePred p]
    (hp : ∀ w, p w → weight w = a) :
    Tensor.pullback (fun x : Unit × {w // p w} => x.2.val)
      (fun y : {w // p w} × Unit => fun i => complement 5 (y.1.val i))
      (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin 7))
      (shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (b) (Matrix.vecCons (0) Matrix.vecEmpty)))) =
      Tensor.matrixCoefficients Unit {w // p w} Unit := by
  funext x y z
  have hx : weight x.2.val = a := hp _ x.2.property
  have hy : weight (fun i => complement 5 (y.1.val i)) = b := by
    have hw := complement_word_weight y.1.val
    have hyw : weight y.1.val = a := hp _ y.1.property
    simp only [Fintype.card_fin] at hw
    omega
  have hzero : weight (fun _ : Fin n => (0 : Fin 7)) = 0 := by
    simp [weight, CWLeafStatistics.weight]
  have hleaf := congrFun (congrFun (congrFun (zeroZ_leaf F 5 n p) x) y) z
  simpa [Tensor.pullback, shapeTensor, hzero, hx, hy, strand, Tensor.power] using hleaf

end MatrixMultiplication.CWShapeLeaves






namespace MatrixMultiplication.CWWindowedLeaves

open MatrixMultiplication.Foundation CWStrands CWShapeLeaves CWLeafRestrictions InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

abbrev Alphabet (n a : ℕ) := {w : Raw n // weight w = a}

def complementWord {n : ℕ} (w : Raw n) : Raw n := fun i => complement 5 (w i)
def zeroWord (n : ℕ) : Raw n := fun _ => 0

variable (F : Type*) [CommRing F]

theorem zeroX_local (n a b : ℕ) (hab : a + b = 2 * n)
    (u v : Alphabet n a) :
    shapeTensor (F := F) (Fin n) (Matrix.vecCons (0) (Matrix.vecCons (a) (Matrix.vecCons (b) Matrix.vecEmpty))) (zeroWord n) u.val (complementWord v.val) =
      if u = v then 1 else 0 := by
  unfold zeroWord complementWord
  have h := zeroX_shape_leaf F n a b hab (fun w => weight w = a) (fun _ h => h)
  have hh := congrFun (congrFun (congrFun h ((), ())) ((), u)) (v, ())
  simpa only [Tensor.pullback, Tensor.matrixCoefficients,
    true_and, and_true] using hh

theorem zeroY_local (n a b : ℕ) (hab : a + b = 2 * n)
    (u v : Alphabet n a) :
    shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (0) (Matrix.vecCons (b) Matrix.vecEmpty))) u.val (zeroWord n) (complementWord v.val) =
      if u = v then 1 else 0 := by
  unfold zeroWord complementWord
  have h := zeroY_shape_leaf F n a b hab (fun w => weight w = a) (fun _ h => h)
  have hh := congrFun (congrFun (congrFun h (u, ())) ((), ())) ((), v)
  have huv : (v = u) ↔ (u = v) := eq_comm
  simpa only [Tensor.pullback, Tensor.matrixCoefficients,
    true_and, and_true, huv] using hh

theorem zeroZ_local (n a b : ℕ) (hab : a + b = 2 * n)
    (u v : Alphabet n a) :
    shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (b) (Matrix.vecCons (0) Matrix.vecEmpty))) u.val (complementWord v.val) (zeroWord n) =
      if u = v then 1 else 0 := by
  unfold zeroWord complementWord
  have h := zeroZ_shape_leaf F n a b hab (fun w => weight w = a) (fun _ h => h)
  have hh := congrFun (congrFun (congrFun h ((), u)) (v, ())) ((), ())
  simpa only [Tensor.pullback, Tensor.matrixCoefficients,
    true_and, and_true] using hh

section ExactWindows

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [Fintype A] in
theorem zero_window (n m : ℕ) (hm : 0 < m) (statistic : Raw n → A)
    (ν : A → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hν : ∀ s, ν s = if statistic (zeroWord n) = s then 1 else 0) :
    typeWindow ν η (fun _ : Fin m => statistic (zeroWord n)) := by
  intro s
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  by_cases hs : statistic (zeroWord n) = s <;>
    simpa [empiricalLaw, wordPopulation, hν s, hs, hm'] using hη

end ExactWindows

end MatrixMultiplication.CWWindowedLeaves






namespace MatrixMultiplication.CWCompleteStatistics

open CWWindowedLeaves CWLeafStatistics CWStrands AllFieldParameters
open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem two_weight (w : Raw 2) :
    CWStrands.weight w = statisticWeight (twoStatistic w) := by
  rw [twoStatistic, statistic_weight]
  simp [CWStrands.weight, pairEquiv, Fin.sum_univ_succ]

theorem four_weight (w : Raw 4) :
    CWStrands.weight w = statisticWeight (fourStatistic w).1 +
      statisticWeight (fourStatistic w).2 := by
  simp only [fourStatistic, statistic_weight]
  simp [CWStrands.weight, orderedEquiv, Fin.sum_univ_succ, Nat.add_assoc]

theorem two_multiplicity (s : Fin 6) :
    Fintype.card {w : Raw 2 // twoStatistic w = s} = AllFieldParameters.multiplicity s := by
  let e : {w : Raw 2 // twoStatistic w = s} ≃
      {u : Fin 7 × Fin 7 // pairStatistic u = s} :=
    { toFun := fun w => ⟨pairEquiv w.val, w.property⟩
      invFun := fun u => ⟨pairEquiv.symm u.val, by simpa [twoStatistic] using u.property⟩
      left_inv := by intro w; apply Subtype.ext; simp
      right_inv := by intro u; apply Subtype.ext; simp }
  rw [Fintype.card_congr e, pair_multiplicity]

theorem four_multiplicity (s : Fin 6 × Fin 6) :
    Fintype.card {w : Raw 4 // fourStatistic w = s} =
      AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2 := by
  let e : {w : Raw 4 // fourStatistic w = s} ≃
      {u : (Fin 7 × Fin 7) × (Fin 7 × Fin 7) //
        pairStatistic u.1 = s.1 ∧ pairStatistic u.2 = s.2} :=
    { toFun := fun w => ⟨orderedEquiv w.val,
        congrArg Prod.fst w.property, congrArg Prod.snd w.property⟩
      invFun := fun u => ⟨orderedEquiv.symm u.val, by
        apply Prod.ext
        · simpa [fourStatistic] using u.property.1
        · simpa [fourStatistic] using u.property.2⟩
      left_inv := by intro w; apply Subtype.ext; simp
      right_inv := by intro u; apply Subtype.ext; simp }
  rw [Fintype.card_congr e, ordered_pair_multiplicity]

theorem two_complement (w : Raw 2) :
    twoStatistic (complementWord w) = complementStatistic (twoStatistic w) := by
  exact complement_statistic (pairEquiv w)

theorem four_complement (w : Raw 4) :
    fourStatistic (complementWord w) = orderedComplementStatistic (fourStatistic w) := by
  apply Prod.ext
  · exact complement_statistic (orderedEquiv w).1
  · exact complement_statistic (orderedEquiv w).2

theorem two_fixedWeight_multiplicity (a : ℕ) (s : Fin 6) (hs : statisticWeight s = a) :
    Fintype.card {w : Alphabet 2 a // twoStatistic w.val = s} =
      AllFieldParameters.multiplicity s := by
  rw [ExactStatisticWords.card_fixedWeight_fiber twoStatistic CWStrands.weight
    statisticWeight two_weight a s hs, two_multiplicity]

theorem four_fixedWeight_multiplicity (a : ℕ) (s : Fin 6 × Fin 6)
    (hs : statisticWeight s.1 + statisticWeight s.2 = a) :
    Fintype.card {w : Alphabet 4 a // fourStatistic w.val = s} =
      AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2 := by
  rw [ExactStatisticWords.card_fixedWeight_fiber fourStatistic CWStrands.weight
    (fun s => statisticWeight s.1 + statisticWeight s.2) four_weight a s hs,
    four_multiplicity]

end MatrixMultiplication.CWCompleteStatistics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryChildLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instDecidableEqResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first
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

def minCapacity (a : Capacity) : ℝ := min (a 0) (min (a 1) (a 2))

end MatrixMultiplication.Staggering

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.FiniteSchedule

open Staggering

theorem stageActive_iff_unique_lot (K tick : ℕ) (stage : Fin 3) :
    stageActive K tick stage ↔ ∃! j : Fin K, lotTick j stage = tick := by
  constructor
  · rintro ⟨hle, hlt⟩
    refine ⟨⟨tick - stage.val, by omega⟩, ?_, ?_⟩
    · dsimp [lotTick]
      omega
    · intro j hj
      apply Fin.ext
      dsimp [lotTick] at hj ⊢
      omega
  · rintro ⟨j, hj, _⟩
    have hjlt := j.isLt
    dsimp [stageActive, lotTick] at *
    omega

theorem lot_active_at_its_tick {K : ℕ} (j : Fin K) (stage : Fin 3) :
    stageActive K (lotTick j stage) stage := by
  have hj := j.isLt
  dsimp [stageActive, lotTick]
  omega

def tickCapacity (K : ℕ) (a b c : Capacity) (tick : ℕ) : Capacity := fun i =>
  (if stageActive K tick 0 then a i else 0) +
    (if stageActive K tick 1 then b i else 0) +
    (if stageActive K tick 2 then c i else 0)

end MatrixMultiplication.FiniteSchedule

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.PhysicalOrders

open Staggering

theorem sum_selected_placement (rho sigma : PhysicalOrder) (value : ℝ) :
    (∑ phi : PhysicalOrder, if rho.trans phi = sigma then value else 0) = value := by
  classical
  obtain ⟨phi, hphi, hunique⟩ := physical_order_unique rho sigma
  calc
    _ = ∑ psi : PhysicalOrder, if psi = phi then value else 0 := by
      apply Finset.sum_congr rfl
      intro psi _
      have hiff : rho.trans psi = sigma ↔ psi = phi := by
        constructor
        · exact hunique psi
        · rintro rfl
          exact hphi
      simp only [hiff]
    _ = value := by simp

variable {History : Type*} [Fintype History]

def aggregateCapacity (amount : History → ℝ) (capacity : History → Capacity) : Capacity :=
  fun i => ∑ h, amount h * capacity h i

def perPhysicalOrderCapacity (amount : History → ℝ) (capacity : History → Capacity)
    (priority : History → PhysicalOrder) (sigma : PhysicalOrder) : Capacity := by
  classical
  exact fun i => ∑ h, ∑ phi : PhysicalOrder,
    if (priority h).trans phi = sigma then amount h / 6 * capacity h i else 0

theorem perPhysicalOrderCapacity_apply (amount : History → ℝ)
    (capacity : History → Capacity) (priority : History → PhysicalOrder)
    (sigma : PhysicalOrder) (i : Fin 3) :
    perPhysicalOrderCapacity amount capacity priority sigma i =
      (1 / 6 : ℝ) * aggregateCapacity amount capacity i := by
  classical
  unfold perPhysicalOrderCapacity aggregateCapacity
  simp only [sum_selected_placement]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem perPhysicalOrderCapacity_eq (amount : History → ℝ)
    (capacity : History → Capacity) (priority : History → PhysicalOrder)
    (sigma : PhysicalOrder) :
    perPhysicalOrderCapacity amount capacity priority sigma =
      fun i => (1 / 6 : ℝ) * aggregateCapacity amount capacity i := by
  funext i
  exact perPhysicalOrderCapacity_apply amount capacity priority sigma i

theorem minCapacity_mul (a : Capacity) (r : ℝ) (hr : 0 ≤ r) :
    minCapacity (fun i => r * a i) = r * minCapacity a := by
  unfold minCapacity
  rw [mul_min_of_nonneg _ _ hr, mul_min_of_nonneg _ _ hr]

end MatrixMultiplication.PhysicalOrders

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem aShape_mem {K : ℕ} (h : AfterA K) : aShape h ∈ below (initialShape h.1.val) := by
  have hc := (stageA_support_complement _ h.1.property _ (aSplit_mem h)).1
  cases hh : h.2.2 <;> simp [aShape, halfShape, hh, aSplit_mem h, hc]

theorem stageA_children_size : ∀ g ∈ positiveInitial, ∀ t ∈ below g, t ∈ shapes 8 := by
  decide +kernel

theorem aShape_size {K : ℕ} (h : AfterA K) : aShape h ∈ shapes 8 :=
  stageA_children_size _ h.1.property _ (aShape_mem h)

theorem cShape_zero {K : ℕ} (h : AfterC K) : ∃ i, cShape h i = 0 := by
  have hg := stageC_children_geometry (cShapeParent h.1)
    (bShape_size h.1.1.val) h.1.1.property (cSplit h)
    (stageCAtom_mem _ (bShape_size h.1.1.val) h.1.1.property h.2.1)
  cases hh : h.2.2 with
  | false => simpa [cShape, halfShape, hh] using hg.2.2.1
  | true => simpa [cShape, halfShape, hh] using hg.2.2.2

theorem a_transition {K : ℕ} (h : InitialPositive K) (right : Bool) :
    ∑ k : ASplit h, aAmount ⟨h, k, right⟩ = initialAmount h.val := by
  change (∑ k : ASplit h, initialAmount h.val *
    stageALaw (initialShape h.val) (below (initialShape h.val))[k.val]) = _
  rw [← Finset.mul_sum, Fin.sum_univ_fun_getElem,
    stageALaw_normalized _ h.property, mul_one]

theorem b_transition {K : ℕ} (h : APositive K) (right : Bool) :
    ∑ k : BSplit h, bAmount ⟨h, k, right⟩ = aAmount h.val := by
  change (∑ k : BSplit h, aAmount h.val *
    stageBLaw (aShape h.val) (below (aShape h.val))[k.val]) = _
  rw [← Finset.mul_sum, Fin.sum_univ_fun_getElem,
    stageBLaw_normalized _ h.property, mul_one]

theorem part_transition {K : ℕ} (allocation : Allocation) (h : BPositive K) :
    ∑ i : Fin 3, partAmount allocation (h, i) = bAmount h.val := by
  simp only [partAmount, ← Finset.mul_sum, allocation.total, mul_one]

theorem c_transition {K : ℕ} (allocation : Allocation) (h : PartC K) (right : Bool) :
    ∑ k : Fin 4, cAmount allocation (h, k, right) = partAmount allocation h := by
  simp only [cAmount, ← Finset.mul_sum, stageCWeight_normalized, mul_one]

theorem a_population_transition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : InitialPositive K) (right : Bool) (phi : Placement) :
    (∑ k : ASplit h, population allocation dilation (.afterA ⟨h, k, right⟩, phi)) =
      population allocation dilation (.initial h.val, phi) := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, amount, canonicalAmount,
    ← Finset.mul_sum, ← Finset.sum_div, a_transition]

theorem b_population_transition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : APositive K) (right : Bool) (phi : Placement) :
    (∑ k : BSplit h, population allocation dilation (.afterB ⟨h, k, right⟩, phi)) =
      population allocation dilation (.afterA h.val, phi) := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, amount, canonicalAmount,
    ← Finset.mul_sum, ← Finset.sum_div, b_transition]

theorem part_population_transition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : BPositive K) (phi : Placement) :
    (∑ i : Fin 3, population allocation dilation (.partC (h, i), phi)) =
      population allocation dilation (.afterB h.val, phi) := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, amount, canonicalAmount,
    ← Finset.mul_sum, ← Finset.sum_div, part_transition]

theorem c_population_transition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : PartC K) (right : Bool) (phi : Placement) :
    (∑ k : Fin 4, population allocation dilation (.afterC (h, k, right), phi)) =
      population allocation dilation (.partC h, phi) := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, amount, canonicalAmount,
    ← Finset.mul_sum, ← Finset.sum_div, c_transition]

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem branchPopulation_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) :
    (∑ b : w.1.Branch, branchPopulation allocation dilation w b) =
      population allocation dilation (w.1.source, w.2) := by
  rcases w with ⟨w, phi⟩
  cases w with
  | stageA h => exact a_population_transition allocation dilation h false phi
  | stageB h => exact b_population_transition allocation dilation h false phi
  | stageC h => exact c_population_transition allocation dilation h false phi

def terminal {K : ℕ} : CanonicalHistory K → Prop
  | .initial h => initialShape h ∉ positiveInitial
  | .afterA h => aShape h ∉ positiveSecond
  | .afterB h => positive (bShape h) ≠ true
  | .partC _ => False
  | .afterC _ => True

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem Work.splitShape_le {K : ℕ} (w : Work K) (b : w.Branch) :
    ∀ i, w.splitShape b i ≤ w.parentShape i := by
  cases w with
  | stageA h => exact below_le (aSplit_mem ⟨h, b, false⟩)
  | stageB h => exact below_le (bSplit_mem ⟨h, b, false⟩)
  | stageC h => exact below_le (stageCAtom_mem _ (bShape_size h.1.val) h.1.property b)

theorem jointCounts_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) : ∑ u, jointCounts allocation dilation w u =
      population allocation dilation (w.1.source, w.2) := by
  rw [jointCounts, shapeCounts_sum, branchPopulation_sum]

theorem jointCounts_support_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : 0 < jointCounts allocation dilation w u) :
    u.1.val + u.2.1.val + u.2.2.val = 2 * w.1.halfLength := by
  obtain ⟨b, rfl, _⟩ := shapeCounts_positive _ _ u hu
  exact (encodePhysicalShape_total _ _ _).trans (w.1.splitShape_spec b).2

theorem jointCounts_support_le {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : 0 < jointCounts allocation dilation w u) (s : Fin 3) :
    (JointPopulation.shapeSide s u).val ≤ physicalShape w.2 w.1.parentShape s := by
  obtain ⟨b, rfl, _⟩ := shapeCounts_positive _ _ u hu
  rw [branchShape, encodePhysicalShape_side]
  exact w.1.splitShape_le b (w.2.symm s)

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters

abbrev CanonicalActive (K tick : ℕ) :=
  {w : Work K // FiniteSchedule.lotTick w.lot w.stage = tick}

def activeAggregateCapacity {K : ℕ} (allocation : Allocation) (tick : ℕ)
    (capacity : Work K → Staggering.Capacity) : Staggering.Capacity :=
  PhysicalOrders.aggregateCapacity (fun w : CanonicalActive K tick => workAmount allocation w.val)
    (fun w => capacity w.val)

def physicalTickCapacity {K : ℕ} (allocation : Allocation) (tick : ℕ)
    (capacity : Work K → Staggering.Capacity) (sigma : Placement) : Staggering.Capacity :=
  fun i => ∑ w : CanonicalActive K tick, ∑ phi : Placement,
    if PlacedWork.physicalOrder (w.val, phi) = sigma then
      (amount allocation (w.val.source, phi) : ℝ) * capacity w.val i else 0

theorem physicalTickCapacity_eq_partition {K : ℕ} (allocation : Allocation) (tick : ℕ)
    (capacity : Work K → Staggering.Capacity) (sigma : Placement) :
    physicalTickCapacity allocation tick capacity sigma =
      PhysicalOrders.perPhysicalOrderCapacity
        (fun w : CanonicalActive K tick => workAmount allocation w.val)
        (fun w => capacity w.val) (fun w => w.val.priority) sigma := by
  funext i
  simp only [physicalTickCapacity, PhysicalOrders.perPhysicalOrderCapacity,
    PlacedWork.physicalOrder, amount, workAmount, Rat.cast_div, Rat.cast_ofNat]

theorem physicalTickCapacity_eq_sixth {K : ℕ} (allocation : Allocation) (tick : ℕ)
    (capacity : Work K → Staggering.Capacity) (sigma : Placement) :
    physicalTickCapacity allocation tick capacity sigma =
      fun i => (1 / 6 : ℝ) * activeAggregateCapacity allocation tick capacity i := by
  rw [physicalTickCapacity_eq_partition]
  exact PhysicalOrders.perPhysicalOrderCapacity_eq _ _ _ _

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters CWStrands CWWindowedLeaves
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def Work.statisticWeight {K : ℕ} (w : Work K) : w.Statistic → ℕ :=
  match w with
  | .stageA _ => fun a => AllFieldParameters.statisticWeight a.1 +
      AllFieldParameters.statisticWeight a.2
  | .stageB _ => AllFieldParameters.statisticWeight
  | .stageC _ => fun _ => 0

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryPositions
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def bSubdivisionPositionEquiv {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : BPositive K) (phi : Placement) :
    Fin (population allocation dilation (.afterB h.val, phi)) ≃
      (Σ i : Fin 3, Fin (population allocation dilation (.partC (h, i), phi))) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sigma]
    exact (part_population_transition allocation dilation h phi).symm)

theorem final_state_terminal {K : ℕ} (h : State K (K + 2)) : terminal h.val.1 := by
  have hr := h.property
  have hlot := (initialAncestor h.val.1).1.isLt
  cases hh : h.val.1 with
  | initial g =>
      simp only [hh, resident] at hr
      simp only [hh, initialAncestor] at hlot
      intro hp
      have := hr hp
      omega
  | afterA a =>
      simp only [hh, resident] at hr
      simp only [hh, initialAncestor] at hlot
      intro hp
      have := hr.2 hp
      omega
  | afterB b =>
      simp only [hh, resident] at hr
      exact hr.2
  | partC c =>
      simp only [hh, resident] at hr
      simp only [hh, initialAncestor] at hlot
      omega
  | afterC c => trivial

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
attribute [local instance] Classical.propDecidable Classical.decEq

theorem currentShape_spec {K : ℕ} (h : CanonicalHistory K) :
    ShapeBounded (currentShape h) ∧ shapeTotal (currentShape h) = 2 * currentLength h := by
  cases h with
  | initial h => exact root_shape_spec _ (initialShape_mem h)
  | afterA h => exact ⟨mem_shapes_bounded (aShape_size h) (by omega), mem_shapes_total (aShape_size h)⟩
  | afterB h => exact ⟨mem_shapes_bounded (bShape_size h) (by omega), mem_shapes_total (bShape_size h)⟩
  | partC h => exact ⟨mem_shapes_bounded (bShape_size h.1.val) (by omega),
      mem_shapes_total (bShape_size h.1.val)⟩
  | afterC h =>
      cases hh : h.2.2 with
      | false =>
          simpa only [currentShape, currentLength, cShape, cSplit, cShapeParent, halfShape, hh,
            Bool.false_eq_true, ite_false, if_false, Nat.mul_one] using
            stageC_shape_spec _ (bShape_size h.1.1.val) h.1.1.property h.2.1
      | true =>
          simpa only [currentShape, currentLength, cShape, cSplit, cShapeParent, halfShape, hh,
            ite_true, if_true, Nat.mul_one] using
            stageC_complement_spec _ (bShape_size h.1.1.val) h.1.1.property h.2.1

theorem positive_iff_no_zero (u : Shape) : positive u = true ↔ ∀ i, u i ≠ 0 := by
  simp only [positive, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h i
    fin_cases i
    · change u 0 ≠ 0
      omega
    · change u 1 ≠ 0
      omega
    · change u 2 ≠ 0
      omega
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    omega

theorem not_positive_has_zero (u : Shape) (hu : positive u ≠ true) : ∃ i, u i = 0 := by
  by_contra hn
  apply hu
  rw [positive_iff_no_zero]
  intro i hi
  exact hn ⟨i, hi⟩

theorem terminal_has_zero {K : ℕ} (h : CanonicalHistory K) (ht : terminal h) :
    ∃ i, currentShape h i = 0 := by
  cases h with
  | initial h =>
      apply not_positive_has_zero
      intro hp
      exact ht (List.mem_filter.mpr ⟨initialShape_mem h, hp⟩)
  | afterA h =>
      apply not_positive_has_zero
      intro hp
      exact ht (List.mem_filter.mpr ⟨aShape_size h, hp⟩)
  | afterB h => exact not_positive_has_zero _ ht
  | partC h => exact False.elim ht
  | afterC h => exact cShape_zero h

theorem child_length {K : ℕ} (w : Work K) (b : w.Branch) (right : Bool) :
    currentLength (w.child b right) = w.halfLength := by
  cases w <;> rfl

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open MatrixMultiplication.Foundation AllFieldParameters CWStrands InheritedMasks
open scoped BigOperators Classical

instance instFintypeResidentStatistic {K : ℕ} (h : CanonicalHistory K) : Fintype (ResidentStatistic h) := by
  cases h <;> dsimp [ResidentStatistic] <;> infer_instance

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev ProducedPositions {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :=
  Σ h : Produced K tick, Fin (population allocation dilation h.val)

abbrev SplitPositions {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :=
  Σ w : Active K tick, Σ b : w.val.1.Branch,
    Bool × Fin (branchPopulation allocation dilation w.val b)

def splitToProduced {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :
    SplitPositions (K := K) (tick := tick) allocation dilation →
      ProducedPositions (K := K) (tick := tick) allocation dilation := by
  rintro ⟨⟨⟨w, phi⟩, hw⟩, b, right, i⟩
  cases w with
  | stageA h =>
      exact ⟨⟨(.afterA ⟨h, b, right⟩, phi), hw.symm⟩,
        halfPosition allocation dilation (.stageA h, phi) b right i⟩
  | stageB h =>
      let child : AfterB K := ⟨h, b, right⟩
      let j := halfPosition allocation dilation (.stageB h, phi) b right i
      by_cases hp : positive (bShape child) = true
      · let part := bSubdivisionPositionEquiv allocation dilation ⟨child, hp⟩ phi j
        exact ⟨⟨(.partC (⟨child, hp⟩, part.1), phi), hw.symm⟩, part.2⟩
      · exact ⟨⟨(.afterB child, phi), hw.symm, hp⟩, j⟩
  | stageC h =>
      exact ⟨⟨(.afterC (h, b, right), phi), hw.symm⟩,
        halfPosition allocation dilation (.stageC h, phi) b right i⟩

def producedToSplit {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :
    ProducedPositions (K := K) (tick := tick) allocation dilation →
      SplitPositions (K := K) (tick := tick) allocation dilation := by
  rintro ⟨⟨⟨h, phi⟩, hp⟩, i⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h =>
      exact ⟨⟨(.stageA h.1, phi), hp.symm⟩, h.2.1, h.2.2,
        unhalfPosition allocation dilation (.stageA h.1, phi) h.2.1 h.2.2 i⟩
  | afterB h =>
      exact ⟨⟨(.stageB h.1, phi), hp.1.symm⟩, h.2.1, h.2.2,
        unhalfPosition allocation dilation (.stageB h.1, phi) h.2.1 h.2.2 i⟩
  | partC h =>
      let j := (bSubdivisionPositionEquiv allocation dilation h.1 phi).symm ⟨h.2, i⟩
      exact ⟨⟨(.stageB h.1.val.1, phi), hp.symm⟩, h.1.val.2.1, h.1.val.2.2,
        unhalfPosition allocation dilation (.stageB h.1.val.1, phi)
          h.1.val.2.1 h.1.val.2.2 j⟩
  | afterC h =>
      exact ⟨⟨(.stageC h.1, phi), hp.symm⟩, h.2.1, h.2.2,
        unhalfPosition allocation dilation (.stageC h.1, phi) h.2.1 h.2.2 i⟩

theorem producedToSplit_splitToProduced {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (p : SplitPositions (K := K) (tick := tick) allocation dilation) :
    producedToSplit allocation dilation (splitToProduced allocation dilation p) = p := by
  rcases p with ⟨⟨⟨w, phi⟩, hw⟩, b, right, i⟩
  cases w with
  | stageA h => rfl
  | stageB h =>
      by_cases hp : positive (bShape (⟨h, b, right⟩ : AfterB K)) = true
      · dsimp only [splitToProduced]
        rw [dite_eq_left hp]
        dsimp only [producedToSplit]
        let lift : Fin (population allocation dilation (.afterB ⟨h, b, right⟩, phi)) →
            SplitPositions (K := K) (tick := tick) allocation dilation :=
          fun position => ⟨⟨(.stageB h, phi), hw⟩, b, right,
            unhalfPosition allocation dilation (.stageB h, phi) b right position⟩
        exact congrArg lift ((bSubdivisionPositionEquiv allocation dilation
          ⟨⟨h, b, right⟩, hp⟩ phi).symm_apply_apply
            (halfPosition allocation dilation (.stageB h, phi) b right i))
      · dsimp only [splitToProduced]
        rw [dite_eq_right hp]
        rfl
  | stageC h => rfl

theorem splitToProduced_producedToSplit {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (p : ProducedPositions (K := K) (tick := tick) allocation dilation) :
    splitToProduced allocation dilation (producedToSplit allocation dilation p) = p := by
  rcases p with ⟨⟨⟨h, phi⟩, hp⟩, i⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h => rfl
  | afterB h =>
      rcases h with ⟨a, b, right⟩
      dsimp only [producedToSplit, splitToProduced]
      rw [dite_eq_right hp.2]
      rfl
  | partC h =>
      rcases h with ⟨⟨⟨a, b, right⟩, hb⟩, part⟩
      dsimp only [producedToSplit, splitToProduced]
      rw [dite_eq_left hb]
      let lift : (Σ j : Fin 3,
          Fin (population allocation dilation
            (.partC (⟨⟨a, b, right⟩, hb⟩, j), phi))) →
          ProducedPositions (K := K) (tick := tick) allocation dilation :=
        fun q => ⟨⟨(.partC (⟨⟨a, b, right⟩, hb⟩, q.1), phi), hp⟩, q.2⟩
      exact congrArg lift ((bSubdivisionPositionEquiv allocation dilation
        ⟨⟨a, b, right⟩, hb⟩ phi).apply_symm_apply ⟨part, i⟩)
  | afterC h => rfl

def producedPositionEquiv {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :
    ProducedPositions (K := K) (tick := tick) allocation dilation ≃
      SplitPositions (K := K) (tick := tick) allocation dilation where
  toFun := producedToSplit allocation dilation
  invFun := splitToProduced allocation dilation
  left_inv := splitToProduced_producedToSplit allocation dilation
  right_inv := producedToSplit_splitToProduced allocation dilation

theorem producedPositionEquiv_shape {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (p : ProducedPositions (K := K) (tick := tick) allocation dilation) :
    currentPhysicalShape p.1.val =
      physicalShape (producedPositionEquiv allocation dilation p).1.val.2
        (halfShape (producedPositionEquiv allocation dilation p).1.val.1.parentShape
          ((producedPositionEquiv allocation dilation p).1.val.1.splitShape
            (producedPositionEquiv allocation dilation p).2.1)
          (producedPositionEquiv allocation dilation p).2.2.1) := by
  rcases p with ⟨⟨⟨h, phi⟩, hp⟩, i⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h => rfl
  | afterB h => rfl
  | partC h => rfl
  | afterC h => rfl

theorem producedPositionEquiv_length {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (p : ProducedPositions (K := K) (tick := tick) allocation dilation) :
    currentLength p.1.val.1 = (producedPositionEquiv allocation dilation p).1.val.1.halfLength := by
  rcases p with ⟨⟨⟨h, phi⟩, hp⟩, i⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h => rfl
  | afterB h => rfl
  | partC h => rfl
  | afterC h => rfl

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_InitialState
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

namespace AllFieldWitness

variable {F : Type*} [Field F]

def volume (W : AllFieldWitness F) : ℕ := W.rows * W.inner * W.columns

end AllFieldWitness
end MatrixMultiplication

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldFiniteFamily

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

variable {F : Type*} [Field F]

namespace LocalMap

variable {X Y Z X' Y' Z' X'' Y'' Z'' : Type}
  [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype X'] [Fintype Y'] [Fintype Z']
  {source : Tensor F X Y Z} {middle : Tensor F X' Y' Z'}
  {target : Tensor F X'' Y'' Z''}

def repairBranches {I : Type} [Fintype I]
    (T Q : I → Tensor F X Y Z) (L : ℕ)
    (repair : ∀ i, InverseLinearRecovery.RecoveredBy (Q i) (T i) L) :
    LocalMap
      (Tensor.directSum (fun _ : InverseLinearRecovery.MaskRectangles L => Tensor.directSum T))
      (Tensor.directSum Q) := by
  choose a b c h using repair
  exact ofExists (Replication.repair_branches T Q a b c h)

end LocalMap

namespace Execution

variable {SX SY SZ X Y Z X' Y' Z' : Type}
  [Fintype SX] [Fintype SY] [Fintype SZ]
  [Fintype X] [Fintype Y] [Fintype Z]
  {source : Tensor F SX SY SZ} {current : Tensor F X Y Z}

def extractSelectedAndRepair (E : Execution source current)
    {I J : Type} [Fintype I] [Fintype J]
    (assignment : JointExtraction.Assignment X Y Z I)
    (coherent : JointExtraction.Coherent current assignment)
    (select : J → I) (injective : Function.Injective select)
    (ideal : J → Tensor F X Y Z) (L : ℕ)
    (repair : ∀ j, InverseLinearRecovery.RecoveredBy (ideal j)
      (JointExtraction.branch current assignment (select j)) L) :
    Execution source (Tensor.directSum ideal) := by
  let extracted := E.restrict _ (LocalMap.extract current assignment coherent)
  let selected := extracted.restrict _
    (LocalMap.selectBranches (JointExtraction.branch current assignment) select injective)
  exact selected.step (InverseLinearRecovery.MaskRectangles L)
    (by simp [InverseLinearRecovery.MaskRectangles]) _
    ((LocalMap.repairBranches (fun j => JointExtraction.branch current assignment (select j))
      ideal L repair).withSource _
      (by
        funext first second third
        simp only [Tensor.directSum]
        split_ifs <;> rfl))

end Execution

end MatrixMultiplication.AllFieldFiniteFamily

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_MatrixMapDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldFiniteFamily

open MatrixMultiplication.Foundation

variable {F : Type*} [Field F]

theorem matrixCoefficients_decidable (A B C : Type)
    (dA eA : DecidableEq A) (dB eB : DecidableEq B) (dC eC : DecidableEq C) :
    @Tensor.matrixCoefficients F _ A B C dA dB dC =
      @Tensor.matrixCoefficients F _ A B C eA eB eC := by
  have hA : dA = eA := Subsingleton.elim _ _
  have hB : dB = eB := Subsingleton.elim _ _
  have hC : dC = eC := Subsingleton.elim _ _
  cases hA
  cases hB
  cases hC
  rfl

namespace LocalMap

def redecideMatrix {X Y Z A B C : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    {source : Tensor F X Y Z}
    {dA : DecidableEq A} {dB : DecidableEq B} {dC : DecidableEq C}
    (map : LocalMap source (@Tensor.matrixCoefficients F _ A B C dA dB dC))
    (eA : DecidableEq A) (eB : DecidableEq B) (eC : DecidableEq C) :
    LocalMap source (@Tensor.matrixCoefficients F _ A B C eA eB eC) where
  x := map.x
  y := map.y
  z := map.z
  coefficient := map.coefficient.trans
    (matrixCoefficients_decidable A B C dA eA dB eB dC eC)

end LocalMap
end MatrixMultiplication.AllFieldFiniteFamily

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistorySums
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def secondMass (t : Shape) : ℚ :=
  2 * (positiveInitial.map (fun g => initialLaw g * stageALaw g t)).sum

def littleMass (t u : Shape) : ℚ := 2 * secondMass t * stageBLaw t u

 theorem secondMass_cast (t : Shape) :
    (secondMass t : ℝ) =
      2 * (positiveInitial.map (fun g => (initialLaw g : ℝ) * (stageALaw g t : ℝ))).sum := by
  simp only [secondMass, Rat.cast_mul, Rat.cast_ofNat, list_rat_cast_inline_MatrixMultiplication_AllFieldHistorySums]

 theorem littleMass_cast (t u : Shape) :
    (littleMass t u : ℝ) = 2 * (secondMass t : ℝ) * (stageBLaw t u : ℝ) := by
  simp only [littleMass, Rat.cast_mul, Rat.cast_ofNat]

theorem initial_positive_sum (K : ℕ) (f : Shape → ℝ) :
    (∑ h : InitialPositive K, f (initialShape h.val)) =
      (K : ℝ) * (positiveInitial.map f).sum := by
  rw [subtype_sum_indicator_inline_MatrixMultiplication_AllFieldHistorySums (fun h : Initial K => initialShape h ∈ positiveInitial)
    (fun h => f (initialShape h))]
  change (∑ history : Initial K,
    if sortedInitial[history.2.val] ∈ positiveInitial then f sortedInitial[history.2.val] else 0) = _
  simp only [Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_fun_getElem sortedInitial
    (fun g => if g ∈ positiveInitial then f g else 0)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply congrArg (fun r : ℝ => (K : ℝ) * r)
  change _ = ((sortedInitial.filter positive).map f).sum
  rw [list_filter_sum_inline_MatrixMultiplication_AllFieldHistorySums]
  apply list_sum_congr
  intro g hg
  simp only [positiveInitial, List.mem_filter, hg, true_and]

theorem stageA_parent_sum : ∀ g ∈ positiveInitial, g 0 + g 1 + g 2 = 16 := by
  decide +kernel

theorem stageA_extend_sum (g : Shape) (hg : g ∈ positiveInitial)
    (f : Shape → ℝ) :
    ((below g).map (fun t => (stageALaw g t : ℝ) * f t)).sum =
      ((shapes 8).map (fun t => (stageALaw g t : ℝ) * f t)).sum := by
  have he : below g = (shapes 8).filter
      (fun t => t 0 ≤ g 0 && t 1 ≤ g 1 && t 2 ≤ g 2) := by
    simp only [below, stageA_parent_sum g hg]
  rw [he, list_filter_sum_inline_MatrixMultiplication_AllFieldHistorySums]
  apply list_sum_congr
  intro t ht
  by_cases hb : (t 0 ≤ g 0 && t 1 ≤ g 1 && t 2 ≤ g 2) = true
  · simp only [hb, ite_true, if_true]
  · have hnot : t ∉ below g := by rw [he]; simp [hb]
    have hz : stageALaw g t = 0 := splitLaw_outside_support _ _ g t hnot
    simp [hb, hz]

 theorem a_parent_history_sum {K : ℕ} (h : InitialPositive K) (f : Shape → ℝ) :
    (∑ p : ASplit h × Bool, (aAmount ⟨h, p⟩ : ℝ) * f (aShape ⟨h, p⟩)) =
      2 * (initialAmount h.val : ℝ) *
        ((below (initialShape h.val)).map
          (fun t => (stageALaw (initialShape h.val) t : ℝ) * f t)).sum := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, aAmount, aShape, aSplit,
    halfShape, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, Rat.cast_mul,
    List.get_eq_getElem]
  simp only [mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Fin.sum_univ_fun_getElem (below (initialShape h.val))
    (fun t => (stageALaw (initialShape h.val) t : ℝ) *
      f (complement (initialShape h.val) t)),
    Fin.sum_univ_fun_getElem (below (initialShape h.val))
      (fun t => (stageALaw (initialShape h.val) t : ℝ) * f t),
    stageA_complement_sum _ h.property]
  ring

 theorem a_history_sum_parents (K : ℕ) (f : Shape → ℝ) :
    (∑ h : AfterA K, (aAmount h : ℝ) * f (aShape h)) =
      (K : ℝ) * (positiveInitial.map (fun g => 2 * (initialLaw g : ℝ) *
        ((below g).map (fun t => (stageALaw g t : ℝ) * f t)).sum)).sum := by
  rw [Fintype.sum_sigma]
  simp only [a_parent_history_sum, initialAmount]
  exact initial_positive_sum K (fun g => 2 * (initialLaw g : ℝ) *
    ((below g).map (fun t => (stageALaw g t : ℝ) * f t)).sum)

 theorem a_history_sum (K : ℕ) (f : Shape → ℝ) :
    (∑ h : AfterA K, (aAmount h : ℝ) * f (aShape h)) =
      (K : ℝ) * ((shapes 8).map (fun t => (secondMass t : ℝ) * f t)).sum := by
  rw [a_history_sum_parents]
  apply congrArg (fun r : ℝ => (K : ℝ) * r)
  calc
    _ = (positiveInitial.map (fun g => ((shapes 8).map
        (fun t => 2 * (initialLaw g : ℝ) * ((stageALaw g t : ℝ) * f t))).sum)).sum := by
      apply list_sum_congr
      intro g hg
      rw [stageA_extend_sum g hg, List.sum_map_mul_left]
    _ = ((shapes 8).map (fun t => (positiveInitial.map
        (fun g => 2 * (initialLaw g : ℝ) * ((stageALaw g t : ℝ) * f t))).sum)).sum :=
      list_sum_comm _ _ _
    _ = _ := by
      apply list_sum_congr
      intro t _
      rw [secondMass_cast]
      calc
        _ = (positiveInitial.map
            (fun g => 2 * ((initialLaw g : ℝ) * (stageALaw g t : ℝ)) * f t)).sum := by
          apply list_sum_congr
          intro g _
          ring
        _ = _ := by rw [List.sum_map_mul_right, List.sum_map_mul_left]

 theorem a_positive_history_sum (K : ℕ) (f : Shape → ℝ) :
    (∑ h : APositive K, (aAmount h.val : ℝ) * f (aShape h.val)) =
      (K : ℝ) * (positiveSecond.map (fun t => (secondMass t : ℝ) * f t)).sum := by
  rw [subtype_sum_indicator_inline_MatrixMultiplication_AllFieldHistorySums (fun h : AfterA K => aShape h ∈ positiveSecond)
    (fun h => (aAmount h : ℝ) * f (aShape h))]
  trans ∑ h : AfterA K, (aAmount h : ℝ) *
    (if aShape h ∈ positiveSecond then f (aShape h) else 0)
  · apply Finset.sum_congr rfl
    intro h _
    split_ifs <;> simp_all
  rw [a_history_sum K (fun t => if t ∈ positiveSecond then f t else 0)]
  apply congrArg (fun r : ℝ => (K : ℝ) * r)
  change _ = (((shapes 8).filter positive).map
    (fun t => (secondMass t : ℝ) * f t)).sum
  rw [list_filter_sum_inline_MatrixMultiplication_AllFieldHistorySums]
  apply list_sum_congr
  intro t ht
  simp only [positiveSecond, List.mem_filter, ht, true_and]
  split_ifs <;> simp_all

 theorem b_parent_history_sum {K : ℕ} (h : APositive K) (f : Shape → ℝ) :
    (∑ p : BSplit h × Bool, (bAmount ⟨h, p⟩ : ℝ) * f (bShape ⟨h, p⟩)) =
      2 * (aAmount h.val : ℝ) *
        ((below (aShape h.val)).map
          (fun u => (stageBLaw (aShape h.val) u : ℝ) * f u)).sum := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, bAmount, bShape, bSplit,
    halfShape, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, Rat.cast_mul,
    List.get_eq_getElem]
  simp only [mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Fin.sum_univ_fun_getElem (below (aShape h.val))
    (fun u => (stageBLaw (aShape h.val) u : ℝ) *
      f (complement (aShape h.val) u)),
    Fin.sum_univ_fun_getElem (below (aShape h.val))
      (fun u => (stageBLaw (aShape h.val) u : ℝ) * f u),
    stageB_complement_sum _ h.property]
  ring

 theorem b_history_sum (K : ℕ) (f : Shape → Shape → ℝ) :
    (∑ h : AfterB K, (bAmount h : ℝ) * f (aShape h.1.val) (bShape h)) =
      (K : ℝ) * (positiveSecond.map (fun t =>
        ((below t).map (fun u => (littleMass t u : ℝ) * f t u)).sum)).sum := by
  rw [Fintype.sum_sigma]
  simp only [b_parent_history_sum]
  have he : (∑ h : APositive K, 2 * (aAmount h.val : ℝ) *
      ((below (aShape h.val)).map
        (fun u => (stageBLaw (aShape h.val) u : ℝ) * f (aShape h.val) u)).sum) =
      ∑ h : APositive K, (aAmount h.val : ℝ) *
        (2 * ((below (aShape h.val)).map
          (fun u => (stageBLaw (aShape h.val) u : ℝ) * f (aShape h.val) u)).sum) := by
    apply Finset.sum_congr rfl
    intro h _
    ring
  rw [he, a_positive_history_sum K (fun t =>
    2 * ((below t).map (fun u => (stageBLaw t u : ℝ) * f t u)).sum)]
  apply congrArg (fun r : ℝ => (K : ℝ) * r)
  apply list_sum_congr
  intro t _
  calc
    _ = 2 * (secondMass t : ℝ) *
        ((below t).map (fun u => (stageBLaw t u : ℝ) * f t u)).sum := by ring
    _ = _ := by
      rw [← List.sum_map_mul_left]
      apply list_sum_congr
      intro u _
      rw [littleMass_cast]
      ring

 theorem b_positive_history_sum (K : ℕ) (f : Shape → Shape → ℝ) :
    (∑ h : BPositive K, (bAmount h.val : ℝ) *
      f (aShape h.val.1.val) (bShape h.val)) =
      (K : ℝ) * (positiveSecond.map (fun t =>
        (((below t).filter positive).map
          (fun u => (littleMass t u : ℝ) * f t u)).sum)).sum := by
  rw [subtype_sum_indicator_inline_MatrixMultiplication_AllFieldHistorySums (fun h : AfterB K => positive (bShape h) = true)
    (fun h => (bAmount h : ℝ) * f (aShape h.1.val) (bShape h))]
  trans ∑ h : AfterB K, (bAmount h : ℝ) *
    (if positive (bShape h) then f (aShape h.1.val) (bShape h) else 0)
  · apply Finset.sum_congr rfl
    intro h _
    split_ifs <;> simp_all
  rw [b_history_sum K (fun t u => if positive u then f t u else 0)]
  apply congrArg (fun r : ℝ => (K : ℝ) * r)
  apply list_sum_congr
  intro t _
  rw [list_filter_sum_inline_MatrixMultiplication_AllFieldHistorySums]
  apply list_sum_congr
  intro u _
  split_ifs <;> simp_all

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_ActiveSums
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def workStagesEquiv (K : ℕ) :
    Work K ≃ InitialPositive K ⊕ APositive K ⊕ PartC K where
  toFun
    | .stageA h => .inl h
    | .stageB h => .inr (.inl h)
    | .stageC h => .inr (.inr h)
  invFun
    | .inl h => .stageA h
    | .inr (.inl h) => .stageB h
    | .inr (.inr h) => .stageC h
  left_inv w := by cases w <;> rfl
  right_inv h := by rcases h with h | h | h <;> rfl

theorem work_sum {K : ℕ} (f : Work K → ℝ) :
    (∑ w, f w) = (∑ h : InitialPositive K, f (.stageA h)) +
      (∑ h : APositive K, f (.stageB h)) + (∑ h : PartC K, f (.stageC h)) := by
  calc
    _ = ∑ h : InitialPositive K ⊕ APositive K ⊕ PartC K,
        f ((workStagesEquiv K).symm h) :=
      ((workStagesEquiv K).symm.sum_comp f).symm
    _ = _ := by
      simp only [Fintype.sum_sum_type]
      exact (add_assoc _ _ _).symm

theorem sum_lot_tick (K tick : ℕ) (stage : Fin 3) (value : ℝ) :
    (∑ lot : Fin K, if FiniteSchedule.lotTick lot stage = tick then value else 0) =
      if FiniteSchedule.stageActive K tick stage then value else 0 := by
  by_cases active : FiniteSchedule.stageActive K tick stage
  · obtain ⟨lot, hlot, unique⟩ :=
      (FiniteSchedule.stageActive_iff_unique_lot K tick stage).mp active
    have he (j : Fin K) : FiniteSchedule.lotTick j stage = tick ↔ j = lot :=
      ⟨unique j, fun h => by simpa only [h] using hlot⟩
    simp only [he, ite_eq_left active]
    simp
  · have hn (lot : Fin K) : FiniteSchedule.lotTick lot stage ≠ tick := by
      intro h
      exact active (h ▸ FiniteSchedule.lot_active_at_its_tick lot stage)
    simp only [hn, ite_eq_right active, ite_false, if_false, Finset.sum_const_zero]

def stageASourceSum (fA : Shape → ℝ) : ℝ :=
  (positiveInitial.map (fun g => (initialLaw g : ℝ) * fA g)).sum

def stageBSourceSum (fB : Shape → ℝ) : ℝ :=
  (positiveSecond.map (fun t => (secondMass t : ℝ) * fB t)).sum

def stageCSourceSum (allocation : Allocation) (fC : Shape → Shape → Fin 3 → ℝ) : ℝ :=
  (positiveSecond.map (fun t => (((below t).filter positive).map (fun u =>
    (littleMass t u : ℝ) * ∑ part : Fin 3, (allocation.mass part : ℝ) * fC t u part)).sum)).sum

theorem stageA_one_lot_sum (fA : Shape → ℝ) :
    (∑ h : InitialPositive 1, (initialAmount h.val : ℝ) * fA (initialShape h.val)) =
      stageASourceSum fA := by
  simpa only [Nat.cast_one, one_mul, initialAmount, stageASourceSum] using
    initial_positive_sum 1 (fun g => (initialLaw g : ℝ) * fA g)

theorem stageB_one_lot_sum (fB : Shape → ℝ) :
    (∑ h : APositive 1, (aAmount h.val : ℝ) * fB (aShape h.val)) =
      stageBSourceSum fB := by
  simpa only [Nat.cast_one, one_mul, stageBSourceSum] using a_positive_history_sum 1 fB

theorem stageC_one_lot_sum (allocation : Allocation) (fC : Shape → Shape → Fin 3 → ℝ) :
    (∑ h : PartC 1, (partAmount allocation h : ℝ) *
      fC (cParameterParent h) (cShapeParent h) h.2) = stageCSourceSum allocation fC := by
  simp only [Fintype.sum_prod_type, partAmount, Rat.cast_mul,
    cParameterParent, cShapeParent, mul_assoc, ← Finset.mul_sum]
  simpa only [Nat.cast_one, one_mul, stageCSourceSum] using
    b_positive_history_sum 1 (fun t u => ∑ part : Fin 3,
      (allocation.mass part : ℝ) * fC t u part)

theorem subtype_sum_indicator_inline_MatrixMultiplication_AllFieldActiveSums {A : Type*} [Fintype A]
    (P : A → Prop) [DecidablePred P] [Fintype {a // P a}] (f : A → ℝ) :
    (∑ a : {a // P a}, f a.val) = ∑ a, if P a then f a else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

theorem active_shape_sum (K tick : ℕ) (allocation : Allocation)
    (fA fB : Shape → ℝ) (fC : Shape → Shape → Fin 3 → ℝ) :
    (∑ w : CanonicalActive K tick,
      workAmount allocation w.val * shapeValue fA fB fC w.val) =
      (if FiniteSchedule.stageActive K tick 0 then stageASourceSum fA else 0) +
      (if FiniteSchedule.stageActive K tick 1 then stageBSourceSum fB else 0) +
      (if FiniteSchedule.stageActive K tick 2 then stageCSourceSum allocation fC else 0) := by
  rw [subtype_sum_indicator_inline_MatrixMultiplication_AllFieldActiveSums
    (fun w : Work K => FiniteSchedule.lotTick w.lot w.stage = tick)
    (fun w => workAmount allocation w * shapeValue fA fB fC w)]
  rw [← (workLotEquiv K).symm.sum_comp
    (fun w => if FiniteSchedule.lotTick w.lot w.stage = tick then
      workAmount allocation w * shapeValue fA fB fC w else 0)]
  simp only [Fintype.sum_prod_type, workLotEquiv_symm_apply, workRelot_lot,
    workRelot_stage, workAmount_relot, shapeValue_relot]
  rw [Finset.sum_comm]
  simp only [sum_lot_tick]
  rw [work_sum]
  change (∑ history : InitialPositive 1, if FiniteSchedule.stageActive K tick 0 then
    (initialAmount history.val : ℝ) * fA (initialShape history.val) else 0) +
    (∑ history : APositive 1, if FiniteSchedule.stageActive K tick 1 then
      (aAmount history.val : ℝ) * fB (aShape history.val) else 0) +
    (∑ history : PartC 1, if FiniteSchedule.stageActive K tick 2 then
      (partAmount allocation history : ℝ) *
        fC (cParameterParent history) (cShapeParent history) history.2 else 0) = _
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    stageA_one_lot_sum, stageB_one_lot_sum, stageC_one_lot_sum]

def stageASourceCapacity (fA : Shape → Staggering.Capacity) : Staggering.Capacity :=
  fun i => stageASourceSum (fun g => fA g i)

def stageBSourceCapacity (fB : Shape → Staggering.Capacity) : Staggering.Capacity :=
  fun i => stageBSourceSum (fun t => fB t i)

def stageCSourceCapacity (allocation : Allocation)
    (fC : Shape → Shape → Fin 3 → Staggering.Capacity) : Staggering.Capacity :=
  fun i => stageCSourceSum allocation (fun t u part => fC t u part i)

theorem activeAggregateCapacity_shapeCapacity (K tick : ℕ) (allocation : Allocation)
    (fA fB : Shape → Staggering.Capacity)
    (fC : Shape → Shape → Fin 3 → Staggering.Capacity) :
    activeAggregateCapacity allocation tick (shapeCapacity (K := K) fA fB fC) =
      FiniteSchedule.tickCapacity K (stageASourceCapacity fA) (stageBSourceCapacity fB)
        (stageCSourceCapacity allocation fC) tick := by
  funext i
  exact active_shape_sum K tick allocation (fun g => fA g i) (fun t => fB t i)
    (fun t u part => fC t u part i)

end MatrixMultiplication.AllFieldHistory

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWWordDimensionParameters
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.CWWordDimensions

open scoped BigOperators Polynomial
open CWStrands

attribute [local instance] Classical.propDecidable

theorem site_enumerator :
    (∑ a : Fin 7, (Polynomial.X : Polynomial ℕ) ^ CWLeafStatistics.weight a) =
      sitePolynomial := by
  norm_num [Fin.sum_univ_succ, CWLeafStatistics.weight, sitePolynomial]
  ring

theorem word_enumerator (P : Type*) [Fintype P] :
    (∑ w : P → Fin 7, (Polynomial.X : Polynomial ℕ) ^ weight w) =
      sitePolynomial ^ Fintype.card P := by
  classical
  calc
    (∑ w : P → Fin 7, (Polynomial.X : Polynomial ℕ) ^ weight w) =
        ∑ w : P → Fin 7, ∏ i, (Polynomial.X : Polynomial ℕ) ^
          CWLeafStatistics.weight (w i) := by
      apply Finset.sum_congr rfl
      intro w _
      exact (Finset.prod_pow_eq_pow_sum Finset.univ
        (fun i => CWLeafStatistics.weight (w i)) Polynomial.X).symm
    _ = ∏ _i : P, ∑ a : Fin 7, (Polynomial.X : Polynomial ℕ) ^
        CWLeafStatistics.weight a :=
      (Fintype.prod_sum (fun (_i : P) (a : Fin 7) =>
        (Polynomial.X : Polynomial ℕ) ^ CWLeafStatistics.weight a)).symm
    _ = sitePolynomial ^ Fintype.card P := by simp only [site_enumerator, Finset.prod_const,
      Finset.card_univ]

abbrev WeightWords (P : Type*) [Fintype P] (j : ℕ) := {w : P → Fin 7 // weight w = j}

theorem card_weightWords (P : Type*) [Fintype P] (j : ℕ) :
    Fintype.card (WeightWords P j) = (sitePolynomial ^ Fintype.card P).coeff j := by
  classical
  rw [← word_enumerator]
  simp [WeightWords, Fintype.card_subtype,
    Polynomial.coeff_X_pow, eq_comm]

theorem card_weightWords_fin (n j : ℕ) :
    Fintype.card (WeightWords (Fin n) j) = recursiveCoeff n j := by
  have h := card_weightWords (Fin n) j
  simp only [Fintype.card_fin, coeff_eq_recursive] at h
  rw [Fintype.card_eq_nat_card] at h ⊢
  exact h

end MatrixMultiplication.CWWordDimensions

end

namespace MatrixMultiplication.CWWordDimensionParameters

open CWWordDimensions AllFieldParameters.Contractions

theorem table_eq_card (j : Fin 17) :
    (coefficients[j.val]?.getD 0) =
      Fintype.card (WeightWords (Fin 8) j.val) := by
  have h := card_weightWords_fin 8 j.val
  rw [Fintype.card_eq_nat_card] at h ⊢
  exact (table_eq_recursive j).trans h.symm

theorem word_card_positive (j : Fin 17) :
    0 < Fintype.card (WeightWords (Fin 8) j.val) := by
  have h := table_eq_card j
  rw [Fintype.card_eq_nat_card] at h ⊢
  rw [← h]
  exact table_positive j

end MatrixMultiplication.CWWordDimensionParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_InitialLeafRates
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instDecidableEqResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instFintypeResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldInitialLeafRates

open AllFieldHistory AllFieldParameters
open CWWindowedLeaves Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev InitialZero (K : ℕ) :=
  {h : Initial K // initialShape h ∉ positiveInitial}

abbrev PopulationHistory (K : ℕ) := InitialZero K × Placement

theorem shapeMax_lt {K : ℕ} (h : InitialZero K) :
    shapeMax (initialShape h.val) < 17 := by
  have hb := (root_shape_spec _ (initialShape_mem h.val)).1
  exact Nat.lt_succ_of_le (max_le (hb 0) (max_le (hb 1) (hb 2)))

def shapeIndex {K : ℕ} (h : InitialZero K) : Fin 17 :=
  ⟨shapeMax (initialShape h.val), shapeMax_lt h⟩

theorem card_alphabet_pos {K : ℕ} (h : InitialZero K) :
    0 < Fintype.card (Alphabet 8 (shapeMax (initialShape h.val))) := by
  have hc := CWWordDimensionParameters.word_card_positive (shapeIndex h)
  rw [Fintype.card_eq_nat_card] at hc ⊢
  exact hc

abbrev Words {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : PopulationHistory K) :=
  Fin (population allocation dilation (.initial h.1.val, h.2)) →
    Alphabet 8 (shapeMax (initialShape h.1.val))

theorem card_words_pos {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : PopulationHistory K) :
    0 < Fintype.card (Words allocation dilation h) := by
  simp only [Words, Fintype.card_fun, Fintype.card_fin]
  exact pow_pos (card_alphabet_pos h.1) _

abbrev ProductWords {K : ℕ} (allocation : Allocation) (dilation : ℕ) :=
  ∀ h : PopulationHistory K, Words allocation dilation h

def volume {K : ℕ} (allocation : Allocation) (dilation : ℕ) : ℕ :=
  Fintype.card (ProductWords (K := K) allocation dilation)

theorem volume_eq_prod {K : ℕ} (allocation : Allocation) (dilation : ℕ) :
    volume (K := K) allocation dilation =
      ∏ h : PopulationHistory K, Fintype.card (Words allocation dilation h) := by
  rw [volume, Fintype.card_pi]

theorem volume_pos {K : ℕ} (allocation : Allocation) (dilation : ℕ) :
    0 < volume (K := K) allocation dilation := by
  rw [volume_eq_prod]
  exact Finset.prod_pos (fun h _ => card_words_pos allocation dilation h)

end MatrixMultiplication.AllFieldInitialLeafRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_TerminalStatisticLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instDecidableEqResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instFintypeResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.half_unhalfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.unhalf_halfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldTerminalStatisticLaws

open AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ}

theorem aShape_mem_shapes (h : AZero K) : aShape h.1.val ∈ shapes 8 :=
  aShape_size h.1.val

theorem aShape_not_positive (h : AZero K) : positive (aShape h.1.val) ≠ true := by
  intro hp
  exact h.1.property (List.mem_filter.mpr ⟨aShape_mem_shapes h, hp⟩)

theorem aShape_mem_zeroSecond (h : AZero K) : aShape h.1.val ∈ zeroSecond := by
  simp [zeroSecond, aShape_mem_shapes h, aShape_not_positive h]

theorem bShape_max_lt_five (h : BZero K) : shapeMax (bShape h.1.val) < 5 := by
  have hb := child_statistic_weight_bounded (bParent h)
    (bParent_mem_positiveSecond h) (bShape h.1.val) (bShape_mem_below h)
  exact max_lt_iff.mpr ⟨hb 0, max_lt_iff.mpr ⟨hb 1, hb 2⟩⟩

def bWeight (h : BZero K) : Fin 5 :=
  ⟨shapeMax (bShape h.1.val), bShape_max_lt_five h⟩

@[simp] theorem bWeight_val (h : BZero K) : (bWeight h).val = shapeMax (bShape h.1.val) :=
  rfl

def Slot : TerminalZero K → Type
  | .inl _ => PairSlot
  | .inr _ => Fin 6

instance instFintypeSlot (h : TerminalZero K) : Fintype (Slot h) := by
  cases h <;> dsimp [Slot] <;> infer_instance

def history : TerminalZero K → History K
  | .inl h => (.afterA h.1.val, h.2)
  | .inr h => (.afterB h.1.val, h.2)

@[simp] theorem history_inl (h : AZero K) :
    history (.inl h) = (.afterA h.1.val, h.2) := rfl

@[simp] theorem history_inr (h : BZero K) :
    history (.inr h) = (.afterB h.1.val, h.2) := rfl

def law : (h : TerminalZero K) → Slot h → ℚ
  | .inl h, s => zeroPairLaw (aShape h.1.val) s.1 s.2
  | .inr h, s => statisticLaw (binaryParameter (bParent h) (bShape h.1.val)) (bWeight h) s

@[simp] theorem law_inl (h : AZero K) (s : PairSlot) :
    law (.inl h) s = zeroPairLaw (aShape h.1.val) s.1 s.2 := rfl

@[simp] theorem law_inr (h : BZero K) (s : Fin 6) :
    law (.inr h) s =
      statisticLaw (binaryParameter (bParent h) (bShape h.1.val)) (bWeight h) s := rfl

theorem statisticLaw_nonnegative (t u : Shape) (k : Fin 5) (s : Fin 6) :
    0 ≤ statisticLaw (binaryParameter t u) k s := by
  obtain ⟨hl, hh⟩ := binaryParameter_bounds t u
  unfold statisticLaw
  split_ifs <;> linarith

theorem statisticLaw_total (d : ℚ) (k : Fin 5) :
    ∑ s : Fin 6, statisticLaw d k s = 1 := by
  fin_cases k <;> simp [statisticLaw, Fin.sum_univ_succ, singletonSlot]

theorem law_nonneg (h : TerminalZero K) (s : Slot h) : 0 ≤ law h s := by
  cases h with
  | inl h => exact zeroPairLaw_nonnegative (aShape h.1.val) s.1 s.2
  | inr h => exact statisticLaw_nonnegative (bParent h) (bShape h.1.val) (bWeight h) s

theorem law_total (h : TerminalZero K) : ∑ s : Slot h, law h s = 1 := by
  cases h with
  | inl h => exact zeroPairLaw_full_normalized (aShape h.1.val) (aShape_mem_zeroSecond h)
  | inr h => exact statisticLaw_total _ (bWeight h)

theorem history_amount_pos (allocation : Allocation) (h : TerminalZero K) :
    0 < amount allocation (history h) := by
  cases h with
  | inl h =>
      change 0 < aAmount h.1.val / 6
      exact div_pos (aAmount_pos h.1.val) (by norm_num)
  | inr h =>
      change 0 < bAmount h.1.val / 6
      exact div_pos (bAmount_pos h.1.val) (by norm_num)

end MatrixMultiplication.AllFieldTerminalStatisticLaws

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_FinalState
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldFinalState

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldTerminalStatisticLaws
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev InitialIndex (K : ℕ) := AllFieldInitialLeafRates.PopulationHistory K
abbrev CIndex (K : ℕ) := AfterC K × Placement
abbrev Index (K : ℕ) := InitialIndex K ⊕ (TerminalZero K ⊕ CIndex K)

def history {K : ℕ} : Index K → History K
  | .inl h => (.initial h.1.val, h.2)
  | .inr (.inl h) => AllFieldTerminalStatisticLaws.history h
  | .inr (.inr h) => (.afterC h.1, h.2)

theorem history_terminal {K : ℕ} (h : Index K) : terminal (history h).1 := by
  rcases h with h | h | h
  · exact h.1.property
  · rcases h with h | h
    · exact h.1.property
    · exact h.1.property
  · trivial

theorem terminal_resident_final {K : ℕ} (h : CanonicalHistory K) (ht : terminal h) :
    resident (K + 2) h := by
  have hlot := (initialAncestor h).1.isLt
  cases h with
  | initial h => exact fun hp => False.elim (ht hp)
  | afterA h =>
      refine ⟨?_, fun hp => False.elim (ht hp)⟩
      change h.1.val.1.val < K at hlot
      omega
  | afterB h =>
      refine ⟨?_, ht⟩
      change h.1.val.1.val.1.val < K at hlot
      omega
  | partC h => exact False.elim ht
  | afterC h =>
      change h.1.1.val.1.val.1.val.1.val < K at hlot
      change h.1.1.val.1.val.1.val.1.val + 3 ≤ K + 2
      omega

def toState {K : ℕ} (h : Index K) : State K (K + 2) :=
  ⟨history h, terminal_resident_final _ (history_terminal h)⟩

def fromState {K : ℕ} (h : State K (K + 2)) : Index K := by
  have ht := final_state_terminal h
  rcases h with ⟨⟨h, phi⟩, hr⟩
  cases h with
  | initial h => exact .inl (⟨h, ht⟩, phi)
  | afterA h => exact .inr (.inl (.inl (⟨h, ht⟩, phi)))
  | afterB h => exact .inr (.inl (.inr (⟨h, ht⟩, phi)))
  | partC h => exact False.elim ht
  | afterC h => exact .inr (.inr (h, phi))

def indexEquiv (K : ℕ) : Index K ≃ State K (K + 2) where
  toFun := toState
  invFun := fromState
  left_inv h := by
    rcases h with h | h | h
    · rfl
    · cases h <;> rfl
    · rfl
  right_inv h := by
    have ht := final_state_terminal h
    rcases h with ⟨⟨h, phi⟩, hr⟩
    cases h with
    | initial h => rfl
    | afterA h => rfl
    | afterB h => rfl
    | partC h => exact False.elim ht
    | afterC h => rfl

variable {K : ℕ} (allocation : Allocation) (dilation : ℕ)

abbrev Words := ∀ h : Index K, HistoryWord allocation dilation (history h)
abbrev InitialWords := ∀ h : InitialIndex K,
  HistoryWord allocation dilation (.initial h.1.val, h.2)
abbrev ZeroWords := ∀ h : TerminalZero K,
  HistoryWord allocation dilation (AllFieldTerminalStatisticLaws.history h)
abbrev CWords := ∀ h : CIndex K, HistoryWord allocation dilation (.afterC h.1, h.2)
abbrev Parts := InitialWords (K := K) allocation dilation ×
  (ZeroWords (K := K) allocation dilation × CWords (K := K) allocation dilation)

instance wordsFintype : Fintype (Words (K := K) allocation dilation) :=
  Fintype.ofFinite _

def grouped (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (Words (K := K) allocation dilation) (Words (K := K) allocation dilation)
      (Words (K := K) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : Index K =>
    historyTensor F allocation dilation ε (history h))

def stateWord (w : Words (K := K) allocation dilation) :
    ∀ h : State K (K + 2), HistoryWord allocation dilation h.val :=
  Equiv.piCongrLeft (fun h : State K (K + 2) => HistoryWord allocation dilation h.val)
    (indexEquiv K) w

theorem grouped_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : Words (K := K) allocation dilation) :
    stateTensor F allocation dilation ε (K + 2) (stateWord allocation dilation x)
      (stateWord allocation dilation y) (stateWord allocation dilation z) =
    grouped allocation dilation F ε x y z := by
  change (∏ h : State K (K + 2), historyTensor F allocation dilation ε h.val
    (stateWord allocation dilation x h) (stateWord allocation dilation y h)
      (stateWord allocation dilation z h)) = _
  rw [← (indexEquiv K).prod_comp]
  unfold grouped CommonDimensions.familyProduct
  apply Finset.prod_congr rfl
  intro h _
  have hstate (w : Words (K := K) allocation dilation) :
      stateWord allocation dilation w ((indexEquiv K) h) = w h :=
    Equiv.piCongrLeft_apply_apply
      (fun state : State K (K + 2) => HistoryWord allocation dilation state.val)
      (indexEquiv K) w h
  rw [hstate, hstate, hstate]
  rfl

def groupedMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (stateTensor F (K := K) allocation dilation ε (K + 2))
      (grouped (K := K) allocation dilation F ε) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (stateWord (K := K) allocation dilation) (stateWord (K := K) allocation dilation)
    (stateWord (K := K) allocation dilation) _).symm.trans ?_⟩
  funext x y z
  exact grouped_coefficient allocation dilation F ε x y z

def initialTensor (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (InitialWords (K := K) allocation dilation) (InitialWords (K := K) allocation dilation)
      (InitialWords (K := K) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : InitialIndex K =>
    historyTensor F allocation dilation ε (.initial h.1.val, h.2))

def zeroTensor (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (ZeroWords (K := K) allocation dilation) (ZeroWords (K := K) allocation dilation)
      (ZeroWords (K := K) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : TerminalZero K =>
    historyTensor F allocation dilation ε (AllFieldTerminalStatisticLaws.history h))

def cTensor (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (CWords (K := K) allocation dilation) (CWords (K := K) allocation dilation)
      (CWords (K := K) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : CIndex K =>
    historyTensor F allocation dilation ε (.afterC h.1, h.2))

def partsTensor (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (Parts (K := K) allocation dilation) (Parts (K := K) allocation dilation)
      (Parts (K := K) allocation dilation) :=
  Tensor.product (initialTensor (K := K) allocation dilation F ε)
    (Tensor.product (zeroTensor (K := K) allocation dilation F ε)
      (cTensor (K := K) allocation dilation F ε))

def joinParts (w : Parts (K := K) allocation dilation) : Words (K := K) allocation dilation
  | .inl h => w.1 h
  | .inr (.inl h) => w.2.1 h
  | .inr (.inr h) => w.2.2 h

theorem parts_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : Parts (K := K) allocation dilation) :
    grouped allocation dilation F ε (joinParts allocation dilation x)
      (joinParts allocation dilation y) (joinParts allocation dilation z) =
    partsTensor allocation dilation F ε x y z := by
  unfold grouped CommonDimensions.familyProduct
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  rfl

def partsMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (grouped (K := K) allocation dilation F ε)
      (partsTensor (K := K) allocation dilation F ε) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (joinParts (K := K) allocation dilation) (joinParts (K := K) allocation dilation)
    (joinParts (K := K) allocation dilation) _).symm.trans ?_⟩
  funext x y z
  exact parts_coefficient allocation dilation F ε x y z

def map (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (stateTensor F (K := K) allocation dilation ε (K + 2))
      (partsTensor (K := K) allocation dilation F ε) :=
  (groupedMap allocation dilation F ε).comp (partsMap allocation dilation F ε)

end MatrixMultiplication.AllFieldFinalState

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCoarseReorder
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.JointCoarseReorder
open JointCoarseHashing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem reorder_support {P : Type*} (sigma : Equiv.Perm (Fin 3)) (S : P → ℕ)
    (t : Triple P) (ht : HasSupportSum S t) : HasSupportSum S (reorder sigma t) := by
  intro p
  have hsum : (∑ i : Fin 3, (tripleSide (sigma i) t p).val) =
      ∑ i : Fin 3, (tripleSide i t p).val :=
    Equiv.sum_comp sigma (fun i : Fin 3 => (tripleSide i t p).val)
  simpa [reorder, tripleSide, Fin.sum_univ_succ, Nat.add_assoc] using hsum.trans (by
    simpa [tripleSide, Fin.sum_univ_succ, Nat.add_assoc] using ht p)

end MatrixMultiplication.JointCoarseReorder

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCanonicalMixed
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCanonicalMixed

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization JointCanonicalCW
open CWStrands HistorySymmetry InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [CommRing F]
    (counts : H → Shape → ℕ) (leftLength rightLength : H → ℕ)
    (parentShape : H → Fin 3 → ℕ) (sharing : H → Bool)
    (hleft : ∀ h, leftLength h ≤ 8)

def inputTensor (h : H) : Tensor F
    (Left leftLength h × Right rightLength h)
    (Left leftLength h × Right rightLength h)
    (Left leftLength h × Right rightLength h) :=
  if sharing h then parentTensor leftLength rightLength parentShape h
  else Tensor.product (strand (Fin (leftLength h))) (strand (Fin (rightLength h)))

end MatrixMultiplication.JointCanonicalMixed

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWStageCPlacements
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instDecidableEqResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instFintypeResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.CWStageCProducts.join_split_children _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.CommonDimensions

namespace MatrixMultiplication.TerminalProducts

variable {K H : Type*} [CommSemiring K] [Fintype H] [DecidableEq H]

theorem restrict_familyProduct {X Y Z X' Y' Z' : H → Type*}
    [∀ h, Fintype (X h)] [∀ h, Fintype (Y h)] [∀ h, Fintype (Z h)]
    (T : ∀ h, Tensor K (X h) (Y h) (Z h))
    (a : ∀ h, X' h → X h → K) (b : ∀ h, Y' h → Y h → K)
    (c : ∀ h, Z' h → Z h → K) :
    Tensor.restrict (fun x s => ∏ h, a h (x h) (s h))
      (fun y s => ∏ h, b h (y h) (s h)) (fun z s => ∏ h, c h (z h) (s h))
      (familyProduct T) = familyProduct (fun h => Tensor.restrict (a h) (b h) (c h) (T h)) := by
  funext x y z
  simp only [Tensor.restrict, familyProduct, Fintype.prod_sum, ← Finset.prod_mul_distrib]

theorem matrix_restriction_of_history_restrictions {X Y Z : H → Type*}
    [∀ h, Fintype (X h)] [∀ h, Fintype (Y h)] [∀ h, Fintype (Z h)]
    (T : ∀ h, Tensor K (X h) (Y h) (Z h)) (A B C : H → Type*)
    [∀ h, Fintype (A h)] [∀ h, Fintype (B h)] [∀ h, Fintype (C h)]
    [∀ h, DecidableEq (A h)] [∀ h, DecidableEq (B h)] [∀ h, DecidableEq (C h)]
    (a : ∀ h, (A h × B h) → X h → K) (b : ∀ h, (B h × C h) → Y h → K)
    (c : ∀ h, (C h × A h) → Z h → K)
    (hloc : ∀ h, Tensor.restrict (a h) (b h) (c h) (T h) =
      Tensor.matrixCoefficients (A h) (B h) (C h)) :
    ∃ (aa : ((∀ h, A h) × (∀ h, B h)) → (∀ h, X h) → K)
      (bb : ((∀ h, B h) × (∀ h, C h)) → (∀ h, Y h) → K)
      (cc : ((∀ h, C h) × (∀ h, A h)) → (∀ h, Z h) → K),
      Tensor.restrict aa bb cc (familyProduct T) =
        Tensor.matrixCoefficients (∀ h, A h) (∀ h, B h) (∀ h, C h) := by
  classical
  have hp := restrict_familyProduct T a b c
  simp_rw [hloc] at hp
  obtain ⟨aa, bb, cc, hmatrix⟩ := matrix_familyProduct_restrict (K := K) A B C
  refine ⟨Tensor.composeRestrictionMatrix aa (fun x s => ∏ h, a h (x h) (s h)),
    Tensor.composeRestrictionMatrix bb (fun y s => ∏ h, b h (y h) (s h)),
    Tensor.composeRestrictionMatrix cc (fun z s => ∏ h, c h (z h) (s h)), ?_⟩
  rw [← Tensor.restrict_restrict, hp, hmatrix]

end MatrixMultiplication.TerminalProducts

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.CWStageC

open MatrixMultiplication.Foundation CWStrands CWLeafRestrictions

@[simp] theorem interior_weight (i : Fin 5) : CWLeafStatistics.weight (interior i) = 1 := by
  have hi : i.val + 1 ≠ 6 := by have := i.isLt; omega
  simp [CWLeafStatistics.weight, interior, hi]

@[simp] theorem zero_weight : CWLeafStatistics.weight (0 : Fin 7) = 0 := rfl

@[simp] theorem last_weight : CWLeafStatistics.weight (6 : Fin 7) = 2 := rfl

@[simp] theorem interior_complement (i : Fin 5) : complement 5 (interior i) = interior i := by
  apply complement_interior
  · simp [interior]
  · dsimp [interior]
    have := i.isLt
    omega

variable (F : Type*) [CommRing F]

theorem coefficient110 (i j : Fin 5) :
    FieldCW.tensor F 5 (interior i) (interior j) 0 = if i = j then 1 else 0 := by
  simpa only [interior_complement, interior_injective.eq_iff] using
    tensor_last_zero_matching F 5 (interior i) (interior j)

theorem coefficient101 (i j : Fin 5) :
    FieldCW.tensor F 5 (interior i) 0 (interior j) = if i = j then 1 else 0 := by
  simpa only [interior_complement, interior_injective.eq_iff] using
    tensor_middle_zero_matching F 5 (interior i) (interior j)

theorem coefficient011 (i j : Fin 5) :
    FieldCW.tensor F 5 0 (interior i) (interior j) = if i = j then 1 else 0 := by
  simpa only [interior_complement, interior_injective.eq_iff] using
    tensor_zero_matching F 5 (interior i) (interior j)

theorem coefficient002 : FieldCW.tensor F 5 0 0 6 = 1 := by
  simpa [complement, lastLabel] using tensor_zero_matching F 5 0 0

theorem branch0 :
    Tensor.pullback (fun x : Unit × Fin 5 => (Matrix.vecCons (0) (Matrix.vecCons (interior x.2) Matrix.vecEmpty)))
      (fun y : Fin 5 × Unit => (Matrix.vecCons (0) (Matrix.vecCons (interior y.1) Matrix.vecEmpty)))
      (fun _ : Unit × Unit => (Matrix.vecCons (6) (Matrix.vecCons (0) Matrix.vecEmpty)))
      (shapeTensor (F := F) (Fin 2) (Matrix.vecCons (1) (Matrix.vecCons (1) (Matrix.vecCons (2) Matrix.vecEmpty)))) =
      Tensor.matrixCoefficients Unit (Fin 5) Unit := by
  funext x y z
  simp [Tensor.pullback, shapeTensor, weight, strand, Fin.sum_univ_succ,
    Fin.prod_univ_succ, interior_weight,
    coefficient002, coefficient110, Tensor.matrixCoefficients]

theorem branch1 :
    Tensor.pullback (fun x : Unit × Fin 5 => (Matrix.vecCons (interior x.2) (Matrix.vecCons (0) Matrix.vecEmpty)))
      (fun y : Fin 5 × Unit => (Matrix.vecCons (interior y.1) (Matrix.vecCons (0) Matrix.vecEmpty)))
      (fun _ : Unit × Unit => (Matrix.vecCons (0) (Matrix.vecCons (6) Matrix.vecEmpty)))
      (shapeTensor (F := F) (Fin 2) (Matrix.vecCons (1) (Matrix.vecCons (1) (Matrix.vecCons (2) Matrix.vecEmpty)))) =
      Tensor.matrixCoefficients Unit (Fin 5) Unit := by
  funext x y z
  simp [Tensor.pullback, shapeTensor, weight, strand, Fin.sum_univ_succ,
    Fin.prod_univ_succ, interior_weight,
    coefficient002, coefficient110, Tensor.matrixCoefficients]

theorem branch2 :
    Tensor.pullback (fun x : Fin 5 × Unit => (Matrix.vecCons (0) (Matrix.vecCons (interior x.1) Matrix.vecEmpty)))
      (fun y : Unit × Fin 5 => (Matrix.vecCons (interior y.2) (Matrix.vecCons (0) Matrix.vecEmpty)))
      (fun z : Fin 5 × Fin 5 => (Matrix.vecCons (interior z.1) (Matrix.vecCons (interior z.2) Matrix.vecEmpty)))
      (shapeTensor (F := F) (Fin 2) (Matrix.vecCons (1) (Matrix.vecCons (1) (Matrix.vecCons (2) Matrix.vecEmpty)))) =
      Tensor.matrixCoefficients (Fin 5) Unit (Fin 5) := by
  funext x y z
  simp [Tensor.pullback, shapeTensor, weight, strand, Fin.sum_univ_succ,
    Fin.prod_univ_succ, interior_weight,
    coefficient011, coefficient101, Tensor.matrixCoefficients]
  all_goals (split_ifs <;> simp_all [eq_comm])

theorem branch3 :
    Tensor.pullback (fun x : Fin 5 × Unit => (Matrix.vecCons (interior x.1) (Matrix.vecCons (0) Matrix.vecEmpty)))
      (fun y : Unit × Fin 5 => (Matrix.vecCons (0) (Matrix.vecCons (interior y.2) Matrix.vecEmpty)))
      (fun z : Fin 5 × Fin 5 => (Matrix.vecCons (interior z.2) (Matrix.vecCons (interior z.1) Matrix.vecEmpty)))
      (shapeTensor (F := F) (Fin 2) (Matrix.vecCons (1) (Matrix.vecCons (1) (Matrix.vecCons (2) Matrix.vecEmpty)))) =
      Tensor.matrixCoefficients (Fin 5) Unit (Fin 5) := by
  funext x y z
  simp [Tensor.pullback, shapeTensor, weight, strand, Fin.sum_univ_succ,
    Fin.prod_univ_succ, interior_weight,
    coefficient011, coefficient101, Tensor.matrixCoefficients]
  all_goals (split_ifs <;> simp_all [eq_comm])

end MatrixMultiplication.CWStageC

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

instance smallRowFintype (b : Fin 4) : Fintype (SmallRow b) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun b => Fin.elim0 b)))) b
  all_goals dsimp [SmallRow]; infer_instance

instance smallInnerFintype (b : Fin 4) : Fintype (SmallInner b) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun b => Fin.elim0 b)))) b
  all_goals dsimp [SmallInner]; infer_instance

instance smallRowDecidableEq (b : Fin 4) : DecidableEq (SmallRow b) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun b => Fin.elim0 b)))) b
  all_goals dsimp [SmallRow]; infer_instance

instance smallInnerDecidableEq (b : Fin 4) : DecidableEq (SmallInner b) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun b => Fin.elim0 b)))) b
  all_goals dsimp [SmallInner]; infer_instance

instance rowFintype (s : Fin 3) (b : Fin 4) : Fintype (Row s b) := by
  unfold Row; split_ifs <;> infer_instance
instance middleFintype (s : Fin 3) (b : Fin 4) : Fintype (Middle s b) := by
  unfold Middle; split_ifs <;> infer_instance
instance columnFintype (s : Fin 3) (b : Fin 4) : Fintype (Column s b) := by
  unfold Column; split_ifs <;> infer_instance
instance rowDecidableEq (s : Fin 3) (b : Fin 4) : DecidableEq (Row s b) := by
  unfold Row; split_ifs <;> infer_instance
instance middleDecidableEq (s : Fin 3) (b : Fin 4) : DecidableEq (Middle s b) := by
  unfold Middle; split_ifs <;> infer_instance
instance columnDecidableEq (s : Fin 3) (b : Fin 4) : DecidableEq (Column s b) := by
  unfold Column; split_ifs <;> infer_instance

def source (F : Type*) [CommRing F] (s : Fin 3) : Tensor F Word Word Word :=
  CWStrands.shapeTensor (Fin 2) (shape s)

def branchSource (F : Type*) [CommRing F] (s : Fin 3) (b : Fin 4) :
    Tensor F Word Word Word :=
  fun x y z =>
    if CWLeafStatistics.weight (x 0) = branchAtom s b 0 ∧
      CWLeafStatistics.weight (y 0) = branchAtom s b 1 ∧
      CWLeafStatistics.weight (z 0) = branchAtom s b 2
    then source F s x y z else 0

variable (F : Type*) [CommRing F]

theorem coefficient_swapXZ (x y z : Fin 7) :
    FieldCW.tensor F 5 x y z = FieldCW.tensor F 5 z y x := by
  simp only [FieldCW.tensor, Finset.sum_add_distrib,
    mul_assoc, mul_comm, mul_left_comm]
  ring

theorem coefficient_swapYZ (x y z : Fin 7) :
    FieldCW.tensor F 5 x y z = FieldCW.tensor F 5 x z y := by
  simp only [FieldCW.tensor, Finset.sum_add_distrib,
    mul_assoc, mul_comm, mul_left_comm]
  ring

theorem source_zero_apply (x y z : Word) :
    source F 0 x y z = source F 2 z y x := by
  have hs : CWStrands.strand (F := F) (Fin 2) x y z =
      CWStrands.strand (F := F) (Fin 2) z y x := by
    apply Finset.prod_congr rfl
    intro i hi
    exact coefficient_swapXZ F (x i) (y i) (z i)
  simp [source, CWStrands.shapeTensor, shape, hs, and_comm, and_assoc]

theorem source_one_apply (x y z : Word) :
    source F 1 x y z = source F 2 x z y := by
  have hs : CWStrands.strand (F := F) (Fin 2) x y z =
      CWStrands.strand (F := F) (Fin 2) x z y := by
    apply Finset.prod_congr rfl
    intro i hi
    exact coefficient_swapYZ F (x i) (y i) (z i)
  simp [source, CWStrands.shapeTensor, shape, hs, and_comm]

theorem source_two : source F 2 =
    CWStrands.shapeTensor (F := F) (Fin 2) (Matrix.vecCons (1) (Matrix.vecCons (1) (Matrix.vecCons (2) Matrix.vecEmpty))) := by
  congr 1

theorem canonical_masked_pullback (b : Fin 4) :
    ∃ (a : (SmallRow b × SmallInner b) → Word)
      (c : (SmallInner b × SmallRow b) → Word)
      (e : (SmallRow b × SmallRow b) → Word),
      Tensor.pullback a c e (branchSource F 2 b) =
        Tensor.matrixCoefficients (SmallRow b) (SmallInner b) (SmallRow b) := by
  fin_cases b
  · refine ⟨(fun x : Unit × Fin 5 => (Matrix.vecCons (CWStageC.interior x.2) (Matrix.vecCons (0) Matrix.vecEmpty))),
      (fun y : Fin 5 × Unit => (Matrix.vecCons (CWStageC.interior y.1) (Matrix.vecCons (0) Matrix.vecEmpty))),
      (fun _ : Unit × Unit => (Matrix.vecCons (0) (Matrix.vecCons (6) Matrix.vecEmpty))), ?_⟩
    funext x y z
    have h := congrFun (congrFun (congrFun (CWStageC.branch1 F) x) y) z
    convert h using 1 <;> first | rfl | simp [Tensor.pullback, branchSource, branchAtom, canonicalAtom, CWStageC.zero_weight, CWStageC.interior_weight, source_two]
  · refine ⟨(fun x : Unit × Fin 5 => (Matrix.vecCons (0) (Matrix.vecCons (CWStageC.interior x.2) Matrix.vecEmpty))),
      (fun y : Fin 5 × Unit => (Matrix.vecCons (0) (Matrix.vecCons (CWStageC.interior y.1) Matrix.vecEmpty))),
      (fun _ : Unit × Unit => (Matrix.vecCons (6) (Matrix.vecCons (0) Matrix.vecEmpty))), ?_⟩
    funext x y z
    have h := congrFun (congrFun (congrFun (CWStageC.branch0 F) x) y) z
    convert h using 1 <;> rfl
  · refine ⟨(fun x : Fin 5 × Unit => (Matrix.vecCons (CWStageC.interior x.1) (Matrix.vecCons (0) Matrix.vecEmpty))),
      (fun y : Unit × Fin 5 => (Matrix.vecCons (0) (Matrix.vecCons (CWStageC.interior y.2) Matrix.vecEmpty))),
      (fun z : Fin 5 × Fin 5 => (Matrix.vecCons (CWStageC.interior z.2) (Matrix.vecCons (CWStageC.interior z.1) Matrix.vecEmpty))), ?_⟩
    funext x y z
    have h := congrFun (congrFun (congrFun (CWStageC.branch3 F) x) y) z
    convert h using 1 <;> first | rfl | simp [Tensor.pullback, branchSource, branchAtom, canonicalAtom, CWStageC.zero_weight, CWStageC.interior_weight, source_two]
  · refine ⟨(fun x : Fin 5 × Unit => (Matrix.vecCons (0) (Matrix.vecCons (CWStageC.interior x.1) Matrix.vecEmpty))),
      (fun y : Unit × Fin 5 => (Matrix.vecCons (CWStageC.interior y.2) (Matrix.vecCons (0) Matrix.vecEmpty))),
      (fun z : Fin 5 × Fin 5 => (Matrix.vecCons (CWStageC.interior z.1) (Matrix.vecCons (CWStageC.interior z.2) Matrix.vecEmpty))), ?_⟩
    funext x y z
    have h := congrFun (congrFun (congrFun (CWStageC.branch2 F) x) y) z
    convert h using 1 <;> first | rfl | simp [Tensor.pullback, branchSource, branchAtom, canonicalAtom, CWStageC.zero_weight, CWStageC.interior_weight, source_two]

theorem branchSource_zero_apply (b : Fin 4) (x y z : Word) :
    branchSource F 0 b x y z = branchSource F 2 b z y x := by
  simp [branchSource, branchAtom, source_zero_apply,
    and_comm, and_assoc]

theorem branchSource_one_apply (b : Fin 4) (x y z : Word) :
    branchSource F 1 b x y z = branchSource F 2 b x z y := by
  simp [branchSource, branchAtom, source_one_apply,
    and_comm]

theorem oriented_masked_pullback (s : Fin 3) (b : Fin 4) :
    ∃ (a : (Row s b × Middle s b) → Word)
      (c : (Middle s b × Column s b) → Word)
      (e : (Column s b × Row s b) → Word),
      Tensor.pullback a c e (branchSource F s b) =
        Tensor.matrixCoefficients (Row s b) (Middle s b) (Column s b) := by
  obtain ⟨a, c, e, h⟩ := canonical_masked_pullback F b
  fin_cases s
  · refine ⟨fun x => e x.swap, fun y => c y.swap, fun z => a z.swap, ?_⟩
    funext x y z
    have hh := congrFun (congrFun (congrFun h z.swap) y.swap) x.swap
    simpa [Tensor.pullback, branchSource_zero_apply, Row, Middle, Column,
      Tensor.matrixCoefficients, Prod.swap, eq_comm, and_comm, and_left_comm, and_assoc] using hh
  · refine ⟨fun x => a x.swap, fun y => e y.swap, fun z => c z.swap, ?_⟩
    funext x y z
    have hh := congrFun (congrFun (congrFun h x.swap) z.swap) y.swap
    simpa [Tensor.pullback, branchSource_one_apply, Row, Middle, Column,
      Tensor.matrixCoefficients, Prod.swap, eq_comm, and_comm, and_left_comm, and_assoc] using hh
  · exact ⟨a, c, e, h⟩

end MatrixMultiplication.CWStageCProducts

end

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.CWStageCProducts

attribute [local instance] Classical.propDecidable Classical.decEq

theorem card_rowWords (s : Fin 3) (counts : Fin 4 → ℕ) :
    Fintype.card (RowWords s counts) =
      5 ^ (if s = 1 then singleCount counts else crossCount counts) := by
  rw [Fintype.card_pi, Fintype.prod_sigma]
  simp only [Fintype.card_eq_nat_card]
  fin_cases s <;>
    simp [Fin.prod_univ_succ, Row, SmallRow, SmallInner, singleCount, crossCount, pow_add]

theorem card_middleWords (s : Fin 3) (counts : Fin 4 → ℕ) :
    Fintype.card (MiddleWords s counts) =
      5 ^ (if s = 2 then singleCount counts else crossCount counts) := by
  rw [Fintype.card_pi, Fintype.prod_sigma]
  simp only [Fintype.card_eq_nat_card]
  fin_cases s <;>
    simp [Fin.prod_univ_succ, Middle, SmallRow, SmallInner, singleCount, crossCount, pow_add]

theorem card_columnWords (s : Fin 3) (counts : Fin 4 → ℕ) :
    Fintype.card (ColumnWords s counts) =
      5 ^ (if s = 0 then singleCount counts else crossCount counts) := by
  rw [Fintype.card_pi, Fintype.prod_sigma]
  simp only [Fintype.card_eq_nat_card]
  fin_cases s <;>
    simp [Fin.prod_univ_succ, Column, SmallRow, SmallInner, singleCount, crossCount, pow_add]

def volume (s : Fin 3) (counts : Fin 4 → ℕ) : ℕ :=
  Fintype.card (RowWords s counts) * Fintype.card (MiddleWords s counts) *
    Fintype.card (ColumnWords s counts)

theorem volume_eq (s : Fin 3) (counts : Fin 4 → ℕ) :
    volume s counts = 5 ^ (singleCount counts + 2 * crossCount counts) := by
  rw [volume, card_rowWords, card_middleWords, card_columnWords]
  fin_cases s <;> simp [pow_add, two_mul] <;> ring

theorem volume_pos (s : Fin 3) (counts : Fin 4 → ℕ) : 0 < volume s counts := by
  rw [volume_eq]
  positivity

variable {H : Type*} [Fintype H]

def historyVolume (side : H → Fin 3) (counts : H → Fin 4 → ℕ) : ℕ :=
  Fintype.card (HistoryRowWords side counts) *
    Fintype.card (HistoryMiddleWords side counts) *
      Fintype.card (HistoryColumnWords side counts)

theorem historyVolume_eq_prod (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    historyVolume side counts = ∏ h, volume (side h) (counts h) := by
  simp only [historyVolume, HistoryRowWords, HistoryMiddleWords, HistoryColumnWords,
    Fintype.card_pi, volume, Finset.prod_mul_distrib]

abbrev PopulationHistory (K : ℕ) := AllFieldHistory.PartC K × AllFieldHistory.Placement

def populationSide {K : ℕ} (h : PopulationHistory K) : Fin 3 :=
  h.2 (AllFieldHistory.stageCDistinguished (AllFieldHistory.cShapeParent h.1))

def populationAtomCounts {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) (h : PopulationHistory K) (i : Fin 4) : ℕ :=
  AllFieldHistory.population allocation dilation (.afterC (h.1, i, false), h.2)

def populationVolume {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) : ℕ :=
  historyVolume (populationSide (K := K)) (populationAtomCounts allocation dilation)

end MatrixMultiplication.CWStageCProducts

end

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

theorem branchAtom_eq_stageCAtom (u : AllFieldParameters.Shape) (b : Fin 4) :
    branchAtom (AllFieldHistory.stageCDistinguished u) b = AllFieldHistory.stageCAtom u b := by
  rfl

theorem shape_eq_parent (u : AllFieldParameters.Shape)
    (hu : u ∈ AllFieldParameters.shapes 4) (hpos : AllFieldParameters.positive u = true) :
    shape (AllFieldHistory.stageCDistinguished u) = u := by
  rcases AllFieldHistory.positive_four_shapes u hu hpos with rfl | rfl | rfl <;>
    funext i <;> fin_cases i <;> rfl

end MatrixMultiplication.CWStageCProducts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWStageCStatistics
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

def siteTensor (F : Type*) [CommRing F] (g : Fin 3 → ℕ) :
    Tensor F (Fin 7) (Fin 7) (Fin 7) :=
  fun x y z => if CWLeafStatistics.weight x = g 0 ∧
    CWLeafStatistics.weight y = g 1 ∧ CWLeafStatistics.weight z = g 2
    then FieldCW.tensor F 5 x y z else 0

theorem siteTensor_eq_shapeTensor (F : Type*) [CommRing F] (g : Fin 3 → ℕ) :
    Tensor.pullback (fun (x : Fin 7) (_ : Fin 1) => x)
      (fun (y : Fin 7) (_ : Fin 1) => y) (fun (z : Fin 7) (_ : Fin 1) => z)
      (CWStrands.shapeTensor (F := F) (Fin 1) g) = siteTensor F g := by
  funext x y z
  simp [Tensor.pullback, CWStrands.shapeTensor, CWStrands.weight, CWStrands.strand,
    siteTensor]

def childProduct (F : Type*) [CommRing F] (s : Fin 3) (b : Fin 4) :
    Tensor F ChildPair ChildPair ChildPair :=
  Tensor.product (siteTensor F (branchAtom s b))
    (siteTensor F (fun i => shape s i - branchAtom s b i))

theorem weight_joinChildren (x : ChildPair) :
    CWStrands.weight (joinChildren x) =
      CWLeafStatistics.weight x.1 + CWLeafStatistics.weight x.2 := by
  simp [CWStrands.weight, joinChildren, Fin.sum_univ_succ]

theorem strand_joinChildren (F : Type*) [CommRing F] (x y z : ChildPair) :
    CWStrands.strand (F := F) (Fin 2) (joinChildren x) (joinChildren y) (joinChildren z) =
      FieldCW.tensor F 5 x.1 y.1 z.1 * FieldCW.tensor F 5 x.2 y.2 z.2 := by
  simp [CWStrands.strand, joinChildren, Fin.prod_univ_succ]

theorem masked_eq_childProduct (F : Type*) [CommRing F] (s : Fin 3) (b : Fin 4) :
    Tensor.pullback joinChildren joinChildren joinChildren (branchSource F s b) =
      childProduct F s b := by
  funext x y z
  have h0 := branchAtom_le_shape s b 0
  have h1 := branchAtom_le_shape s b 1
  have h2 := branchAtom_le_shape s b 2
  by_cases hL : CWLeafStatistics.weight x.1 = branchAtom s b 0 ∧
      CWLeafStatistics.weight y.1 = branchAtom s b 1 ∧
      CWLeafStatistics.weight z.1 = branchAtom s b 2
  · have htotal :
        (CWLeafStatistics.weight x.1 + CWLeafStatistics.weight x.2 = shape s 0 ∧
          CWLeafStatistics.weight y.1 + CWLeafStatistics.weight y.2 = shape s 1 ∧
          CWLeafStatistics.weight z.1 + CWLeafStatistics.weight z.2 = shape s 2) ↔
        (CWLeafStatistics.weight x.2 = shape s 0 - branchAtom s b 0 ∧
          CWLeafStatistics.weight y.2 = shape s 1 - branchAtom s b 1 ∧
          CWLeafStatistics.weight z.2 = shape s 2 - branchAtom s b 2) := by
      rcases hL with ⟨hx, hy, hz⟩
      constructor <;> rintro ⟨ha, hb, hc⟩ <;>
        exact ⟨by omega, by omega, by omega⟩
    simp only [hL.1, hL.2.1, hL.2.2] at htotal
    simp [Tensor.pullback, branchSource, source, CWStrands.shapeTensor,
      weight_joinChildren, strand_joinChildren, childProduct, Tensor.product, siteTensor,
      hL, htotal, mul_ite]
  · simp [Tensor.pullback, branchSource, childProduct, Tensor.product, siteTensor, hL]

theorem childProduct_split (F : Type*) [CommRing F] (s : Fin 3) (b : Fin 4)
    (x y z : Word) :
    childProduct F s b (splitChildren x) (splitChildren y) (splitChildren z) =
      branchSource F s b x y z := by
  have h := congrFun (congrFun (congrFun (masked_eq_childProduct F s b)
    (splitChildren x)) (splitChildren y)) (splitChildren z)
  simpa only [Tensor.pullback, join_split_children] using h.symm

theorem childProduct_pullback (F : Type*) [CommRing F] (s : Fin 3) (b : Fin 4) :
    ∃ (a : (Row s b × Middle s b) → ChildPair)
      (c : (Middle s b × Column s b) → ChildPair)
      (e : (Column s b × Row s b) → ChildPair),
      Tensor.pullback a c e (childProduct F s b) =
        Tensor.matrixCoefficients (Row s b) (Middle s b) (Column s b) := by
  obtain ⟨a, c, e, h⟩ := oriented_masked_pullback F s b
  refine ⟨splitChildren ∘ a, splitChildren ∘ c, splitChildren ∘ e, ?_⟩
  funext x y z
  change childProduct F s b (splitChildren (a x)) (splitChildren (c y))
    (splitChildren (e z)) = _
  rw [childProduct_split]
  exact congrFun (congrFun (congrFun h x) y) z

theorem childProduct_restriction (F : Type*) [CommRing F] (s : Fin 3) (b : Fin 4) :
    ∃ (a : (Row s b × Middle s b) → ChildPair → F)
      (c : (Middle s b × Column s b) → ChildPair → F)
      (e : (Column s b × Row s b) → ChildPair → F),
      Tensor.restrict a c e (childProduct F s b) =
        Tensor.matrixCoefficients (Row s b) (Middle s b) (Column s b) := by
  classical
  obtain ⟨a, c, e, h⟩ := childProduct_pullback F s b
  refine ⟨(fun x w => if w = a x then 1 else 0),
    (fun y w => if w = c y then 1 else 0),
    (fun z w => if w = e z then 1 else 0), ?_⟩
  rw [← Tensor.pullback_eq_restrict]
  exact h

def placedChildProduct (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :=
  childProduct F (phi s) (atomPermutation s phi b)

theorem placedChildProduct_eq (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    placedChildProduct F s phi b =
      Tensor.product (siteTensor F (fun i => branchAtom s b (phi.symm i)))
        (siteTensor F (fun i => shape s (phi.symm i) - branchAtom s b (phi.symm i))) := by
  have ha : branchAtom (phi s) (atomPermutation s phi b) =
      fun i => branchAtom s b (phi.symm i) := by
    funext i
    simpa only [Equiv.apply_symm_apply] using branchAtom_transport s phi b (phi.symm i)
  have hs : shape (phi s) = fun i => shape s (phi.symm i) := by
    funext i
    exact shape_transport s phi i
  simp only [placedChildProduct, childProduct, ha, hs]

theorem placedChildProduct_restriction (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    ∃ (a : (Row (phi s) b × Middle (phi s) b) → ChildPair → F)
      (c : (Middle (phi s) b × Column (phi s) b) → ChildPair → F)
      (e : (Column (phi s) b × Row (phi s) b) → ChildPair → F),
      Tensor.restrict a c e (placedChildProduct F s phi b) =
        Tensor.matrixCoefficients (Row (phi s) b) (Middle (phi s) b) (Column (phi s) b) := by
  have h := childProduct_restriction F (phi s) (atomPermutation s phi b)
  unfold placedChildProduct
  by_cases hp : phi (Equiv.swap 2 s 0) = Equiv.swap 2 (phi s) 0
  · have he : atomPermutation s phi = Equiv.refl _ := ite_eq_left hp
    rw [he] at h ⊢
    exact h
  · have he : atomPermutation s phi = Equiv.swap 2 3 := ite_eq_right hp
    rw [he] at h ⊢
    fin_cases b <;> norm_num only [Equiv.swap_apply_def] at h ⊢ <;> exact h

end MatrixMultiplication.CWStageCProducts

end

noncomputable section
section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

def placedShapeChildProduct (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) : Tensor F ChildWords ChildWords ChildWords :=
  Tensor.product
    (CWStrands.shapeTensor (Fin 1) (fun i => branchAtom s b (phi.symm i)))
    (CWStrands.shapeTensor (Fin 1)
      (fun i => shape s (phi.symm i) - branchAtom s b (phi.symm i)))

theorem placedShapeChildProduct_eq_stageC (F : Type*) [CommRing F]
    (u : AllFieldParameters.Shape) (hu : u ∈ AllFieldParameters.shapes 4)
    (hpos : AllFieldParameters.positive u = true)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    placedShapeChildProduct F (AllFieldHistory.stageCDistinguished u) phi b =
      Tensor.product
        (CWStrands.shapeTensor (Fin 1) (fun i => AllFieldHistory.stageCAtom u b (phi.symm i)))
        (CWStrands.shapeTensor (Fin 1) (fun i => u (phi.symm i) -
          AllFieldHistory.stageCAtom u b (phi.symm i))) := by
  unfold placedShapeChildProduct
  rw [branchAtom_eq_stageCAtom, shape_eq_parent u hu hpos]

theorem placedShapeChildProduct_pullback (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    Tensor.pullback singletonChildWords singletonChildWords singletonChildWords
      (placedShapeChildProduct F s phi b) = placedChildProduct F s phi b := by
  rw [placedChildProduct_eq]
  funext x y z
  have hL := congrFun (congrFun (congrFun
    (siteTensor_eq_shapeTensor F (fun i => branchAtom s b (phi.symm i))) x.1) y.1) z.1
  have hR := congrFun (congrFun (congrFun
    (siteTensor_eq_shapeTensor F
      (fun i => shape s (phi.symm i) - branchAtom s b (phi.symm i))) x.2) y.2) z.2
  exact congrArg₂ (fun a b : F => a * b) hL hR

theorem placedShapeChildProduct_restriction (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    ∃ (a : (Row (phi s) b × Middle (phi s) b) → ChildWords → F)
      (c : (Middle (phi s) b × Column (phi s) b) → ChildWords → F)
      (e : (Column (phi s) b × Row (phi s) b) → ChildWords → F),
      Tensor.restrict a c e (placedShapeChildProduct F s phi b) =
        Tensor.matrixCoefficients (Row (phi s) b) (Middle (phi s) b) (Column (phi s) b) := by
  classical
  let E : ChildPair → ChildWords → F := fun p w => if w = singletonChildWords p then 1 else 0
  have hE : Tensor.restrict E E E (placedShapeChildProduct F s phi b) =
      placedChildProduct F s phi b := by
    rw [← Tensor.pullback_eq_restrict]
    exact placedShapeChildProduct_pullback F s phi b
  obtain ⟨a, c, e, h⟩ := placedChildProduct_restriction F s phi b
  refine ⟨Tensor.composeRestrictionMatrix a E, Tensor.composeRestrictionMatrix c E,
    Tensor.composeRestrictionMatrix e E, ?_⟩
  rw [← Tensor.restrict_restrict, hE, h]

def placedShapeChildProducts (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (counts : Fin 4 → ℕ) :
    Tensor F (Positions counts → ChildWords) (Positions counts → ChildWords)
      (Positions counts → ChildWords) :=
  CommonDimensions.familyProduct
    (fun p : Positions counts => placedShapeChildProduct F s phi p.1)

theorem placedShapeChildProducts_restriction (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (counts : Fin 4 → ℕ) :
    ∃ (a : (RowWords (phi s) counts × MiddleWords (phi s) counts) →
        (Positions counts → ChildWords) → F)
      (c : (MiddleWords (phi s) counts × ColumnWords (phi s) counts) →
        (Positions counts → ChildWords) → F)
      (e : (ColumnWords (phi s) counts × RowWords (phi s) counts) →
        (Positions counts → ChildWords) → F),
      Tensor.restrict a c e (placedShapeChildProducts F s phi counts) =
        Tensor.matrixCoefficients (RowWords (phi s) counts) (MiddleWords (phi s) counts)
          (ColumnWords (phi s) counts) := by
  classical
  choose a c e h using fun p : Positions counts => placedShapeChildProduct_restriction F s phi p.1
  exact TerminalProducts.matrix_restriction_of_history_restrictions
    (fun p : Positions counts => placedShapeChildProduct F s phi p.1)
    (fun p => Row (phi s) p.1) (fun p => Middle (phi s) p.1)
    (fun p => Column (phi s) p.1) a c e h

end MatrixMultiplication.CWStageCProducts

end

open scoped BigOperators
open MatrixMultiplication.Foundation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_GroupOrbitCount
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistorySupport

open AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev ActiveClass (K tick : ℕ) := Active K tick × JointPopulation.Shape

def selectedBaseCount {K tick : ℕ} (allocation : Allocation)
    (D : Finset (ActiveClass K tick)) : ℕ :=
  ∑ c ∈ D, activeCounts allocation 1 c.1 c.2

def selectedBasePopulation {K tick : ℕ} (allocation : Allocation)
    (D : Finset (ActiveClass K tick)) : ℝ := (selectedBaseCount allocation D : ℝ)

def positiveClasses {K tick : ℕ} (allocation : Allocation) (h : Active K tick) :
    Finset (ActiveClass K tick) :=
  Finset.univ.filter fun c => c.1 = h ∧ 0 < activeCounts allocation 1 c.1 c.2

end MatrixMultiplication.AllFieldHistorySupport

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryIncomingMasks

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters
open AllFieldHistoryChildLaws AllFieldHistorySupport
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def joinHalves (w : Work K) :
    ((Fin w.halfLength → Fin 7) × (Fin w.halfLength → Fin 7)) →
      (Fin (currentLength w.source) → Fin 7) :=
  match w with
  | .stageA _ => fun x => Fin.append x.1 x.2
  | .stageB _ => fun x => Fin.append x.1 x.2
  | .stageC _ => fun x => Fin.append x.1 x.2

def sourcePositionsEquiv (allocation : Allocation) (m : ℕ) (h : Active K tick) :
    JointPopulation.Positions (activeCounts allocation m) h ≃
      Fin (population allocation m (h.val.1.source, h.val.2)) :=
  finCongr (jointCounts_sum allocation m h.val)

end MatrixMultiplication.AllFieldHistoryIncomingMasks

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C]
  {P X Y : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, DecidableEq (X c)]
  [∀ c, Fintype (Y c)] [∀ c, DecidableEq (Y c)]

def pairProfile (w : CompleteWordPair P X Y) : PairProfile P X Y :=
  (InheritedMasks.profile P X w.left, InheritedMasks.profile P Y w.right)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, Fintype (Y c)] in
theorem pairProfile_smul (g : HalfClassPermutations P)
    (w : CompleteWordPair P X Y) : pairProfile (g • w) = pairProfile w := by
  apply Prod.ext
  · apply (InheritedMasks.profile_eq_iff P X _ _).mpr
    exact ⟨fun c => g.1 c, fun c => by
      funext i
      simp⟩
  · apply (InheritedMasks.profile_eq_iff P Y _ _).mpr
    exact ⟨fun c => g.2 c, fun c => by
      funext i
      simp⟩

omit [Fintype C] [DecidableEq C]
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, DecidableEq (X c)]
  [∀ c, Fintype (Y c)] [∀ c, DecidableEq (Y c)] in
theorem completeWordPair_ext {w v : CompleteWordPair P X Y}
    (hl : w.left = v.left) (hr : w.right = v.right) : w = v := by
  cases w
  cases v
  cases hl
  cases hr
  rfl

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, Fintype (Y c)] in
theorem pairProfile_eq_iff (w v : CompleteWordPair P X Y) :
    pairProfile w = pairProfile v ↔
      ∃ g : HalfClassPermutations P, g • w = v := by
  constructor
  · intro h
    have hl := (InheritedMasks.profile_eq_iff P X w.left v.left).mp
      (congrArg Prod.fst h)
    have hr := (InheritedMasks.profile_eq_iff P Y w.right v.right).mp
      (congrArg Prod.snd h)
    obtain ⟨el, hel⟩ := hl
    obtain ⟨er, her⟩ := hr
    refine ⟨(fun c => (el c)⁻¹, fun c => (er c)⁻¹), ?_⟩
    apply completeWordPair_ext
    · funext c i
      exact congrFun (hel c) i
    · funext c i
      exact congrFun (her c) i
  · rintro ⟨g, rfl⟩
    exact (pairProfile_smul g w).symm

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, Fintype (Y c)] in
theorem pairProfile_eq_iff_orbitRel (w v : CompleteWordPair P X Y) :
    pairProfile w = pairProfile v ↔
      MulAction.orbitRel (HalfClassPermutations P) (CompleteWordPair P X Y) w v := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (pairProfile_eq_iff v w).mp h.symm
    exact ⟨g, hg⟩
  · rintro ⟨g, rfl⟩
    exact pairProfile_smul g v

def pairOrbitProfile : PairOrbit P X Y → PairProfile P X Y :=
  Quotient.lift pairProfile fun w v h => (pairProfile_eq_iff_orbitRel w v).mpr h

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, Fintype (Y c)] in
theorem pairOrbitProfile_injective :
    Function.Injective (pairOrbitProfile (P := P) (X := X) (Y := Y)) := by
  intro q r
  induction q using Quotient.inductionOn with
  | h w =>
    induction r using Quotient.inductionOn with
    | h v =>
      intro h
      apply Quotient.sound
      exact (pairProfile_eq_iff_orbitRel w v).mp h

end

end MatrixMultiplication.PermutationMatching

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryOrbitCount

open AllFieldHistory AllFieldHistorySupport PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Classes (K tick : ℕ) := ActiveClass K tick

end MatrixMultiplication.AllFieldHistoryOrbitCount

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupOrbitCount

open AllFieldHistory AllFieldHistorySupport PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable instance groupOrbitFintype {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Fintype (GroupOrbit (K := K) (tick := tick) allocation m sigma) := by
  haveI : Finite (GroupOrbit (K := K) (tick := tick) allocation m sigma) :=
    Finite.of_injective pairOrbitProfile pairOrbitProfile_injective
  exact Fintype.ofFinite _

end MatrixMultiplication.AllFieldGroupOrbitCount

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryRecoveryBudget
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section





noncomputable section

namespace MatrixMultiplication.AllFieldHistoryMasks

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistorySupport
open JointCanonicalization InheritedMasks PermutationMatching HistorySymmetry
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

abbrev Classes (K tick : ℕ) := Active K tick × JointPopulation.Shape

abbrev Positions (allocation : Allocation) (m : ℕ) (c : Classes K tick) :=
  Fin (activeCounts allocation m c.1 c.2)

abbrev Letters (c : Classes K tick) := Fin (activeHalfLength c.1) → Fin 7

abbrev Words (allocation : Allocation) (m : ℕ) :=
  CompleteWordPair (Positions (K := K) (tick := tick) allocation m) Letters Letters

abbrev MaskIndex (K tick : ℕ) := Active K tick × SymbolChoice K tick × SymbolChoice K tick

def testedClasses (allocation : Allocation) (i : MaskIndex K tick) : Finset (Classes K tick) :=
  positiveClasses allocation i.1

def classStatistic (c : Classes K tick) : Letters c → Statistic c.1 := statistic c.1

def leftSymbol (i : MaskIndex K tick) (c : Classes K tick) : Statistic c.1 := i.2.1 c.1

def rightSymbol (i : MaskIndex K tick) (c : Classes K tick) : Statistic c.1 := i.2.2 c.1

def leftProbability (side : Fin 3) (i : MaskIndex K tick) (c : Classes K tick) : ℝ :=
  leftLaw c.1 c.2 side (leftSymbol i c)

def rightProbability (side : Fin 3) (i : MaskIndex K tick) (c : Classes K tick) : ℝ :=
  rightLaw c.1 c.2 side (rightSymbol i c)

def center (allocation : Allocation) (side : Fin 3) (i : MaskIndex K tick) : ℝ :=
  classProductMixture (fun c : testedClasses allocation i => Positions allocation 1 c.val)
    (fun c => leftProbability side i c.val) (fun c => rightProbability side i c.val)

def childWindows (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : Words (K := K) (tick := tick) allocation m) : Prop :=
  HistorySymmetry.childWindows classStatistic classStatistic
    (activeLaw (activeCounts allocation m) (fun c => leftLaw c.1 c.2 side))
    (activeLaw (activeCounts allocation m) (fun c => rightLaw c.1 c.2 side))
    (activeWidth (activeCounts allocation m) (fun c => childWidth ε c.1))
    (activeWidth (activeCounts allocation m) (fun c => childWidth ε c.1)) w

def lossConstant (allocation : Allocation) (ε : ℝ) : ℝ :=
  ∑ i : MaskIndex K tick,
    1 / (2 * selectedBasePopulation allocation (testedClasses allocation i) *
      (pairWidth ε i.1) ^ 2)

end MatrixMultiplication.AllFieldHistoryMasks






end
end




section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryRecovery

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistoryChildLaws
open AllFieldHistorySupport JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def childStatistic (_side : Fin 3) (c : Active K tick × JointPopulation.Shape) :=
  statistic c.1

def leftPrescription (side : Fin 3) (c : Active K tick × JointPopulation.Shape) :=
  leftLaw c.1 c.2 side

def rightPrescription (side : Fin 3) (c : Active K tick × JointPopulation.Shape) :=
  rightLaw c.1 c.2 side

def outputWidth (ε : ℝ) (_side : Fin 3) (c : Active K tick × JointPopulation.Shape) :=
  AllFieldHistoryMasks.childWidth ε c.1

def parents (F : Type*) [CommRing F] (h : Active K tick) :=
  JointCanonicalMixed.inputTensor (F := F) activeHalfLength activeHalfLength
    activeParentShape (fun _ => true) h

def canonical (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) (ε : ℝ) :
    Tensor F (AllFieldHistoryMasks.Words (K := K) (tick := tick) allocation m)
      (AllFieldHistoryMasks.Words (K := K) (tick := tick) allocation m) (AllFieldHistoryMasks.Words (K := K) (tick := tick) allocation m) :=
  canonicalIdeal (activeCounts allocation m) (Left activeHalfLength)
    (Right activeHalfLength) (parents F)
    (coarse activeHalfLength activeHalfLength halfLength_le_eight)
    childStatistic childStatistic leftPrescription rightPrescription
    (outputWidth ε) (outputWidth ε)

end MatrixMultiplication.AllFieldHistoryRecovery






namespace MatrixMultiplication.AllFieldHistoryRecovery

open AllFieldHistory AllFieldHistorySupport

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def minimumDilation (allocation : Allocation) (ε : ℝ) : ℕ :=
  Nat.ceil (3 * (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6)) + 2

end MatrixMultiplication.AllFieldHistoryRecovery

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryGroupCore
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupMasks

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryMasks AllFieldHistoryIncomingMasks
open JointPopulation JointCanonicalization JointCanonicalCW InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def marginal (allocation : Allocation) (m : ℕ) (side : Fin 3) (sigma : Placement)
    (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∀ (h : ActiveOrder K tick sigma) a,
    wordPopulation (fun j => coarse activeHalfLength activeHalfLength
      AllFieldHistoryRecovery.halfLength_le_eight side h.val (w h j)) a =
    wordPopulation (sideWord (activeCounts allocation m) side
      (triple (activeCounts allocation m) (canonicalTarget (activeCounts allocation m))) h.val) a

def incoming (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (h : ActiveOrder K tick sigma) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) :
    HistoryWord allocation m (h.val.val.1.source, h.val.val.2) :=
  fun p => joinHalves h.val.val.1
    (w h ((sourcePositionsEquiv allocation m h.val).symm p))

def received (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (sigma : Placement) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∀ h : ActiveOrder K tick sigma,
    residentMask allocation m ε (h.val.val.1.source, h.val.val.2) side
      (incoming allocation m sigma h w)

def rawPass (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (sigma : Placement) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∀ (i : MaskIndex K tick) (hi : i.1.val.physicalOrder = sigma),
    |(∑ j : JointPopulation.Positions (activeCounts allocation m) i.1,
        if statistic i.1 (w ⟨i.1, hi⟩ j).1 = i.2.1 i.1 ∧
          statistic i.1 (w ⟨i.1, hi⟩ j).2 = i.2.2 i.1 then (1 : ℝ) else 0) /
        (population allocation m (i.1.val.1.source, i.1.val.2) : ℝ) -
      center allocation side i| ≤ pairWidth ε i.1

def completeKeep (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (sigma : Placement) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  marginal allocation m side sigma w ∧ received allocation m ε side sigma w ∧
    rawPass allocation m ε side sigma w

end MatrixMultiplication.AllFieldHistoryGroupMasks

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRates
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section





noncomputable section






namespace MatrixMultiplication.AllFieldZeroLeafRates

open MatrixMultiplication.Foundation Filter AllFieldParameters CWWindowedLeaves CWCompleteStatistics
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

abbrev fourWords (t : Shape) (counts : PairSlot → ℕ) (m : ℕ) :=
  ExactStatisticWords.Words
    (fun w : Alphabet 4 (shapeMax t) => fourStatistic w.val) (fun s => m * counts s)

def twoWords (k : Fin 5) (counts : Fin 6 → ℕ) (m : ℕ) :=
  ExactStatisticWords.Words
    (fun w : Alphabet 2 k.val => twoStatistic w.val) (fun s => m * counts s)

instance twoWordsFintype (k : Fin 5) (counts : Fin 6 → ℕ) (m : ℕ) :
    Fintype (twoWords k counts m) := by
  unfold twoWords
  infer_instance

theorem four_supported (t : Shape) (counts : PairSlot → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (zeroPairLaw t s.1 s.2 : ℝ)) (s : PairSlot) (hs : 0 < counts s) :
    Fintype.card {w : Alphabet 4 (shapeMax t) // fourStatistic w.val = s} =
      AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2 := by
  apply four_fixedWeight_multiplicity
  by_contra hweight
  have hzero := zeroPairLaw_outside_support t s.1 s.2 hweight
  have hpos : (0 : ℝ) < (counts s : ℝ) / (∑ s, counts s : ℕ) :=
    div_pos (by exact_mod_cast hs) (by exact_mod_cast hD)
  rw [hlaw s, hzero, Rat.cast_zero] at hpos
  exact (lt_irrefl 0) hpos

theorem two_supported (d : ℚ) (k : Fin 5) (counts : Fin 6 → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (statisticLaw d k s : ℝ)) (s : Fin 6) (hs : 0 < counts s) :
    Fintype.card {w : Alphabet 2 k.val // twoStatistic w.val = s} =
      AllFieldParameters.multiplicity s := by
  apply two_fixedWeight_multiplicity
  by_contra hweight
  have hzero := statisticLaw_outside_support d k s hweight
  have hpos : (0 : ℝ) < (counts s : ℝ) / (∑ s, counts s : ℕ) :=
    div_pos (by exact_mod_cast hs) (by exact_mod_cast hD)
  rw [hlaw s, hzero, Rat.cast_zero] at hpos
  exact (lt_irrefl 0) hpos

theorem four_card_pos (t : Shape) (counts : PairSlot → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (zeroPairLaw t s.1 s.2 : ℝ)) (m : ℕ) :
    0 < Fintype.card (fourWords t counts m) := by
  apply ExactStatisticWords.card_pos_of_supported
    (fun w : Alphabet 4 (shapeMax t) => fourStatistic w.val) (fun s => m * counts s)
    (fun s => AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2)
  · intro s hs
    exact four_supported t counts hD hlaw s (Nat.pos_of_mul_pos_left hs)
  · intro s _
    exact Nat.mul_pos (multiplicity_pos s.1) (multiplicity_pos s.2)

theorem two_card_pos (d : ℚ) (k : Fin 5) (counts : Fin 6 → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (statisticLaw d k s : ℝ)) (m : ℕ) :
    0 < Fintype.card (twoWords k counts m) := by
  have h := ExactStatisticWords.card_pos_of_supported
    (fun w : Alphabet 2 k.val => twoStatistic w.val) (fun s => m * counts s)
    AllFieldParameters.multiplicity
    (fun s hs => two_supported d k counts hD hlaw s (Nat.pos_of_mul_pos_left hs))
    (fun s _ => multiplicity_pos s)
  rw [Fintype.card_eq_nat_card] at h ⊢
  exact h

end MatrixMultiplication.AllFieldZeroLeafRates

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_GroupOrbitTransport
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupOrbitData

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitCount JointPopulation JointCanonicalization
open JointCoarseHashing PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ} {sigma : Placement}

theorem reorder_support {P : Type*} (sigma : Placement) (S : P → ℕ)
    (t : Triple P) (ht : HasSupportSum S t) : HasSupportSum S (reorder sigma t) :=
  JointCoarseReorder.reorder_support sigma S t ht

def ambient (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Finset (Triple (Pos (K := K) (tick := tick) allocation m sigma)) :=
  (ambientSet (Counts (K := K) (tick := tick) allocation m sigma) (fun h => 2 * activeHalfLength h.val)).image
    (reorder sigma)

def support (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (p : Pos (K := K) (tick := tick) allocation m sigma) : ℕ :=
  2 * activeHalfLength p.1.val

theorem counts_support (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape)
    (hu : 0 < Counts (K := K) (tick := tick) allocation m sigma h u) :
    u.1.val + u.2.1.val + u.2.2.val = 2 * activeHalfLength h.val :=
  jointCounts_support_sum allocation m h.val.val u hu

theorem ambient_support (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (f : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (hf : f ∈ ambient allocation m sigma) : HasSupportSum (support allocation m sigma) f := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
  exact reorder_support sigma _ t (Finset.mem_filter.mp ht).2.1

theorem coarse_mem_ambient (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) :
    coarse allocation m sigma e ∈ ambient allocation m sigma := by
  apply Finset.mem_image.mpr
  refine ⟨triple (Counts (K := K) (tick := tick) allocation m sigma) e, ?_, rfl⟩
  apply targetSet_subset_ambient (Counts (K := K) (tick := tick) allocation m sigma)
    (fun h => 2 * activeHalfLength h.val) (counts_support allocation m sigma)
  simp only [targetSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨e, rfl⟩

def Admissible (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) : Prop :=
  groupIdealSide allocation m ε (sigma side) sigma e w ∧
    ∀ h j, CWStrands.weight (w h j).1 = (shapeSide (sigma side) ((e h).val j)).val ∧
      CWStrands.weight (w h j).2 = activeParentShape h.val (sigma side) -
        (shapeSide (sigma side) ((e h).val j)).val

def usedOrbits (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) : Finset (Orbit (K := K) (tick := tick) allocation m sigma) :=
  Finset.univ.filter fun o => ∃ w, Admissible allocation m ε sigma o.1 e w ∧
    orbitOf allocation m sigma e w = o.2

def passing (allocation : Allocation) (m : ℕ) (sigma : Placement) (ε : ℝ)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma) :
    Finset (Variable (K := K) (tick := tick) allocation m sigma) :=
  (full allocation m sigma e o).filter fun v => completeKeep allocation m ε (sigma v.1) sigma v.2

def competitors (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (_o : Orbit (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma) :
    Finset (Triple (Pos (K := K) (tick := tick) allocation m sigma)) :=
  (Finset.univ.image (coarse allocation m sigma)).filter fun t =>
    t ≠ coarse allocation m sigma e ∧
    tripleSide v.1 t = tripleSide v.1 (coarse allocation m sigma e) ∧
    ∃ f, coarse allocation m sigma f = t ∧ Compatible allocation m ε sigma v.1 f v.2

theorem full_pos (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma)
    (ho : o ∈ usedOrbits allocation m ε sigma e) : 0 < (full allocation m sigma e o).card := by
  obtain ⟨w, _, hw⟩ := (Finset.mem_filter.mp ho).2
  apply Finset.card_pos.mpr
  exact ⟨(o.1, w), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hw⟩⟩

theorem competitor_mem (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma)
    (v : Variable (K := K) (tick := tick) allocation m sigma) (t : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (ht : t ∈ competitors allocation m ε sigma e o v) : t ∈ ambient allocation m sigma := by
  obtain ⟨f, hf, _⟩ := (Finset.mem_filter.mp ht).2.2.2
  rw [← hf]
  exact coarse_mem_ambient allocation m sigma f

theorem competitor_shares (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma)
    (v : Variable (K := K) (tick := tick) allocation m sigma) (t : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (ht : t ∈ competitors allocation m ε sigma e o v) : SharesSide (coarse allocation m sigma e) t := by
  have h := (Finset.mem_filter.mp ht).2.2.1
  rcases v with ⟨side, w⟩
  fin_cases side
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

def data (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement) :
    JointMaskedSelection.OrbitData
      (Pos (K := K) (tick := tick) allocation m sigma) (Targets (K := K) (tick := tick) allocation m sigma)
      (Orbit (K := K) (tick := tick) allocation m sigma) (Variable (K := K) (tick := tick) allocation m sigma) where
  ambient := ambient allocation m sigma
  support := support allocation m sigma
  coarse := coarse allocation m sigma
  support_ambient := ambient_support allocation m sigma
  target_mem := coarse_mem_ambient allocation m sigma
  orbits := usedOrbits allocation m ε sigma
  full := full allocation m sigma
  passing := passing allocation m sigma ε
  full_pos := full_pos allocation m ε sigma
  passing_subset := fun _ _ _ => Finset.filter_subset _ _
  competitors := competitors allocation m ε sigma
  competitor_mem := fun e o _ v _ t ht => competitor_mem allocation m ε sigma e o v t ht
  competitor_ne := fun _ _ _ _ _ _ ht => (Finset.mem_filter.mp ht).2.1
  competitor_shares := fun e o _ v _ t ht => competitor_shares allocation m ε sigma e o v t ht

end MatrixMultiplication.AllFieldGroupOrbitData

end




end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_NativeCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldNativeCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {A : Type*} [Fintype A]

def nativeLA : Staggering.Capacity := fun i =>
  (positiveInitial.map fun g => (initialLaw g : ℝ) * stageACapacity g i).sum

def nativeLB : Staggering.Capacity := fun i =>
  (positiveSecond.map fun t => (secondMass t : ℝ) * stageBCapacity t i).sum

def interiorPairs : List (Shape × Shape) :=
  positiveSecond.flatMap fun t =>
    ((below t).filter positive).map fun u => (t, u)

def interiorMass (tu : Shape × Shape) : ℝ := littleMass tu.1 tu.2

def interiorEntropy (tu : Shape × Shape) : ℝ :=
  binaryEntropyRate (binaryParameter tu.1 tu.2)

def nativeLC (allocation : Fin 3 → ℝ) : Staggering.Capacity := fun i =>
  (interiorPairs.map fun tu => interiorMass tu *
    ((1 - allocation i) * Real.log 2 + allocation i * interiorEntropy tu)).sum

end MatrixMultiplication.AllFieldNativeCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_PairMarginals
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldPairMarginals

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldNativeCapacity
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def statisticWeightCode (a : Fin 6) : Fin 17 :=
  ⟨statisticWeight a, by have := statisticWeight_le_four a; omega⟩

def halfWeightCode (a : PairSlot) : Fin 17 :=
  ⟨statisticWeight a.1 + statisticWeight a.2, by
    have := statisticWeight_le_four a.1
    have := statisticWeight_le_four a.2
    omega⟩

@[simp] theorem statisticWeightCode_val (a : Fin 6) :
    (statisticWeightCode a).val = statisticWeight a := rfl

@[simp] theorem halfWeightCode_val (a : PairSlot) :
    (halfWeightCode a).val = statisticWeight a.1 + statisticWeight a.2 := rfl

end MatrixMultiplication.AllFieldPairMarginals

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_ParametersHalfComplement
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.canonicalChildShape_branchShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.decode_encodePhysicalShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.decode_encodeShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodePhysicalShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodeShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodeShape_total _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.physicalShape_complement _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.physicalShape_source _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldPairMarginals.halfWeightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

theorem pairWeight_zero : ∀ ij : PairSlot,
    statisticWeight ij.1 + statisticWeight ij.2 = 0 ↔ ij = (0,0) := by decide +kernel

theorem pairWeight_eight : ∀ ij : PairSlot,
    statisticWeight ij.1 + statisticWeight ij.2 = 8 ↔ ij = (5,5) := by decide +kernel

theorem pairKappa_zero : ∀ ij : PairSlot,
    (kappa ij.1, kappa ij.2) = (0,0) ↔ ij = (5,5) := by decide +kernel

theorem pairKappa_eight : ∀ ij : PairSlot,
    (kappa ij.1, kappa ij.2) = (5,5) ↔ ij = (0,0) := by decide +kernel

theorem halfLaw_weight_zero (t : Shape) (ht : t ∈ shapes 8) (w : Fin 3)
    (hw : t w = 0) (ij : PairSlot) :
    halfLaw t w ij = if ij = (0,0) then 1 else 0 := by
  apply normalized_singleton_law (halfLaw t w) (0,0) (halfLaw_normalized t ht w)
  intro pair hpair
  apply halfLaw_outside_support t ht w pair
  rw [hw]
  exact fun h => hpair ((pairWeight_zero pair).mp h)

theorem halfLaw_weight_eight (t : Shape) (ht : t ∈ shapes 8) (w : Fin 3)
    (hw : t w = 8) (ij : PairSlot) :
    halfLaw t w ij = if ij = (5,5) then 1 else 0 := by
  apply normalized_singleton_law (halfLaw t w) (5,5) (halfLaw_normalized t ht w)
  intro pair hpair
  apply halfLaw_outside_support t ht w pair
  rw [hw]
  exact fun h => hpair ((pairWeight_eight pair).mp h)

theorem complementary_half_sides_zero_parent : ∀ t ∈ shapes 8, ∀ w v : Fin 3,
    w ≠ v → t w + t v = 8 → t ∈ zeroSecond := by decide +kernel

theorem halfLaw_complementary_sides (t : Shape) (ht : t ∈ shapes 8)
    (w v : Fin 3) (hwv : w ≠ v) (hsum : t w + t v = 8) (ij : PairSlot) :
    halfLaw t w (kappa ij.1, kappa ij.2) = halfLaw t v ij := by
  by_cases hw : t w = 0
  · have hv : t v = 8 := by omega
    rw [halfLaw_weight_zero t ht w hw, halfLaw_weight_eight t ht v hv]
    simp only [pairKappa_zero]
  · by_cases hv : t v = 0
    · have hw8 : t w = 8 := by omega
      rw [halfLaw_weight_eight t ht w hw8, halfLaw_weight_zero t ht v hv]
      simp only [pairKappa_eight]
    · exact halfLaw_zero_complement t
        (complementary_half_sides_zero_parent t ht w v hwv hsum) w v hw hv hwv ij

theorem zero_maximum_axis_nonzero : ∀ t ∈ zeroSecond, t (halfMaxAxis t) ≠ 0 := by
  decide +kernel

theorem halfLaw_at_maximum (t : Shape) (ht : t ∈ zeroSecond) (ij : PairSlot) :
    halfLaw t (halfMaxAxis t) ij = zeroPairLaw t ij.1 ij.2 := by
  have hp : positive t ≠ true := by simpa using (List.mem_filter.mp ht).2
  simp only [halfLaw, hp, Bool.false_eq_true, ite_false, if_false,
    ite_eq_right (zero_maximum_axis_nonzero t ht), ite_true, if_true]

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_GroupAssignmentRetention
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupAdmissible

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery AllFieldGroupOrbitData
open JointPopulation JointCanonicalization PermutationMatching
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

abbrev Symmetries (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  HalfClassPermutations (ClassPositions (Counts (K := K) (tick := tick) allocation m sigma))

@[instance_reducible]
def rawAction (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) :
    MulAction (Symmetries (K := K) (tick := tick) allocation m sigma) (Raw (K := K) (tick := tick) allocation m sigma) :=
  EquivOrbitTransport.action (groupCoordinates (K := K) (tick := tick) allocation m sigma e)

end MatrixMultiplication.AllFieldGroupAdmissible

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_TerminalPopulations
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instDecidableEqResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instFintypeResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldTerminalPopulations

open AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ} {H : Type*} [Fintype H]
  {A : H → Type*} [∀ h, Fintype (A h)]

def denominator (ν : ∀ h, A h → ℚ) : ℕ :=
  AllFieldPopulationCounts.denominator (law ν)

def dilation (ν : ∀ h, A h → ℚ) (m : ℕ) : ℕ := m * denominator ν

def count (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (m : ℕ) (h : H) (a : A h) : ℕ :=
  population allocation m (history h) *
    AllFieldPopulationCounts.baseCount (law ν) ⟨h, a⟩

theorem denominator_pos (ν : ∀ h, A h → ℚ) : 0 < denominator ν :=
  AllFieldPopulationCounts.denominator_pos (law ν)

theorem dilation_pos (ν : ∀ h, A h → ℚ) {m : ℕ} (hm : 0 < m) :
    0 < dilation ν m := Nat.mul_pos hm (denominator_pos ν)

theorem baseCount_cast (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (h : H) (a : A h) :
    (AllFieldPopulationCounts.baseCount (law ν) ⟨h, a⟩ : ℚ) =
      (denominator ν : ℚ) * ν h a :=
  AllFieldPopulationCounts.baseCount_cast (law ν) (fun x => hν x.1 x.2) ⟨h, a⟩

theorem sum_baseCount (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (htotal : ∀ h, ∑ a, ν h a = 1) (h : H) :
    (∑ a, AllFieldPopulationCounts.baseCount (law ν) ⟨h, a⟩) = denominator ν := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, baseCount_cast ν hν, ← Finset.mul_sum, htotal, mul_one]

theorem population_dilation (allocation : Allocation) (ν : ∀ h, A h → ℚ)
    (m : ℕ) (h : History K) :
    population allocation (dilation ν m) h =
      population allocation m h * denominator ν := by
  simp only [population, AllFieldPopulationCounts.count, dilation]
  ac_rfl

theorem populationLength_dilation (allocation : Allocation) (ν : ∀ h, A h → ℚ)
    (m : ℕ) :
    populationLength (K := K) allocation (dilation ν m) =
      populationLength (K := K) allocation m * denominator ν := by
  simp only [populationLength, AllFieldPopulationCounts.blockLength, dilation]
  ac_rfl

theorem sum_count (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (htotal : ∀ h, ∑ a, ν h a = 1) (m : ℕ) (h : H) :
    (∑ a, count allocation history ν m h a) =
      population allocation (dilation ν m) (history h) := by
  simp only [count, ← Finset.mul_sum, sum_baseCount ν hν htotal,
    population_dilation]

theorem count_cast (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (m : ℕ) (h : H) (a : A h) :
    (count allocation history ν m h a : ℚ) =
      (populationLength (K := K) allocation (dilation ν m) : ℚ) *
        amount allocation (history h) * ν h a := by
  rw [count, Nat.cast_mul, population_cast, baseCount_cast ν hν,
    populationLength_dilation, Nat.cast_mul]
  ring

theorem count_dilate (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (m n : ℕ) (h : H) (a : A h) :
    count allocation history ν (m * n) h a =
      m * count allocation history ν n h a := by
  simp only [count, population, AllFieldPopulationCounts.count]
  ac_rfl

theorem count_mul_one (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (m : ℕ) (h : H) (a : A h) :
    count allocation history ν m h a = m * count allocation history ν 1 h a := by
  simpa only [Nat.mul_one] using count_dilate allocation history ν m 1 h a

theorem source_population_pos (allocation : Allocation) (ν : ∀ h, A h → ℚ)
    {m : ℕ} (hm : 0 < m) (h : History K) (hh : 0 < amount allocation h) :
    0 < population allocation (dilation ν m) h :=
  (AllFieldPopulationCounts.count_pos_iff (amount allocation)
    (amount_nonneg allocation) (dilation_pos ν hm) h).2 hh

theorem sum_count_pos (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (htotal : ∀ h, ∑ a, ν h a = 1) {m : ℕ} (hm : 0 < m)
    (h : H) (hh : 0 < amount allocation (history h)) :
    0 < ∑ a, count allocation history ν m h a := by
  rw [sum_count allocation history ν hν htotal]
  exact source_population_pos allocation ν hm (history h) hh

theorem count_ratio (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (htotal : ∀ h, ∑ a, ν h a = 1) {m : ℕ} (hm : 0 < m)
    (h : H) (hh : 0 < amount allocation (history h)) (a : A h) :
    (count allocation history ν m h a : ℚ) /
      (∑ b, count allocation history ν m h b : ℕ) = ν h a := by
  rw [sum_count allocation history ν hν htotal, count_cast allocation history ν hν,
    population_cast]
  have hp : (populationLength (K := K) allocation (dilation ν m) : ℚ) *
      amount allocation (history h) ≠ 0 := by
    rw [← population_cast]
    exact_mod_cast (Nat.ne_of_gt (source_population_pos allocation ν hm (history h) hh))
  exact mul_div_cancel_left₀ _ hp

theorem count_ratio_real (allocation : Allocation) (history : H → History K)
    (ν : ∀ h, A h → ℚ) (hν : ∀ h a, 0 ≤ ν h a)
    (htotal : ∀ h, ∑ a, ν h a = 1) {m : ℕ} (hm : 0 < m)
    (h : H) (hh : 0 < amount allocation (history h)) (a : A h) :
    (count allocation history ν m h a : ℝ) /
      (∑ b, count allocation history ν m h b : ℕ) = (ν h a : ℝ) := by
  have hq := congrArg (fun q : ℚ => (q : ℝ))
    (count_ratio allocation history ν hν htotal hm h hh a)
  simpa only [Rat.cast_div, Rat.cast_natCast] using hq

end MatrixMultiplication.AllFieldTerminalPopulations

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_TerminalRates
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.half_unhalfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.unhalf_halfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.fourStatistic_append _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldTerminalRates

open AllFieldHistory AllFieldParameters AllFieldTerminalStatisticLaws
open AllFieldZeroLeafRates Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

variable {K : ℕ}

def statisticCounts (allocation : Allocation) (h : TerminalZero K) : Slot h → ℕ :=
  AllFieldTerminalPopulations.count allocation history law 1 h

def terminalDilation (K : ℕ) (m : ℕ) : ℕ :=
  AllFieldTerminalPopulations.dilation (law (K := K)) m

def terminalLength (allocation : Allocation) (K : ℕ) (m : ℕ) : ℕ :=
  populationLength (K := K) allocation (terminalDilation K m)

theorem statisticCounts_pos (allocation : Allocation) (h : TerminalZero K) :
    0 < ∑ s, statisticCounts allocation h s :=
  AllFieldTerminalPopulations.sum_count_pos allocation history law law_nonneg law_total
    (by decide) h (history_amount_pos allocation h)

theorem statisticCounts_ratio (allocation : Allocation) (h : TerminalZero K) (s : Slot h) :
    (statisticCounts allocation h s : ℝ) /
      (∑ s, statisticCounts allocation h s : ℕ) = (law h s : ℝ) :=
  AllFieldTerminalPopulations.count_ratio_real allocation history law law_nonneg law_total
    (by decide) h (history_amount_pos allocation h) s

theorem statisticCounts_sum_inl (allocation : Allocation) (h : AZero K) :
    (∑ s : Slot (.inl h), statisticCounts allocation (.inl h) s) =
      ∑ s : PairSlot, statisticCounts allocation (.inl h) s := by
  exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)

theorem statisticCounts_sum_inr (allocation : Allocation) (h : BZero K) :
    (∑ s : Slot (.inr h), statisticCounts allocation (.inr h) s) =
      ∑ s : Fin 6, statisticCounts allocation (.inr h) s := by
  exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)

theorem statisticCounts_repeat (allocation : Allocation) (m : ℕ)
    (h : TerminalZero K) (s : Slot h) :
    m * statisticCounts allocation h s =
      AllFieldTerminalPopulations.count allocation history law m h s :=
  (AllFieldTerminalPopulations.count_mul_one allocation history law m h s).symm

theorem statisticCounts_repeat_sum (allocation : Allocation) (m : ℕ)
    (h : TerminalZero K) :
    (∑ s, m * statisticCounts allocation h s) =
      population allocation (terminalDilation K m) (history h) := by
  simp only [statisticCounts_repeat]
  exact AllFieldTerminalPopulations.sum_count allocation history law law_nonneg law_total m h

def ZeroWords (allocation : Allocation) (m : ℕ) : TerminalZero K → Type
  | .inl h => fourWords (aShape h.1.val) (statisticCounts allocation (.inl h)) m
  | .inr h => twoWords (bWeight h) (statisticCounts allocation (.inr h)) m

local instance terminalTwoWordsFintype (allocation : Allocation) (m : ℕ) (h : BZero K) :
    Fintype (twoWords (bWeight h) (statisticCounts allocation (.inr h)) m) :=
  twoWordsFintype _ _ _

instance zeroWordsFintype (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :
    Fintype (ZeroWords allocation m h) := by
  cases h <;> dsimp [ZeroWords] <;> infer_instance

theorem zeroWords_card_inl (allocation : Allocation) (m : ℕ) (h : AZero K) :
    Fintype.card (ZeroWords allocation m (.inl h)) =
      Fintype.card (fourWords (aShape h.1.val) (statisticCounts allocation (.inl h)) m) := by
  exact Fintype.card_congr (Equiv.refl _)

theorem zeroWords_card_inr (allocation : Allocation) (m : ℕ) (h : BZero K) :
    Fintype.card (ZeroWords allocation m (.inr h)) =
      Fintype.card (twoWords (bWeight h) (statisticCounts allocation (.inr h)) m) := by
  exact Fintype.card_congr (Equiv.refl _)

theorem zeroWords_card_pos (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :
    0 < Fintype.card (ZeroWords allocation m h) := by
  cases h with
  | inl h =>
      rw [zeroWords_card_inl]
      exact four_card_pos (aShape h.1.val) (statisticCounts allocation (.inl h))
        (by simpa only [statisticCounts_sum_inl] using statisticCounts_pos allocation (.inl h))
        (by
          intro slot
          simpa only [statisticCounts_sum_inl, law_inl] using
            statisticCounts_ratio allocation (.inl h) slot) m
  | inr h =>
      rw [zeroWords_card_inr]
      exact two_card_pos (binaryParameter (bParent h) (bShape h.1.val))
        (bWeight h) (statisticCounts allocation (.inr h))
        (by simpa only [statisticCounts_sum_inr] using statisticCounts_pos allocation (.inr h))
        (by
          intro slot
          simpa only [statisticCounts_sum_inr, law_inr] using
            statisticCounts_ratio allocation (.inr h) slot) m

def zeroVolume (allocation : Allocation) (m : ℕ) : ℕ :=
  Fintype.card (∀ h : TerminalZero K, ZeroWords allocation m h)

theorem zeroVolume_pos (allocation : Allocation) (m : ℕ) :
    0 < zeroVolume (K := K) allocation m := by
  simp only [zeroVolume, Fintype.card_pi]
  exact Finset.prod_pos fun h _ => zeroWords_card_pos allocation m h

def terminalVolume (allocation : Allocation) (m : ℕ) : ℕ :=
  AllFieldInitialLeafRates.volume (K := K) allocation (terminalDilation K m) *
    zeroVolume (K := K) allocation m *
      CWStageCProducts.populationVolume (K := K) allocation (terminalDilation K m)

theorem stageCVolume_pos (allocation : Allocation) (dilation : ℕ) :
    0 < CWStageCProducts.populationVolume (K := K) allocation dilation := by
  unfold CWStageCProducts.populationVolume
  rw [CWStageCProducts.historyVolume_eq_prod]
  exact Finset.prod_pos fun h _ => CWStageCProducts.volume_pos _ _

theorem terminalVolume_pos (allocation : Allocation) (m : ℕ) :
    0 < terminalVolume (K := K) allocation m := by
  exact Nat.mul_pos
    (Nat.mul_pos (AllFieldInitialLeafRates.volume_pos allocation _)
      (zeroVolume_pos allocation m)) (stageCVolume_pos allocation _)

end MatrixMultiplication.AllFieldTerminalRates

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWZeroGeometry
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.CWOrientedZero
open MatrixMultiplication.Foundation CWWindowedLeaves CWStrands AllFieldFiniteFamily
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable (F : Type*) [Field F]

theorem tensor_swapXY_inline_MatrixMultiplication_CWOrientedZero (x y z : Fin 7) :
    FieldCW.tensor F 5 x y z = FieldCW.tensor F 5 y x z := by
  unfold FieldCW.tensor
  simp only [Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc]
  ring

theorem tensor_swapYZ_inline_MatrixMultiplication_CWOrientedZero (x y z : Fin 7) :
    FieldCW.tensor F 5 x y z = FieldCW.tensor F 5 x z y := by
  exact (FieldCW.tensor_cyclic F 5 x y z).trans
    ((tensor_swapXY_inline_MatrixMultiplication_CWOrientedZero F y z x).trans (FieldCW.tensor_cyclic F 5 x z y).symm)

theorem shape_swapXY (n a b c : ℕ) (x y z : Raw n) :
    shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (b) (Matrix.vecCons (c) Matrix.vecEmpty))) x y z =
      shapeTensor (F := F) (Fin n) (Matrix.vecCons (b) (Matrix.vecCons (a) (Matrix.vecCons (c) Matrix.vecEmpty))) y x z := by
  have hp : strand (F := F) (Fin n) x y z = strand (F := F) (Fin n) y x z := by
    apply Finset.prod_congr rfl
    intro i _
    exact tensor_swapXY_inline_MatrixMultiplication_CWOrientedZero F _ _ _
  simp only [shapeTensor, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, hp]
  congr 1
  apply propext
  tauto

theorem shape_swapYZ (n a b c : ℕ) (x y z : Raw n) :
    shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (b) (Matrix.vecCons (c) Matrix.vecEmpty))) x y z =
      shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (c) (Matrix.vecCons (b) Matrix.vecEmpty))) x z y := by
  have hp : strand (F := F) (Fin n) x y z = strand (F := F) (Fin n) x z y := by
    apply Finset.prod_congr rfl
    intro i _
    exact tensor_swapYZ_inline_MatrixMultiplication_CWOrientedZero F _ _ _
  simp only [shapeTensor, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, hp]
  congr 1
  apply propext
  tauto

theorem shape_swapXZ (n a b c : ℕ) (x y z : Raw n) :
    shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (b) (Matrix.vecCons (c) Matrix.vecEmpty))) x y z =
      shapeTensor (F := F) (Fin n) (Matrix.vecCons (c) (Matrix.vecCons (b) (Matrix.vecCons (a) Matrix.vecEmpty))) z y x := by
  rw [shape_swapXY, shape_swapYZ, shape_swapXY]

def sideWord (zero selected : Fin 3) {n a : ℕ} (side : Fin 3)
    (w : Alphabet n a) : Raw n :=
  if side = zero then zeroWord n else if side = selected then w.val else complementWord w.val

theorem local_coefficient (n a b : ℕ) (hab : a + b = 2*n)
    (zero selected : Fin 3) (hne : zero ≠ selected) (x y z : Alphabet n a) :
    shapeTensor (F := F) (Fin n) (placedShape zero selected a b)
      (sideWord zero selected 0 x) (sideWord zero selected 1 y)
      (sideWord zero selected 2 z) = if matched zero x y z then 1 else 0 := by
  have shape_eq : placedShape zero selected a b =
      ![placedShape zero selected a b 0, placedShape zero selected a b 1,
        placedShape zero selected a b 2] := by
    ext side
    fin_cases side <;> rfl
  rw [shape_eq]
  fin_cases zero <;> fin_cases selected
  all_goals try contradiction
  · simpa [placedShape, sideWord, matched] using zeroX_local F n a b hab y z
  · have hh := (shape_swapYZ F n 0 b a (zeroWord n) (complementWord y.val) z.val).trans
        (zeroX_local F n a b hab z y)
    have he : (z = y) ↔ (y = z) := eq_comm
    simpa [placedShape, sideWord, matched, he] using hh
  · simpa [placedShape, sideWord, matched] using zeroY_local F n a b hab x z
  · have hh := (shape_swapXZ F n b 0 a (complementWord x.val) (zeroWord n) z.val).trans
        (zeroY_local F n a b hab z x)
    have he : (z = x) ↔ (x = z) := eq_comm
    simpa [placedShape, sideWord, matched, he] using hh
  · simpa [placedShape, sideWord, matched] using zeroZ_local F n a b hab x y
  · have hh := (shape_swapXY F n b a 0 (complementWord x.val) y.val (zeroWord n)).trans
        (zeroZ_local F n a b hab y x)
    have he : (y = x) ↔ (x = y) := eq_comm
    simpa [placedShape, sideWord, matched, he] using hh

theorem matching_nonempty {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
    (Q : Tensor F V V V) (zero : Fin 3) (embed : Fin 3 → E → V)
    (h : ∀ x y z, Q (embed 0 x) (embed 1 y) (embed 2 z) =
      if matched zero x y z then 1 else 0) :
    Nonempty (LocalMap Q (Tensor.matrixCoefficients (Row zero E) (Middle zero E) (Column zero E))) := by
  let e : E := Classical.choice inferInstance
  fin_cases zero
  · refine ⟨LocalMap.ofExists ⟨(fun _ v => if v = embed 0 e then 1 else 0),
      (fun y v => if v = embed 1 y.2 then 1 else 0),
      (fun z v => if v = embed 2 z.1 then 1 else 0), ?_⟩⟩
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    let sm0 : Subsingleton (Middle (0 : Fin 3) E) := by simp only [Middle, show (0 : Fin 3) ≠ 2 from by decide, ite_false, if_false]; infer_instance
    let sr0 : Subsingleton (Row (0 : Fin 3) E) := by simp only [Row, show (0 : Fin 3) ≠ 1 from by decide, ite_false, if_false]; infer_instance
    have hu1 : x.2 = y.1 := @Subsingleton.elim _ sm0 _ _
    have hu2 : z.2 = x.1 := @Subsingleton.elim _ sr0 _ _
    simpa [Tensor.pullback, Tensor.matrixCoefficients, matched, Row, Middle, Column, hu1, hu2] using
      h e y.2 z.1
  · refine ⟨LocalMap.ofExists ⟨(fun x v => if v = embed 0 x.1 then 1 else 0),
      (fun _ v => if v = embed 1 e then 1 else 0),
      (fun z v => if v = embed 2 z.2 then 1 else 0), ?_⟩⟩
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    let sm1 : Subsingleton (Middle (1 : Fin 3) E) := by simp only [Middle, show (1 : Fin 3) ≠ 2 from by decide, ite_false, if_false]; infer_instance
    let sc1 : Subsingleton (Column (1 : Fin 3) E) := by simp only [Column, show (1 : Fin 3) ≠ 0 from by decide, ite_false, if_false]; infer_instance
    have hu1 : x.2 = y.1 := @Subsingleton.elim _ sm1 _ _
    have hu2 : y.2 = z.1 := @Subsingleton.elim _ sc1 _ _
    simpa [Tensor.pullback, Tensor.matrixCoefficients, matched, Row, Middle, Column, hu1, hu2, eq_comm] using
      h x.1 e z.2
  · refine ⟨LocalMap.ofExists ⟨(fun x v => if v = embed 0 x.2 then 1 else 0),
      (fun y v => if v = embed 1 y.1 then 1 else 0),
      (fun _ v => if v = embed 2 e then 1 else 0), ?_⟩⟩
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    let sc2 : Subsingleton (Column (2 : Fin 3) E) := by simp only [Column, show (2 : Fin 3) ≠ 0 from by decide, ite_false, if_false]; infer_instance
    let sr2 : Subsingleton (Row (2 : Fin 3) E) := by simp only [Row, show (2 : Fin 3) ≠ 1 from by decide, ite_false, if_false]; infer_instance
    have hu1 : y.2 = z.1 := @Subsingleton.elim _ sc2 _ _
    have hu2 : z.2 = x.1 := @Subsingleton.elim _ sr2 _ _
    simpa [Tensor.pullback, Tensor.matrixCoefficients, matched, Row, Middle, Column, hu1, hu2] using
      h x.2 y.1 e

def ofMatching {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
    (Q : Tensor F V V V) (zero : Fin 3) (embed : Fin 3 → E → V)
    (h : ∀ x y z, Q (embed 0 x) (embed 1 y) (embed 2 z) =
      if matched zero x y z then 1 else 0) :
    LocalMap Q (Tensor.matrixCoefficients (Row zero E) (Middle zero E) (Column zero E)) :=
  Classical.choice (matching_nonempty F Q zero embed h)

theorem power_coefficient {E : Type} (n a b m : ℕ) (hab : a+b=2*n)
    (zero selected : Fin 3) (hne : zero ≠ selected)
    (words : E → Fin m → Alphabet n a) (hinj : Function.Injective words)
    (x y z : E) :
    Tensor.power (shapeTensor (F := F) (Fin n) (placedShape zero selected a b)) m
      (fun i => sideWord zero selected 0 (words x i))
      (fun i => sideWord zero selected 1 (words y i))
      (fun i => sideWord zero selected 2 (words z i)) =
      if matched zero x y z then 1 else 0 := by
  simp only [Tensor.power, local_coefficient F n a b hab zero selected hne]
  fin_cases zero <;> simp [matched, Fintype.prod_boole, ← funext_iff, hinj.eq_iff]

end MatrixMultiplication.CWOrientedZero

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.CWZeroGeometry

open AllFieldParameters AllFieldHistory CWOrientedZero

def zeroAxis (g : Shape) : Fin 3 :=
  if g 0 = 0 then 0 else if g 1 = 0 then 1 else 2

def maxAxis (g : Shape) : Fin 3 :=
  if g 0 = shapeMax g then 0 else if g 1 = shapeMax g then 1 else 2

theorem zeroAxis_spec (g : Shape) (hz : ∃ i, g i = 0) : g (zeroAxis g) = 0 := by
  unfold zeroAxis
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · obtain ⟨i, hi⟩ := hz
    fin_cases i <;> simp_all

theorem maxAxis_spec (g : Shape) : g (maxAxis g) = shapeMax g := by
  have hm : shapeMax g = g 0 ∨ shapeMax g = g 1 ∨ shapeMax g = g 2 := by
    unfold shapeMax
    rcases le_total (g 0) (max (g 1) (g 2)) with h | h
    · rw [max_eq_right h]
      rcases le_total (g 1) (g 2) with h | h
      · exact Or.inr (Or.inr (max_eq_right h))
      · exact Or.inr (Or.inl (max_eq_left h))
    · exact Or.inl (max_eq_left h)
  unfold maxAxis
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · rcases hm with hm | hm | hm
    · exact (h0 hm.symm).elim
    · exact (h1 hm.symm).elim
    · exact hm.symm

theorem shapeMax_le_total (g : Shape) : shapeMax g ≤ shapeTotal g := by
  exact max_le (coordinate_le_total g 0)
    (max_le (coordinate_le_total g 1) (coordinate_le_total g 2))

theorem shapeMax_pos (g : Shape) (ht : 0 < shapeTotal g) : 0 < shapeMax g := by
  have h0 : g 0 ≤ shapeMax g := le_max_left _ _
  have h1 : g 1 ≤ shapeMax g := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : g 2 ≤ shapeMax g := (le_max_right _ _).trans (le_max_right _ _)
  unfold shapeTotal at ht
  omega

theorem zero_ne_selected (g : Shape) (zero selected : Fin 3)
    (ht : 0 < shapeTotal g) (hz : g zero = 0) (hs : g selected = shapeMax g) :
    zero ≠ selected := by
  intro he
  have hp := shapeMax_pos g ht
  rw [← he, hz] at hs
  omega

theorem max_add_complement (g : Shape) :
    shapeMax g + (shapeTotal g - shapeMax g) = shapeTotal g :=
  Nat.add_sub_of_le (shapeMax_le_total g)

theorem eq_placedShape (g : Shape) (zero selected : Fin 3)
    (hz : g zero = 0) (hs : g selected = shapeMax g) (hne : zero ≠ selected) :
    g = placedShape zero selected (shapeMax g) (shapeTotal g - shapeMax g) := by
  funext side
  fin_cases zero <;> fin_cases selected
  all_goals try contradiction
  all_goals fin_cases side <;>
    simp_all [placedShape, shapeTotal]

theorem physicalShape_eq_placedShape (g : Shape) (phi : Equiv.Perm (Fin 3))
    (zero selected : Fin 3) (hz : g zero = 0)
    (hs : g selected = shapeMax g) (hne : zero ≠ selected) :
    physicalShape phi g = placedShape (phi zero) (phi selected)
      (shapeMax g) (shapeTotal g - shapeMax g) := by
  funext side
  calc
    physicalShape phi g side =
        placedShape zero selected (shapeMax g) (shapeTotal g - shapeMax g)
          (phi.symm side) := congrFun (eq_placedShape g zero selected hz hs hne) _
    _ = _ := by simp only [placedShape, Equiv.symm_apply_eq]

theorem selected_add_remaining (g : Shape) (zero selected side : Fin 3)
    (hz : g zero = 0) (hs : g selected = shapeMax g) (hne : zero ≠ selected)
    (hzs : side ≠ zero) (hss : side ≠ selected) :
    g selected + g side = shapeTotal g := by
  have hside : g side = shapeTotal g - shapeMax g := by
    rw [congrFun (eq_placedShape g zero selected hz hs hne) side]
    simp only [placedShape, ite_eq_right hzs, ite_eq_right hss]
  rw [hs, hside]
  exact max_add_complement g

end MatrixMultiplication.CWZeroGeometry

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_ZeroFinish
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldPairMarginals.halfWeightCode_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.AllFieldZeroWords
open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldTerminalStatisticLaws AllFieldTerminalRates CWWindowedLeaves
open CWCompleteStatistics InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K : ℕ}

def length (h : TerminalZero K) : ℕ := currentLength (history h).1
def shape (h : TerminalZero K) : Shape := currentShape (history h).1

def statistic : (h : TerminalZero K) → Raw (length h) → Slot h
  | .inl _, w => fourStatistic w
  | .inr _, w => twoStatistic w

def complement : (h : TerminalZero K) → Slot h ≃ Slot h
  | .inl _ => orderedComplementStatistic
  | .inr _ => complementStatistic

theorem statistic_complement (h : TerminalZero K) (w : Raw (length h)) :
    statistic h (complementWord w) = complement h (statistic h w) := by
  cases h with
  | inl h => exact four_complement w
  | inr h => exact two_complement w

def words (allocation : Allocation) (m : ℕ) (h : TerminalZero K)
    (w : ZeroWords allocation m h) :
    Fin (population allocation (terminalDilation K m) (history h)) →
      Alphabet (length h) (shapeMax (shape h)) := by
  cases h with
  | inl h =>
      exact fun i => w.val ((finCongr (statisticCounts_repeat_sum allocation m (.inl h))).symm i)
  | inr h =>
      exact fun i => w.val ((finCongr (statisticCounts_repeat_sum allocation m (.inr h))).symm i)

theorem words_injective (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :
    Function.Injective (words allocation m h) := by
  cases h with
  | inl h =>
      intro x y he
      apply Subtype.ext
      exact (finCongr (statisticCounts_repeat_sum allocation m (.inl h))).symm.surjective.injective_comp_right he
  | inr h =>
      intro x y he
      apply Subtype.ext
      exact (finCongr (statisticCounts_repeat_sum allocation m (.inr h))).symm.surjective.injective_comp_right he

theorem repeat_ratio (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (h : TerminalZero K) (s : Slot h) :
    ((m * statisticCounts allocation h s : ℕ) : ℝ) /
      (∑ s, m * statisticCounts allocation h s : ℕ) = (law h s : ℝ) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp only [← Finset.mul_sum, Nat.cast_mul, mul_div_mul_left _ _ hm']
  exact statisticCounts_ratio allocation h s

theorem exact_window_reindex {Slots Letters : Type*}
    [Fintype Slots] [DecidableEq Slots] (stat : Letters → Slots) (counts : Slots → ℕ)
    (word : ExactStatisticWords.Words stat counts) (ν : Slots → ℝ) (η : ℝ)
    (hη : 0 ≤ η) (hratio : ∀ slot, (counts slot : ℝ) / (∑ slot, counts slot : ℕ) = ν slot)
    {positions : ℕ} (reindex : Fin positions ≃ Fin (∑ slot, counts slot)) :
    typeWindow ν η ((stat ∘ word.val) ∘ reindex) := by
  intro slot
  simp only [empiricalLaw, wordPopulation_reindex, word.property,
    Fintype.card_congr reindex, Fintype.card_fin, hratio slot, sub_self, abs_zero]
  exact hη

theorem selected_window (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (h : TerminalZero K) (η : ℝ) (hη : 0 ≤ η) (w : ZeroWords allocation m h) :
    typeWindow (fun s => (law h s : ℝ)) η
      (fun i => statistic h (words allocation m h w i).val) := by
  cases h with
  | inl h =>
      change AllFieldZeroLeafRates.fourWords (aShape h.1.val)
        (statisticCounts allocation (.inl h)) m at w
      intro s
      change PairSlot at s
      have hsum := statisticCounts_repeat_sum allocation m (.inl h)
      let reindex : Fin (population allocation (terminalDilation K m) (history (.inl h))) ≃
          Fin (∑ slot : PairSlot, m * statisticCounts allocation (.inl h) slot) :=
        (finCongr hsum).symm
      have hwindow := exact_window_reindex _ _ w
        (fun slot : PairSlot => (law (.inl h) slot : ℝ)) η hη
        (fun slot => repeat_ratio allocation hm (.inl h) slot) reindex s
      let : DecidableEq PairSlot := fun _ _ => Classical.propDecidable _
      change |empiricalLaw ((fun index => fourStatistic (w.val index).val) ∘ reindex) s -
        (law (.inl h) s : ℝ)| ≤ η
      simpa only [empiricalLaw, wordPopulation, Fintype.card_eq_nat_card,
        Function.comp_def] using hwindow
  | inr h =>
      change AllFieldZeroLeafRates.twoWords (bWeight h)
        (statisticCounts allocation (.inr h)) m at w
      intro s
      change Fin 6 at s
      have hsum := statisticCounts_repeat_sum allocation m (.inr h)
      let reindex : Fin (population allocation (terminalDilation K m) (history (.inr h))) ≃
          Fin (∑ slot : Fin 6, m * statisticCounts allocation (.inr h) slot) :=
        (finCongr hsum).symm
      have hwindow := exact_window_reindex _ _ w
        (fun slot : Fin 6 => (law (.inr h) slot : ℝ)) η hη
        (fun slot => repeat_ratio allocation hm (.inr h) slot) reindex s
      let : DecidableEq (Fin 6) := fun _ _ => Classical.propDecidable _
      change |empiricalLaw ((fun index => twoStatistic (w.val index).val) ∘ reindex) s -
        (law (.inr h) s : ℝ)| ≤ η
      simpa only [empiricalLaw, wordPopulation, Fintype.card_eq_nat_card,
        Function.comp_def] using hwindow

theorem complementary_window (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (h : TerminalZero K) (η : ℝ) (hη : 0 ≤ η) (w : ZeroWords allocation m h) :
    typeWindow ((fun s => (law h s : ℝ)) ∘ (complement h).symm) η
      (fun i => statistic h (complementWord (words allocation m h w i).val)) := by
  have hs := selected_window allocation hm h η hη w
  have he : (fun i => statistic h (complementWord (words allocation m h w i).val)) =
      complement h ∘ (fun i => statistic h (words allocation m h w i).val) := by
    funext i
    exact statistic_complement h _
  rw [he]
  exact (typeWindow_equiv _ η _ (complement h)).mpr hs

end MatrixMultiplication.AllFieldZeroWords

namespace MatrixMultiplication.AllFieldZeroFinish
open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldTerminalStatisticLaws AllFieldTerminalRates AllFieldZeroWords
open CWWindowedLeaves CWCompleteStatistics CWZeroGeometry CWOrientedZero
open AllFieldFiniteFamily InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K : ℕ}

def canonicalZero (h : TerminalZero K) : Fin 3 := zeroAxis (shape h)
def canonicalSelected : TerminalZero K → Fin 3
  | .inl h => halfMaxAxis (aShape h.1.val)
  | .inr h => maxAxis (bShape h.1.val)
def physicalZero (h : TerminalZero K) : Fin 3 := (history h).2 (canonicalZero h)
def physicalSelected (h : TerminalZero K) : Fin 3 := (history h).2 (canonicalSelected h)

theorem shape_has_zero (h : TerminalZero K) : ∃ s, shape h s = 0 := by
  cases h with
  | inl h => exact not_positive_has_zero _ (aShape_not_positive h)
  | inr h => exact not_positive_has_zero _ h.1.property

theorem canonicalZero_spec (h : TerminalZero K) : shape h (canonicalZero h) = 0 :=
  zeroAxis_spec (shape h) (shape_has_zero h)

theorem canonicalSelected_spec (h : TerminalZero K) :
    shape h (canonicalSelected h) = shapeMax (shape h) := by
  cases h with
  | inl h => exact halfMaxAxis_spec _ (aShape_mem_shapes h)
  | inr h => exact maxAxis_spec _

theorem shape_total (h : TerminalZero K) : shapeTotal (shape h) = 2 * length h :=
  (currentShape_spec (history h).1).2

theorem shape_total_pos (h : TerminalZero K) : 0 < shapeTotal (shape h) := by
  rw [shape_total]
  cases h <;> norm_num [length, history, currentLength]

theorem axes_distinct (h : TerminalZero K) : canonicalZero h ≠ canonicalSelected h :=
  zero_ne_selected (shape h) _ _ (shape_total_pos h)
    (canonicalZero_spec h) (canonicalSelected_spec h)

theorem physical_axes_distinct (h : TerminalZero K) : physicalZero h ≠ physicalSelected h :=
  (history h).2.injective.ne (axes_distinct h)

theorem physical_shape (h : TerminalZero K) :
    currentPhysicalShape (history h) = placedShape (physicalZero h) (physicalSelected h)
      (shapeMax (shape h)) (shapeTotal (shape h) - shapeMax (shape h)) :=
  physicalShape_eq_placedShape (shape h) (history h).2 _ _
    (canonicalZero_spec h) (canonicalSelected_spec h) (axes_distinct h)

def nativeLaw : (h : TerminalZero K) → Fin 3 → Slot h → ℚ
  | .inl h, side => halfLaw (aShape h.1.val) side
  | .inr h, side => littleLaw (bParent h) (bShape h.1.val) side

theorem selected_law (h : TerminalZero K) (s : Slot h) :
    nativeLaw h (canonicalSelected h) s = law h s := by
  cases h with
  | inl h => exact halfLaw_at_maximum _ (aShape_mem_zeroSecond h) s
  | inr h =>
      change Fin 6 at s
      change littleLaw (bParent h) (bShape h.1.val) (maxAxis (bShape h.1.val)) s = _
      rw [littleLaw_eq_statisticLaw _ _ _ (child_statistic_weight_bounded _
        (bParent_mem_positiveSecond h) _ (bShape_mem_below h) _)]
      congr 1
      apply Fin.ext
      exact maxAxis_spec _

theorem zero_law (h : TerminalZero K) (s : Slot h) :
    nativeLaw h (canonicalZero h) s =
      if statistic h (zeroWord (length h)) = s then 1 else 0 := by
  have hz := canonicalZero_spec h
  cases h with
  | inl h =>
      change PairSlot at s
      let : DecidableEq PairSlot := fun _ _ => Classical.propDecidable _
      change halfLaw (aShape h.1.val) (canonicalZero (.inl h)) s =
        if ((0, 0) : PairSlot) = s then 1 else 0
      rw [halfLaw_weight_zero _ (aShape_mem_shapes h) _ hz s]
      by_cases hs : s = (0,0)
      · rw [ite_eq_left hs, ite_eq_left hs.symm]
      · rw [ite_eq_right hs, ite_eq_right (Ne.symm hs)]
  | inr h =>
      change Fin 6 at s
      let : DecidableEq (Fin 6) := fun _ _ => Classical.propDecidable _
      change bShape h.1.val (canonicalZero (.inr h)) = 0 at hz
      change littleLaw (bParent h) (bShape h.1.val) (canonicalZero (.inr h)) s =
        if (0 : Fin 6) = s then 1 else 0
      simp only [littleLaw, hz, show (0 : ℕ) ≠ 2 from by decide, ite_false, if_false, singletonSlot]
      by_cases hs : s = 0
      · simp [hs]
      · simp [hs, Ne.symm hs]

theorem remaining_law (h : TerminalZero K) (side : Fin 3)
    (hz : side ≠ canonicalZero h) (hs : side ≠ canonicalSelected h) (s : Slot h) :
    nativeLaw h side s = law h ((AllFieldZeroWords.complement h).symm s) := by
  have hsum := selected_add_remaining (shape h) (canonicalZero h) (canonicalSelected h) side
    (canonicalZero_spec h) (canonicalSelected_spec h) (axes_distinct h) hz hs
  have he : nativeLaw h (canonicalSelected h) ((AllFieldZeroWords.complement h).symm s) =
      nativeLaw h side s := by
    cases h with
    | inl h =>
        exact halfLaw_complementary_sides _ (aShape_mem_shapes h) _ _ (Ne.symm hs)
          (hsum.trans (shape_total (.inl h))) s
    | inr h =>
        exact littleLaw_complement _ _ _ _
          (child_statistic_weight_bounded _ (bParent_mem_positiveSecond h) _ (bShape_mem_below h) _)
          (child_statistic_weight_bounded _ (bParent_mem_positiveSecond h) _ (bShape_mem_below h) _)
          (hsum.trans (shape_total (.inr h))) s
  rw [selected_law] at he
  exact he.symm

def embed (allocation : Allocation) (m : ℕ) (h : TerminalZero K)
    (side : Fin 3) (w : ZeroWords allocation m h) :
    HistoryWord allocation (terminalDilation K m) (history h) :=
  fun i => sideWord (physicalZero h) (physicalSelected h) side (words allocation m h w i)

theorem embed_window (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (h : TerminalZero K) (side : Fin 3) (η : ℝ) (hη : 0 ≤ η)
    (w : ZeroWords allocation m h) :
    typeWindow (fun s => (nativeLaw h ((history h).2.symm side) s : ℝ)) η
      (fun i => statistic h (embed allocation m h side w i)) := by
  by_cases hz : side = physicalZero h
  · have hc : (history h).2.symm side = canonicalZero h := by
      simp only [hz, physicalZero, Equiv.symm_apply_apply]
    simp only [embed, sideWord, ite_eq_left hz, hc]
    have hpop : 0 < population allocation (terminalDilation K m) (history h) := by
      rw [← statisticCounts_repeat_sum allocation m h, ← Finset.mul_sum]
      exact Nat.mul_pos hm (statisticCounts_pos allocation h)
    apply zero_window (length h) _ hpop (statistic h) _ η hη
    intro s
    rw [zero_law]
    split_ifs <;> norm_num
  · by_cases hs : side = physicalSelected h
    · have hc : (history h).2.symm side = canonicalSelected h := by
        simp only [hs, physicalSelected, Equiv.symm_apply_apply]
      simpa only [embed, sideWord, ite_eq_right hz, ite_eq_left hs, hc, selected_law] using
        selected_window allocation hm h η hη w
    · have hcz : (history h).2.symm side ≠ canonicalZero h := by
        intro hh
        apply hz
        exact ((history h).2.apply_symm_apply side).symm.trans (congrArg (history h).2 hh)
      have hcs : (history h).2.symm side ≠ canonicalSelected h := by
        intro hh
        apply hs
        exact ((history h).2.apply_symm_apply side).symm.trans (congrArg (history h).2 hh)
      simp only [embed, sideWord, ite_eq_right hz, ite_eq_right hs, remaining_law h _ hcz hcs]
      exact complementary_window allocation hm h η hη w

theorem embed_mask (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (h : TerminalZero K) (side : Fin 3)
    (w : ZeroWords allocation m h) :
    residentMask allocation (terminalDilation K m) ε (history h) side
      (embed allocation m h side w) := by
  cases h with
  | inl h =>
      intro _
      exact embed_window allocation hm (.inl h) side (ε/8) (by positivity) w
  | inr h =>
      intro _
      exact embed_window allocation hm (.inr h) side (ε/128) (by positivity) w

variable (F : Type*) [Field F]

theorem coefficient (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (h : TerminalZero K) (x y z : ZeroWords allocation m h) :
    historyTensor F allocation (terminalDilation K m) ε (history h)
      (embed allocation m h 0 x) (embed allocation m h 1 y) (embed allocation m h 2 z) =
      if matched (physicalZero h) x y z then 1 else 0 := by
  simp only [historyTensor, ExactRecovery.delete, embed_mask allocation hm hε,
    and_self, ite_true, if_true]
  rw [physical_shape]
  exact power_coefficient F (length h) _ _ _
    ((max_add_complement (shape h)).trans (shape_total h))
    (physicalZero h) (physicalSelected h) (physical_axes_distinct h)
    (words allocation m h) (words_injective allocation m h) x y z

abbrev Row (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :=
  CWOrientedZero.Row (physicalZero h) (ZeroWords allocation m h)
abbrev Middle (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :=
  CWOrientedZero.Middle (physicalZero h) (ZeroWords allocation m h)
abbrev Column (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :=
  CWOrientedZero.Column (physicalZero h) (ZeroWords allocation m h)

def localMap (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (h : TerminalZero K) :
    LocalMap (historyTensor F allocation (terminalDilation K m) ε (history h))
      (Tensor.matrixCoefficients (Row allocation m h) (Middle allocation m h) (Column allocation m h)) := by
  letI : Nonempty (ZeroWords allocation m h) :=
    Fintype.card_pos_iff.mp (zeroWords_card_pos allocation m h)
  exact ofMatching F _ (physicalZero h) (embed allocation m h)
    (coefficient F allocation hm hε h)

theorem volume (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :
    Fintype.card (Row allocation m h) * Fintype.card (Middle allocation m h) *
      Fintype.card (Column allocation m h) = Fintype.card (ZeroWords allocation m h) :=
  CWOrientedZero.volume (physicalZero h) (ZeroWords allocation m h)

end MatrixMultiplication.AllFieldZeroFinish

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_InitialEntropy
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldInitialEntropy

open AllFieldParameters AllFieldHistory MatrixMultiplication.Foundation
open JointPopulationRates JointOrdinaryPopulationSelection
open scoped BigOperators

def nativeInitialMarginal (k : Fin 17) : ℝ :=
  ∑ g : Fin sortedInitial.length,
    (initialLaw (sortedInitial.get g) : ℝ) *
      (∑ w : Fin 3, if sortedInitial.get g w = k.val then 1 else 0) / 3

def nativeH0 : ℝ := homogeneousEntropy nativeInitialMarginal

end MatrixMultiplication.AllFieldInitialEntropy

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_StageCCapacity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.half_unhalfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.unhalf_halfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies
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

theorem allocation_capacity (allocation : Allocation) (d : ℚ) (i : Fin 3) :
    (∑ part : Fin 3, (allocation.mass part : ℝ) *
      (if i = part then binaryEntropyRate d else Real.log 2)) =
      (1 - (allocation.mass i : ℝ)) * Real.log 2 +
        (allocation.mass i : ℝ) * binaryEntropyRate d := by
  have hsum : (∑ part : Fin 3, (allocation.mass part : ℝ)) = 1 := by
    exact_mod_cast allocation.total
  calc
    _ = ∑ part : Fin 3, ((allocation.mass part : ℝ) * Real.log 2 +
        if part = i then (allocation.mass i : ℝ) * (binaryEntropyRate d - Real.log 2) else 0) := by
      apply Finset.sum_congr rfl
      intro part _
      by_cases hp : part = i
      · subst part
        simp only [ite_true, if_true]
        ring
      · simp [hp, Ne.symm hp]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp only [hsum, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
      ring

end MatrixMultiplication.AllFieldStageCCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_ScheduledPositivity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldScheduledYield

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldNativeCapacity
open Filter
open scoped BigOperators Topology

theorem sum_interiorPairs (f : Shape × Shape → ℝ) :
    (interiorPairs.map f).sum =
      (positiveSecond.map fun t =>
        (((below t).filter positive).map fun u => f (t,u)).sum).sum := by
  unfold interiorPairs
  have h : ∀ xs : List Shape,
      ((xs.flatMap fun t => ((below t).filter positive).map fun u => (t,u)).map f).sum =
        (xs.map fun t => (((below t).filter positive).map fun u => f (t,u)).sum).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons t xs ih => simp [ih, List.map_map, Function.comp_def]
  exact h positiveSecond

theorem stageCSourceCapacity_native (allocation : Allocation) :
    stageCSourceCapacity allocation stageCCapacity =
      nativeLC (fun i => (allocation.mass i : ℝ)) := by
  funext i
  unfold stageCSourceCapacity stageCSourceSum nativeLC
  rw [sum_interiorPairs]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  rw [show (∑ part : Fin 3, (allocation.mass part : ℝ) * stageCCapacity t u part i) =
      (1 - (allocation.mass i : ℝ)) * Real.log 2 +
        (allocation.mass i : ℝ) * binaryEntropyRate (binaryParameter t u) from
    AllFieldStageCCapacity.allocation_capacity allocation (binaryParameter t u) i]
  rfl

theorem active_native_capacity (K tick : ℕ) (allocation : Allocation) :
    activeAggregateCapacity allocation tick (workCapacity (K := K)) =
      FiniteSchedule.tickCapacity K nativeLA nativeLB
        (nativeLC (fun i => (allocation.mass i : ℝ))) tick := by
  rw [workCapacity, activeAggregateCapacity_shapeCapacity,
    stageCSourceCapacity_native]
  rfl

theorem physical_order_native_capacity (K tick : ℕ) (allocation : Allocation)
    (sigma : Placement) :
    physicalTickCapacity allocation tick (workCapacity (K := K)) sigma =
      fun i => (1 / 6 : ℝ) * FiniteSchedule.tickCapacity K nativeLA nativeLB
        (nativeLC (fun i => (allocation.mass i : ℝ))) tick i := by
  rw [physicalTickCapacity_eq_sixth, active_native_capacity]

end MatrixMultiplication.AllFieldScheduledYield

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_ConstructionLabels
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldConstructionRates

open MatrixMultiplication.Foundation AllFieldHistory AllFieldScheduledYield
open AllFieldActiveLaws Filter
open scoped BigOperators Topology Classical

variable {K : ℕ}

def denominator (allocation : Allocation) : ℕ := populationLength (K := K) allocation 1

abbrev Slot (K : ℕ) := Unit ⊕ (Fin (K + 2) × Placement)

def capacity (allocation : Allocation) : Slot K → ℝ
  | .inl _ => (K : ℝ) * AllFieldInitialEntropy.nativeH0
  | .inr p => Staggering.minCapacity
      (physicalTickCapacity allocation p.1.val (workCapacity (K := K)) p.2)

def selectionRate (allocation : Allocation) (δ : ℝ) (slot : Slot K) : ℝ :=
  (denominator (K := K) allocation : ℝ) * capacity allocation slot - δ

def initialCount (allocation : Allocation) (δ : ℝ) (m : ℕ) : ℕ :=
  FloorExponentialRates.count (selectionRate (K := K) allocation δ (.inl ())) m

def groupCount (allocation : Allocation) (δ : ℝ) (m : ℕ)
    (tick : Fin (K + 2)) (σ : Placement) : ℕ :=
  FloorExponentialRates.count (selectionRate allocation δ (.inr (tick, σ))) m

theorem groupCount_eq_native (allocation : Allocation) (δ : ℝ) (m : ℕ)
    (tick : Fin (K + 2)) (σ : Placement) :
    groupCount allocation δ m tick σ =
      ⌊Real.exp ((m : ℝ) * ((populationLength (K := K) allocation 1 : ℝ) *
        ((1 / 6 : ℝ) * Staggering.minCapacity (FiniteSchedule.tickCapacity K
          AllFieldNativeCapacity.nativeLA AllFieldNativeCapacity.nativeLB
          (AllFieldNativeCapacity.nativeLC (fun i => (allocation.mass i : ℝ))) tick.val)) - δ))⌋₊ := by
  unfold groupCount FloorExponentialRates.count selectionRate
  simp only [capacity, physical_order_native_capacity,
    PhysicalOrders.minCapacity_mul _ _ (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  rfl

abbrev SelectedLabels (allocation : Allocation) (δ : ℝ) (m : ℕ) :=
  Fin (initialCount (K := K) allocation δ m) ×
    ∀ tick : Fin (K + 2), ∀ σ : Placement, Fin (groupCount allocation δ m tick σ)

theorem card_selected (allocation : Allocation) (δ : ℝ) (m : ℕ) :
    Fintype.card (SelectedLabels (K := K) allocation δ m) =
      initialCount (K := K) allocation δ m *
        ∏ tick : Fin (K + 2), ∏ σ : Placement, groupCount allocation δ m tick σ := by
  simp only [SelectedLabels, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]

end MatrixMultiplication.AllFieldConstructionRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_CWShapePhysicalPermutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Tensor

variable {K X Y : Type*}

def sidePermutation (σ : Equiv.Perm (Fin 3)) (T : Tensor K X X X) :
    Tensor K X X X :=
  fun x y z => T ((Matrix.vecCons (x) (Matrix.vecCons (y) (Matrix.vecCons (z) Matrix.vecEmpty))) (σ.symm 0))
    ((Matrix.vecCons (x) (Matrix.vecCons (y) (Matrix.vecCons (z) Matrix.vecEmpty))) (σ.symm 1)) ((Matrix.vecCons (x) (Matrix.vecCons (y) (Matrix.vecCons (z) Matrix.vecEmpty))) (σ.symm 2))

@[simp] theorem sidePermutation_refl (T : Tensor K X X X) :
    sidePermutation (Equiv.refl _) T = T := by
  rfl

end MatrixMultiplication.Foundation.Tensor

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_Subdivision
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCanonicalization.positionEquiv_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCanonicalization.positionEquiv_symm_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Subdivision

open MatrixMultiplication.Foundation InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Type*) [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]

section Windows

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq I] [∀ index, DecidableEq (P index)] [Fintype A] in
theorem wordPopulation_concatenate (w : ∀ i, P i → A) (a : A) :
    wordPopulation (concatenate P w) a = ∑ i, wordPopulation (w i) a := by
  let e : {p : (Σ i, P i) // concatenate P w p = a} ≃
      (Σ i, {p : P i // w i p = a}) :=
    { toFun := fun p => ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
      invFun := fun p => ⟨⟨p.1, p.2.val⟩, p.2.property⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  exact (Fintype.card_congr e).trans Fintype.card_sigma

omit [DecidableEq I] [∀ index, DecidableEq (P index)] [Fintype A] in
theorem empiricalLaw_concatenate (w : ∀ i, P i → A) (a : A) :
    empiricalLaw (concatenate P w) a =
      ∑ i, ((Fintype.card (P i) : ℝ) / Fintype.card (Σ i, P i)) *
        empiricalLaw (w i) a := by
  rw [empiricalLaw, wordPopulation_concatenate, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Fintype.card (P i) = 0
  · have hp : wordPopulation (w i) a = 0 := by
      have hle := Fintype.card_subtype_le (fun p : P i => w i p = a)
      change wordPopulation (w i) a ≤ Fintype.card (P i) at hle
      omega
    simp [hi, hp]
  · have hi' : (Fintype.card (P i) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hi
    simp only [empiricalLaw, div_eq_mul_inv]
    calc
      (wordPopulation (w i) a : ℝ) * (Fintype.card (Σ i, P i) : ℝ)⁻¹ =
          (wordPopulation (w i) a : ℝ) * (Fintype.card (Σ i, P i) : ℝ)⁻¹ *
            ((Fintype.card (P i) : ℝ) * (Fintype.card (P i) : ℝ)⁻¹) := by
        rw [mul_inv_cancel₀ hi', mul_one]
      _ = (Fintype.card (P i) : ℝ) * (Fintype.card (Σ i, P i) : ℝ)⁻¹ *
          ((wordPopulation (w i) a : ℝ) * (Fintype.card (P i) : ℝ)⁻¹) := by ring

def partWindows (ν : A → ℝ) (η : I → ℝ) (w : ∀ i, P i → A) : Prop :=
  ∀ i, 0 < Fintype.card (P i) → typeWindow ν (η i) (w i)

omit [DecidableEq I] [∀ index, DecidableEq (P index)] [Fintype A] in
theorem typeWindow_concatenate (ν : A → ℝ) (η : ℝ) (ηpart : I → ℝ)
    (hη : 0 ≤ η) (hwidth : ∀ i, ηpart i ≤ η)
    (hsize : 0 < Fintype.card (Σ i, P i)) (w : ∀ i, P i → A)
    (hw : partWindows P ν ηpart w) : typeWindow ν η (concatenate P w) := by
  intro a
  let mass : I → ℝ := fun i => (Fintype.card (P i) : ℝ) / Fintype.card (Σ i, P i)
  let law : I → ℝ := fun i =>
    if Fintype.card (P i) = 0 then ν a else empiricalLaw (w i) a
  have hm : ∀ i, 0 ≤ mass i := fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsum : ∑ i, mass i = 1 := by
    dsimp [mass]
    rw [← Finset.sum_div, ← Nat.cast_sum, ← Fintype.card_sigma]
    exact div_self (by exact_mod_cast (Nat.ne_of_gt hsize))
  have hl : ∀ i, |law i - ν a| ≤ η := by
    intro i
    by_cases hi : Fintype.card (P i) = 0
    · simpa [law, hi] using hη
    · simpa only [law, ite_eq_right hi] using
        (hw i (Nat.pos_of_ne_zero hi) a).trans (hwidth i)
  have heq : empiricalLaw (concatenate P w) a = ∑ i, mass i * law i := by
    rw [empiricalLaw_concatenate]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : Fintype.card (P i) = 0 <;> simp [mass, law, hi]
  rw [heq]
  exact weighted_window mass law (ν a) η hm hsum hl

omit [DecidableEq I] [∀ index, DecidableEq (P index)] [Fintype A] in
theorem statisticWindow_concatenate {X : Type*} (statistic : X → A)
    (ν : A → ℝ) (η : ℝ) (ηpart : I → ℝ)
    (hη : 0 ≤ η) (hwidth : ∀ i, ηpart i ≤ η)
    (hsize : 0 < Fintype.card (Σ i, P i)) (w : ∀ i, P i → X)
    (hw : partWindows P ν ηpart (fun i => statistic ∘ w i)) :
    typeWindow ν η (statistic ∘ concatenate P w) := by
  exact typeWindow_concatenate P ν η ηpart hη hwidth hsize
    (fun index => statistic ∘ w index) hw

end Windows

theorem typeWindow_reindex {A Q R : Type*}
    [Fintype A] [DecidableEq A] [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R]
    (ν : A → ℝ) (η : ℝ) (w : R → A) (e : Q ≃ R) :
    typeWindow ν η (w ∘ e) ↔ typeWindow ν η w := by
  simp only [typeWindow, empiricalLaw, wordPopulation_reindex, Fintype.card_congr e]

end MatrixMultiplication.Subdivision

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_GroupSelectionParameters
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldGroupSelection

open MatrixMultiplication.Foundation AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldScheduledYield AllFieldNativeCapacity
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def nativeDegree (allocation : Allocation) (sigma : Placement) : ℝ :=
  max (orderNativeDegree (K := K) (tick := tick) allocation sigma 0)
    (max (orderNativeDegree (K := K) (tick := tick) allocation sigma 1)
      (orderNativeDegree (K := K) (tick := tick) allocation sigma 2))

def nativeCapacity (allocation : Allocation) : ℝ :=
  (populationLength (K := K) allocation 1 : ℝ) *
    ((1 / 6 : ℝ) * Staggering.minCapacity
      (FiniteSchedule.tickCapacity K nativeLA nativeLB
        (nativeLC (fun i => (allocation.mass i : ℝ))) tick))

def selectionHashRate (allocation : Allocation) (sigma : Placement) (slack : ℝ) : ℝ :=
  nativeDegree (K := K) (tick := tick) allocation sigma + slack / 2

end MatrixMultiplication.AllFieldGroupSelection

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_GroupPairWindows
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupPairWindows

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistorySupport
open AllFieldHistoryChildLaws AllFieldHistoryMasks
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData AllFieldGroupNativeLaws
open JointCompatibilityScaling JointCompatibilityRateLimit
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ} {sigma : Placement}

def weightCode {K : ℕ} (w : Work K) : w.Statistic → Fin 17 :=
  match w with
  | .stageA _ => AllFieldPairMarginals.halfWeightCode
  | .stageB _ => AllFieldPairMarginals.statisticWeightCode
  | .stageC _ => fun _ => 0

@[simp] theorem weightCode_val {K : ℕ} (w : Work K) (a : w.Statistic) :
    (weightCode w a).val = w.statisticWeight a := by
  cases w <;> rfl

end MatrixMultiplication.AllFieldGroupPairWindows

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_GroupSelection
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupSelection

open MatrixMultiplication.Foundation AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldScheduledYield AllFieldNativeCapacity
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

structure Selected (allocation : Allocation) (m : ℕ) (width : ℝ)
    (sigma : Placement) (slack : ℝ) where
  sample : JointCoarseHashing.Sample
    (AllFieldGroupOrbitData.Pos (K := K) (tick := tick) allocation m sigma)
    (JointOrdinarySelection.hashLevel
      (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
  targets : Finset (AllFieldGroupOrbitData.Targets
    (K := K) (tick := tick) allocation m sigma)
  card_targets : targets.card =
    ⌊Real.exp ((m : ℝ) * (nativeCapacity (K := K) (tick := tick) allocation - slack))⌋₊
  good : ∀ e ∈ targets,
    (AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m width sigma).Good
      (JointOrdinarySelection.hashLevel
        (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
      (JointOrdinarySelection.hashSet
        (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
      (m : ℝ) e sample
  distinct_first : ∀ e ∈ targets, ∀ f ∈ targets, e ≠ f →
    (AllFieldGroupOrbitData.coarse (K := K) (tick := tick) allocation m sigma e).1 ≠
      (AllFieldGroupOrbitData.coarse (K := K) (tick := tick) allocation m sigma f).1

end MatrixMultiplication.AllFieldGroupSelection

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryIteration
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open MatrixMultiplication.Foundation AllFieldParameters JointPopulation
open CWStrands HistorySymmetry InheritedMasks JointCanonicalization
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)

abbrev CanonicalWords := CanonicalPairs (activeCounts (K := K) (tick := tick) allocation dilation)
  (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength)

abbrev ProducedWords := ∀ h : Produced K tick,
  Fin (population allocation dilation h.val) → Fin (currentLength h.val.1) → Fin 7

abbrev CanonicalClassPosition :=
  Σ c : Active K tick × JointPopulation.Shape, Fin (activeCounts allocation dilation c.1 c.2)

abbrev CanonicalHalfPosition :=
  CanonicalClassPosition (K := K) (tick := tick) allocation dilation × Bool

def canonicalClassEquiv : CanonicalClassPosition (K := K) (tick := tick) allocation dilation ≃
    (Σ h : Active K tick, Σ u : JointPopulation.Shape, Fin (activeCounts allocation dilation h u)) where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def splitArrangeEquiv :
    (Σ h : Active K tick, Σ b : h.val.1.Branch,
      Fin (branchPopulation allocation dilation h.val b)) × Bool ≃
        SplitPositions (K := K) (tick := tick) allocation dilation where
  toFun p := ⟨p.1.1, p.1.2.1, p.2, p.1.2.2⟩
  invFun p := (⟨p.1, p.2.1, p.2.2.2⟩, p.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def canonicalSplitEquiv :
    CanonicalHalfPosition (K := K) (tick := tick) allocation dilation ≃
      SplitPositions (K := K) (tick := tick) allocation dilation :=
  (Equiv.prodCongr
    ((canonicalClassEquiv allocation dilation).trans
      (Equiv.sigmaCongrRight fun h : Active K tick =>
        branchPositionEquiv allocation dilation h.val))
    (Equiv.refl Bool)).trans (splitArrangeEquiv allocation dilation)

def canonicalProducedEquiv :
    CanonicalHalfPosition (K := K) (tick := tick) allocation dilation ≃
      ProducedPositions (K := K) (tick := tick) allocation dilation :=
  (canonicalSplitEquiv allocation dilation).trans
    (producedPositionEquiv allocation dilation).symm

theorem splitProduced_length (p : SplitPositions (K := K) (tick := tick) allocation dilation) :
    currentLength ((producedPositionEquiv allocation dilation).symm p).1.val.1 =
      activeHalfLength p.1 := by
  simpa only [Equiv.apply_symm_apply, activeHalfLength] using
    producedPositionEquiv_length allocation dilation
      ((producedPositionEquiv allocation dilation).symm p)

def splitWord (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (p : SplitPositions (K := K) (tick := tick) allocation dilation) :
    Fin (activeHalfLength p.1) → Fin 7 :=
  let q := (producedPositionEquiv allocation dilation).symm p
  fun i => x q.1 q.2 (Fin.cast (splitProduced_length allocation dilation p).symm i)

def producedHalfWord (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool) :
    Fin (branchPopulation allocation dilation h.val b) → Fin (activeHalfLength h) → Fin 7 :=
  fun i => splitWord allocation dilation x ⟨h, b, right, i⟩

def regroupAt (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation) :
    Fin (activeHalfLength p.1.1.1) → Fin 7 :=
  splitWord allocation dilation x (canonicalSplitEquiv allocation dilation p)

def regroupWords (x : ProducedWords (K := K) (tick := tick) allocation dilation) :
    CanonicalWords (K := K) (tick := tick) allocation dilation where
  left c i := regroupAt allocation dilation x (⟨c, i⟩, false)
  right c i := regroupAt allocation dilation x (⟨c, i⟩, true)

def branchClassEquiv (h : Active K tick) (b : h.val.1.Branch) :
    Fin (branchPopulation allocation dilation h.val b) ≃
      Fin (activeCounts allocation dilation h (branchShape h.val b)) :=
  { toFun := fun i => ⟨i.val, by
      change i.val < jointCounts allocation dilation h.val (branchShape h.val b)
      rw [jointCounts_at]
      exact i.isLt⟩
    invFun := fun i => ⟨i.val, by
      simpa only [activeCounts, jointCounts_at] using i.isLt⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

def branchClassIndex (h : Active K tick) (b : h.val.1.Branch)
    (i : Fin (branchPopulation allocation dilation h.val b)) :
    Fin (activeCounts allocation dilation h (branchShape h.val b)) :=
  branchClassEquiv allocation dilation h b i

theorem regroupWords_branch (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool)
    (i : Fin (branchPopulation allocation dilation h.val b)) :
    (if right then (regroupWords allocation dilation x).right
      (h, branchShape h.val b) (branchClassIndex allocation dilation h b i)
    else (regroupWords allocation dilation x).left
      (h, branchShape h.val b) (branchClassIndex allocation dilation h b i)) =
        producedHalfWord allocation dilation x h b right i := by
  have he := (branchPositionEquiv allocation dilation h.val).apply_symm_apply ⟨b, i⟩
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact congrArg (fun q : Σ b : h.val.1.Branch,
        Fin (branchPopulation allocation dilation h.val b) =>
      producedHalfWord allocation dilation x h q.1 false q.2) he
  · exact congrArg (fun q : Σ b : h.val.1.Branch,
        Fin (branchPopulation allocation dilation h.val b) =>
      producedHalfWord allocation dilation x h q.1 true q.2) he

def canonicalHalfShape
    (p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation) : AllFieldParameters.Shape :=
  if p.2 then activeParentShape p.1.1.1 - JointCanonicalCW.shapeNat p.1.1.2
  else JointCanonicalCW.shapeNat p.1.1.2

theorem canonicalProduced_length
    (p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation) :
    currentLength (canonicalProducedEquiv allocation dilation p).1.val.1 =
      activeHalfLength p.1.1.1 :=
  splitProduced_length allocation dilation (canonicalSplitEquiv allocation dilation p)

theorem canonicalProduced_shape
    (p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation) :
    currentPhysicalShape (canonicalProducedEquiv allocation dilation p).1.val =
      canonicalHalfShape allocation dilation p := by
  let w := p.1.1.1
  let q := branchPositionEquiv allocation dilation w.val ⟨p.1.1.2, p.1.2⟩
  have hu : physicalShape w.val.2 (w.val.1.splitShape q.1) =
      JointCanonicalCW.shapeNat p.1.1.2 := by
    change physicalShape w.val.2 (w.val.1.splitShape q.1) = decodeShape p.1.1.2
    have hh := congrArg decodeShape
      (branchPositionEquiv_shape allocation dilation w.val ⟨p.1.1.2, p.1.2⟩)
    simpa only [branchShape, decode_encodePhysicalShape] using hh
  let shapeOfSplit (r : SplitPositions (K := K) (tick := tick) allocation dilation) :
      AllFieldParameters.Shape :=
    physicalShape r.1.val.2 (halfShape r.1.val.1.parentShape
      (r.1.val.1.splitShape r.2.1) r.2.2.1)
  have hs : currentPhysicalShape
      ((producedPositionEquiv allocation dilation).symm
        (canonicalSplitEquiv allocation dilation p)).1.val =
      shapeOfSplit ((producedPositionEquiv allocation dilation)
        ((producedPositionEquiv allocation dilation).symm
          (canonicalSplitEquiv allocation dilation p))) :=
    producedPositionEquiv_shape allocation dilation
      ((producedPositionEquiv allocation dilation).symm
        (canonicalSplitEquiv allocation dilation p))
  rw [Equiv.apply_symm_apply] at hs
  change currentPhysicalShape (canonicalProducedEquiv allocation dilation p).1.val =
    physicalShape w.val.2 (halfShape w.val.1.parentShape
      (w.val.1.splitShape q.1) p.2) at hs
  rw [hs]
  cases hr : p.2 <;>
    simp [canonicalHalfShape, halfShape, hr, physicalShape_complement, hu,
      activeParentShape]
  rfl

variable {F : Type*} [Field F]

theorem shapeTensor_finCast {m n : ℕ} (h : m = n) (g : AllFieldParameters.Shape)
    (x y z : Fin n → Fin 7) :
    shapeTensor (F := F) (Fin m) g (x ∘ Fin.cast h) (y ∘ Fin.cast h) (z ∘ Fin.cast h) =
      shapeTensor (Fin n) g x y z := by
  cases h
  rfl

def canonicalChildren : Tensor F
    (CanonicalWords (K := K) (tick := tick) allocation dilation)
    (CanonicalWords (K := K) (tick := tick) allocation dilation)
    (CanonicalWords (K := K) (tick := tick) allocation dilation) :=
  pairClassProduct (P := ClassPositions (activeCounts allocation dilation))
    (JointCanonicalCW.leftTensor activeHalfLength)
    (JointCanonicalCW.rightTensor activeHalfLength activeParentShape)

def producedBase : Tensor F
    (ProducedWords (K := K) (tick := tick) allocation dilation)
    (ProducedWords (K := K) (tick := tick) allocation dilation)
    (ProducedWords (K := K) (tick := tick) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : Produced K tick =>
    Tensor.power (shapeTensor (Fin (currentLength h.val.1)) (currentPhysicalShape h.val))
      (population allocation dilation h.val))

def canonicalHalfWord (x : CanonicalWords (K := K) (tick := tick) allocation dilation)
    (p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation) :
    Fin (activeHalfLength p.1.1.1) → Fin 7 :=
  if p.2 then x.right p.1.1 p.1.2 else x.left p.1.1 p.1.2

theorem regroupWords_half (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation) :
    canonicalHalfWord allocation dilation (regroupWords allocation dilation x) p =
      regroupAt allocation dilation x p := by
  rcases p with ⟨⟨c, i⟩, right⟩
  cases right <;> simp only [canonicalHalfWord, regroupWords, Bool.false_eq_true, ↓reduceIte]

theorem canonicalChildren_flat
    (x y z : CanonicalWords (K := K) (tick := tick) allocation dilation) :
    canonicalChildren (F := F) allocation dilation x y z =
      ∏ p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation,
        shapeTensor (Fin (activeHalfLength p.1.1.1)) (canonicalHalfShape allocation dilation p)
          (canonicalHalfWord allocation dilation x p)
          (canonicalHalfWord allocation dilation y p)
          (canonicalHalfWord allocation dilation z p) := by
  simp only [CanonicalHalfPosition, Fintype.prod_prod_type, CanonicalClassPosition,
    Fintype.prod_sigma, Fintype.prod_bool, canonicalHalfShape, canonicalHalfWord,
    Bool.false_eq_true, ↓reduceIte, Finset.prod_mul_distrib,
    canonicalChildren, pairClassProduct, classProduct, JointCanonicalCW.leftTensor,
    JointCanonicalCW.rightTensor]
  exact mul_comm _ _

theorem producedBase_flat
    (x y z : ProducedWords (K := K) (tick := tick) allocation dilation) :
    producedBase (F := F) allocation dilation x y z =
      ∏ p : ProducedPositions (K := K) (tick := tick) allocation dilation,
        shapeTensor (Fin (currentLength p.1.val.1)) (currentPhysicalShape p.1.val)
          (x p.1 p.2) (y p.1 p.2) (z p.1 p.2) := by
  simp only [producedBase, CommonDimensions.familyProduct, Tensor.power,
    ProducedPositions, Fintype.prod_sigma]

theorem regroup_coefficient_at
    (x y z : ProducedWords (K := K) (tick := tick) allocation dilation)
    (p : CanonicalHalfPosition (K := K) (tick := tick) allocation dilation) :
    shapeTensor (F := F) (Fin (activeHalfLength p.1.1.1)) (canonicalHalfShape allocation dilation p)
      (regroupAt allocation dilation x p) (regroupAt allocation dilation y p)
      (regroupAt allocation dilation z p) =
    shapeTensor (Fin (currentLength (canonicalProducedEquiv allocation dilation p).1.val.1))
      (currentPhysicalShape (canonicalProducedEquiv allocation dilation p).1.val)
      (x (canonicalProducedEquiv allocation dilation p).1 (canonicalProducedEquiv allocation dilation p).2)
      (y (canonicalProducedEquiv allocation dilation p).1 (canonicalProducedEquiv allocation dilation p).2)
      (z (canonicalProducedEquiv allocation dilation p).1 (canonicalProducedEquiv allocation dilation p).2) := by
  rw [← canonicalProduced_shape allocation dilation p]
  exact shapeTensor_finCast (canonicalProduced_length allocation dilation p).symm _ _ _ _

theorem regroup_coefficient
    (x y z : ProducedWords (K := K) (tick := tick) allocation dilation) :
    canonicalChildren (F := F) allocation dilation
      (regroupWords allocation dilation x) (regroupWords allocation dilation y)
      (regroupWords allocation dilation z) = producedBase allocation dilation x y z := by
  rw [canonicalChildren_flat, producedBase_flat]
  simp only [regroupWords_half]
  exact Fintype.prod_equiv (canonicalProducedEquiv allocation dilation) _ _
    (regroup_coefficient_at allocation dilation x y z)

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryProducedMasks

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws InheritedMasks
open JointCanonicalization
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def nativeChildWidth (ε : ℝ) (h : Active K tick) : ℝ :=
  (ε / 16 ^ h.val.1.stage.val) / 8

def halfPositionEquiv (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool) :
    Fin (branchPopulation allocation dilation w b) ≃
      Fin (population allocation dilation (w.1.child b right, w.2)) where
  toFun := halfPosition allocation dilation w b right
  invFun := unhalfPosition allocation dilation w b right
  left_inv := unhalf_halfPosition allocation dilation w b right
  right_inv := half_unhalfPosition allocation dilation w b right

def childHalfWord (allocation : Allocation) (dilation : ℕ)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool)
    (v : HistoryWord allocation dilation (h.val.1.child b right, h.val.2)) :
    Fin (branchPopulation allocation dilation h.val b) →
      Fin (activeHalfLength h) → Fin 7 :=
  fun i j => v (halfPosition allocation dilation h.val b right i)
    (Fin.cast (child_length h.val.1 b right).symm j)

theorem subsingleton_typeWindow {P A : Type*} [Fintype P] [Nonempty P]
    [Subsingleton A] [DecidableEq A] (η : ℝ) (hη : 0 ≤ η) (w : P → A) :
    typeWindow (fun _ : A => 1) η w := by
  intro a
  have hcount : wordPopulation w a = Fintype.card P := by
    apply Fintype.card_congr
    exact
      { toFun := Subtype.val
        invFun := fun i => ⟨i, Subsingleton.elim _ _⟩
        left_inv := fun i => Subtype.ext rfl
        right_inv := fun i => rfl }
  have hpos : (0 : ℝ) < Fintype.card P := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card P)
  simpa only [empiricalLaw, hcount, div_self (ne_of_gt hpos), sub_self, abs_zero] using hη

theorem childHalfWord_window (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool)
    (v : HistoryWord allocation dilation (h.val.1.child b right, h.val.2))
    (hv : residentMask allocation dilation ε (h.val.1.child b right, h.val.2) side v)
    (hp : 0 < branchPopulation allocation dilation h.val b) :
    typeWindow (fun a => (h.val.1.childLaw
        (halfShape h.val.1.parentShape (h.val.1.splitShape b) right)
        (h.val.2.symm side) a : ℝ)) (nativeChildWidth ε h)
      (h.val.1.statistic ∘ childHalfWord allocation dilation h b right v) := by
  rcases h with ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA parent =>
      have hp' : 0 < population allocation dilation
          ((Work.stageA parent).child b right, phi) := by
        rw [branchPopulation_half allocation dilation (.stageA parent, phi) b right]
        exact hp
      have hw := (Subdivision.typeWindow_reindex
        (residentLaw ((Work.stageA parent).child b right, phi) side)
        (ε / 8) (fun i => residentStatistic ((Work.stageA parent).child b right) (v i))
        (halfPositionEquiv allocation dilation (.stageA parent, phi) b right)).mpr (hv hp')
      have he : nativeChildWidth ε (⟨(.stageA parent, phi), ht⟩ : Active K tick) = ε / 8 := by
        norm_num [nativeChildWidth, Work.stage]
      rw [he]
      exact hw
  | stageB parent =>
      have hp' : 0 < population allocation dilation
          ((Work.stageB parent).child b right, phi) := by
        rw [branchPopulation_half allocation dilation (.stageB parent, phi) b right]
        exact hp
      have hw := (Subdivision.typeWindow_reindex
        (residentLaw ((Work.stageB parent).child b right, phi) side)
        (ε / 128) (fun i => residentStatistic ((Work.stageB parent).child b right) (v i))
        (halfPositionEquiv allocation dilation (.stageB parent, phi) b right)).mpr (hv hp')
      have he : nativeChildWidth ε (⟨(.stageB parent, phi), ht⟩ : Active K tick) = ε / 128 := by
        norm_num [nativeChildWidth, Work.stage, div_div]
      rw [he]
      exact hw
  | stageC parent =>
      let : Nonempty (Fin (branchPopulation allocation dilation (.stageC parent, phi) b)) :=
        ⟨⟨0, hp⟩⟩
      let : Subsingleton (Work.stageC parent).Statistic := by
        change Subsingleton PUnit
        infer_instance
      simp only [Work.childLaw, Rat.cast_one]
      apply subsingleton_typeWindow
      unfold nativeChildWidth
      positivity

def producedChildWord (allocation : Allocation) (dilation : ℕ)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool) :
    HistoryWord allocation dilation (h.val.1.child b right, h.val.2) := by
  rcases h with ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA parent => exact x ⟨(.afterA ⟨parent, b, right⟩, phi), ht.symm⟩
  | stageB parent =>
      by_cases hp : positive (bShape (⟨parent, b, right⟩ : AfterB K)) = true
      · let g : BPositive K := ⟨⟨parent, b, right⟩, hp⟩
        let e := bSubdivisionPositionEquiv allocation dilation g phi
        exact fun j => x ⟨(.partC (g, (e j).1), phi), ht.symm⟩ (e j).2
      · exact x ⟨(.afterB ⟨parent, b, right⟩, phi), ht.symm, hp⟩
  | stageC parent => exact x ⟨(.afterC (parent, b, right), phi), ht.symm⟩

theorem splitWord_eq_of_position (allocation : Allocation) (dilation : ℕ)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (p : SplitPositions (K := K) (tick := tick) allocation dilation)
    (q : ProducedPositions (K := K) (tick := tick) allocation dilation)
    (hq : (producedPositionEquiv allocation dilation).symm p = q)
    (hlen : currentLength q.1.val.1 = activeHalfLength p.1) :
    splitWord allocation dilation x p =
      fun i => x q.1 q.2 (Fin.cast hlen.symm i) := by
  subst q
  rfl

end MatrixMultiplication.AllFieldHistoryProducedMasks

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryProduced

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldHistoryProducedMasks
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ)

def passes (ε : ℝ) (side : Fin 3)
    (w : AllFieldHistory.ProducedWords (K := K) (tick := tick) allocation m) : Prop :=
  ∀ h : Produced K tick, residentMask allocation m ε h.val side (w h)

theorem producedTensor_eq_delete (F : Type*) [Field F] (ε : ℝ) :
    AllFieldHistoryRegrouping.producedTensor (K := K) (tick := tick) allocation m F ε =
      ExactRecovery.delete (producedBase (F := F) (K := K) (tick := tick) allocation m)
        (passes allocation m ε 0) (passes allocation m ε 1) (passes allocation m ε 2) := by
  funext x y z
  simp only [AllFieldHistoryRegrouping.producedTensor, CommonDimensions.familyProduct,
    historyTensor, ExactRecovery.delete, Fintype.prod_ite_zero,
    passes, forall_and, producedBase]

theorem canonical_eq_delete (F : Type*) [Field F] (ε : ℝ) :
    AllFieldHistoryRecovery.canonical F (K := K) (tick := tick) allocation m ε =
      ExactRecovery.delete (canonicalChildren (F := F) (K := K) (tick := tick) allocation m)
        (AllFieldHistoryMasks.childWindows allocation m ε 0)
        (AllFieldHistoryMasks.childWindows allocation m ε 1)
        (AllFieldHistoryMasks.childWindows allocation m ε 2) := by
  have hb := JointCanonicalCW.canonicalBase_eq_children (F := F)
    (activeCounts (K := K) (tick := tick) allocation m)
    activeHalfLength activeHalfLength activeParentShape
    AllFieldHistoryRecovery.halfLength_le_eight
    (fun h u hu => jointCounts_support_le allocation m h.val u hu)
  unfold AllFieldHistoryRecovery.canonical JointCanonicalization.canonicalIdeal
  change ExactRecovery.delete
    (JointCanonicalization.canonicalBase (activeCounts allocation m)
      (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength)
      (JointCanonicalCW.parentTensor activeHalfLength activeHalfLength activeParentShape)
      (JointCanonicalCW.coarse activeHalfLength activeHalfLength
        AllFieldHistoryRecovery.halfLength_le_eight))
    (AllFieldHistoryMasks.childWindows allocation m ε 0)
    (AllFieldHistoryMasks.childWindows allocation m ε 1)
    (AllFieldHistoryMasks.childWindows allocation m ε 2) = _
  rw [hb]
  rfl

def pulled (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (AllFieldHistory.ProducedWords (K := K) (tick := tick) allocation m)
      (AllFieldHistory.ProducedWords (K := K) (tick := tick) allocation m)
      (AllFieldHistory.ProducedWords (K := K) (tick := tick) allocation m) :=
  Tensor.pullback (regroupWords allocation m) (regroupWords allocation m)
    (regroupWords allocation m)
    (AllFieldHistoryRecovery.canonical F (K := K) (tick := tick) allocation m ε)

end MatrixMultiplication.AllFieldHistoryProduced

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryTick

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldGroupSelection AllFieldHistoryGroupedRecovery
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ) (ε slack : ℝ)

abbrev Choices := ∀ sigma : Placement,
  Selected (K := K) (tick := tick) allocation m ε sigma slack

abbrev Tags (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :=
  ∀ sigma : Placement, {e // e ∈ (chosen sigma).targets}

local instance tagsDecidableEq_r14e266_1 (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    DecidableEq (Tags allocation m ε slack chosen) := Classical.decEq _
instance tagsFintype (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Fintype (Tags allocation m ε slack chosen) := inferInstance

theorem card_tags (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Fintype.card (Tags allocation m ε slack chosen) =
      ∏ _sigma : Placement,
        ⌊Real.exp ((m : ℝ) * (nativeCapacity (K := K) (tick := tick) allocation - slack))⌋₊ := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro sigma _
  simpa only [Fintype.card_coe] using (chosen sigma).card_targets

end MatrixMultiplication.AllFieldHistoryTick

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryIteration

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

section Presentation

variable {F : Type*} [Field F] {SX SY SZ X Y Z : Type}
    [Fintype SX] [Fintype SY] [Fintype SZ]
    {source : Tensor F SX SY SZ} {target next : Tensor F X Y Z}

def retarget (E : Execution source target) (h : target = next) :
    Execution source next where
  Copies := E.Copies
  copies_positive := E.copies_positive
  map := {
    x := E.map.x
    y := E.map.y
    z := E.map.z
    coefficient := E.map.coefficient.trans h
  }

@[simp] theorem retarget_copies (E : Execution source target) (h : target = next) :
    Fintype.card (retarget E h).Copies = Fintype.card E.Copies := rfl

end Presentation

variable {K : ℕ} (allocation : Allocation) (m : ℕ) (ε slack : ℝ)

abbrev ScheduleChoices := ∀ t : Fin (K + 2),
  AllFieldHistoryTick.Choices (K := K) (tick := t.val) allocation m ε slack

def Labels (InitialTag : Type)
    (chosen : ScheduleChoices (K := K) allocation m ε slack) :
    (n : ℕ) → n ≤ K + 2 → Type
  | 0, _ => InitialTag
  | n + 1, hn =>
      Labels InitialTag chosen n (Nat.le_of_succ_le hn) ×
        AllFieldHistoryTick.Tags allocation m ε slack (chosen ⟨n, hn⟩)

instance labelsFintype (InitialTag : Type) [Fintype InitialTag]
    (chosen : ScheduleChoices (K := K) allocation m ε slack) :
    (n : ℕ) → (hn : n ≤ K + 2) →
      Fintype (Labels allocation m ε slack InitialTag chosen n hn)
  | 0, _ => inferInstanceAs (Fintype InitialTag)
  | n + 1, hn => by
      letI := labelsFintype InitialTag chosen n (Nat.le_of_succ_le hn)
      exact inferInstanceAs (Fintype
        (Labels allocation m ε slack InitialTag chosen n (Nat.le_of_succ_le hn) ×
          AllFieldHistoryTick.Tags allocation m ε slack (chosen ⟨n, hn⟩)))

theorem card_labels (InitialTag : Type) [Fintype InitialTag]
    (chosen : ScheduleChoices (K := K) allocation m ε slack)
    (n : ℕ) (hn : n ≤ K + 2) :
    Fintype.card (Labels allocation m ε slack InitialTag chosen n hn) =
      Fintype.card InitialTag * ∏ t : Fin n, ∏ _sigma : Placement,
        ⌊Real.exp ((m : ℝ) *
          (AllFieldGroupSelection.nativeCapacity (K := K) (tick := t.val) allocation - slack))⌋₊ := by
  induction n with
  | zero =>
      simp [Labels]
      rfl
  | succ n ih =>
      change Fintype.card
        (Labels allocation m ε slack InitialTag chosen n (Nat.le_of_succ_le hn) ×
          AllFieldHistoryTick.Tags allocation m ε slack (chosen ⟨n, hn⟩)) = _
      rw [Fintype.card_prod, AllFieldHistoryTick.card_tags, ih, Fin.prod_univ_castSucc]
      exact Nat.mul_assoc _ _ _

abbrev Tags (InitialTag : Type)
    (chosen : ScheduleChoices (K := K) allocation m ε slack) :=
  Labels allocation m ε slack InitialTag chosen (K + 2) le_rfl

theorem card_tags (InitialTag : Type) [Fintype InitialTag]
    (chosen : ScheduleChoices (K := K) allocation m ε slack) :
    Fintype.card (Tags allocation m ε slack InitialTag chosen) =
      Fintype.card InitialTag * ∏ t : Fin (K + 2), ∏ _sigma : Placement,
        ⌊Real.exp ((m : ℝ) *
          (AllFieldGroupSelection.nativeCapacity (K := K) (tick := t.val) allocation - slack))⌋₊ :=
  card_labels allocation m ε slack InitialTag chosen (K + 2) le_rfl

end MatrixMultiplication.AllFieldHistoryIteration

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_OrderedLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialChoice

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily Filter
open scoped BigOperators Topology Classical

variable {K : ℕ}

structure Choice (allocation : Allocation) (m : ℕ) (δ : ℝ) where
  sample : AllFieldInitialFamily.Sample (K := K) allocation
    (δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) m
  selected : Finset (JointPopulation.Target (initialJointCounts (K := K) allocation m))
  card_selected : selected.card = AllFieldConstructionRates.initialCount (K := K) allocation δ m
  good : ∀ e ∈ selected, AllFieldInitialFamily.Good allocation
    (δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) m sample e

abbrev Tags (allocation : Allocation) (m : ℕ) (δ : ℝ)
    (choice : Choice (K := K) allocation m δ) :=
  AllFieldInitialHash.SelectedTargets (initialJointCounts (K := K) allocation m)
    choice.selected

@[simp] theorem card_tags (allocation : Allocation) (m : ℕ) (δ : ℝ)
    (choice : Choice (K := K) allocation m δ) :
    Fintype.card (Tags allocation m δ choice) =
      AllFieldConstructionRates.initialCount (K := K) allocation δ m := by
  rw [AllFieldInitialHash.selectedTargets_card]
  exact choice.card_selected

def execution (allocation : Allocation) (m : ℕ) (δ : ℝ)
    (choice : Choice (K := K) allocation m δ) (F : Type*) [Field F] (ε : ℝ) :
    Execution (cwSource F K (populationLength (K := K) allocation m))
      (Tensor.directSum (fun _ : Tags allocation m δ choice =>
        stateTensor F (K := K) allocation m ε 0)) :=
  AllFieldInitialFamily.executionWithWidth allocation F
    (δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) ε m
    choice.sample choice.selected choice.good

@[simp] theorem execution_copies (allocation : Allocation) (m : ℕ) (δ : ℝ)
    (choice : Choice (K := K) allocation m δ) (F : Type*) [Field F] (ε : ℝ) :
    Fintype.card (execution allocation m δ choice F ε).Copies = 1 := rfl

end MatrixMultiplication.AllFieldInitialChoice

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldTerminal

open MatrixMultiplication.Foundation AllFieldFiniteFamily CommonDimensions
open scoped BigOperators Classical

variable {F : Type*} {H : Type} [Field F] [Fintype H]
  {X Y Z : H → Type} [∀ h, Fintype (X h)] [∀ h, Fintype (Y h)] [∀ h, Fintype (Z h)]
  (T : ∀ h, Tensor F (X h) (Y h) (Z h)) (A B C : H → Type)
  [∀ h, Fintype (A h)] [∀ h, Fintype (B h)] [∀ h, Fintype (C h)]
  (maps : ∀ h, LocalMap (T h) (Tensor.matrixCoefficients (A h) (B h) (C h)))

def terminalProductMap :
    LocalMap (familyProduct T) (Tensor.matrixCoefficients (∀ h, A h) (∀ h, B h) (∀ h, C h)) :=
  LocalMap.ofExists (TerminalProducts.matrix_restriction_of_history_restrictions
    T A B C (fun h => (maps h).x) (fun h => (maps h).y) (fun h => (maps h).z)
    (fun h => (maps h).coefficient))

variable {I : Type} [Fintype I] {K N : ℕ}

def terminalExecution
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T))) :
    Execution (cwSource F K N)
      (AllFieldSource.matrixTarget F (Fintype.card (∀ h, A h))
        (Fintype.card (∀ h, B h)) (Fintype.card (∀ h, C h)) (Fintype.card I)) :=
  (E.restrict _ ((terminalProductMap T A B C maps).parallelCopies I)).restrict _
    (LocalMap.ofExists (TerminalRelabel.directSum_matrix_restrict_fin (K := F)
      I (∀ h, A h) (∀ h, B h) (∀ h, C h)))

@[simp] theorem terminalExecution_copies
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T))) :
    Fintype.card (terminalExecution T A B C maps E).Copies = Fintype.card E.Copies := rfl

def finish
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T)))
    (hA : 0 < Fintype.card (∀ h, A h)) (hB : 0 < Fintype.card (∀ h, B h))
    (hC : 0 < Fintype.card (∀ h, C h)) (hI : 0 < Fintype.card I) : AllFieldWitness F :=
  (terminalExecution T A B C maps E).toWitness hA hB hC hI

@[simp] theorem finish_multiplicity
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T)))
    (hA : 0 < Fintype.card (∀ h, A h)) (hB : 0 < Fintype.card (∀ h, B h))
    (hC : 0 < Fintype.card (∀ h, C h)) (hI : 0 < Fintype.card I) :
    (finish T A B C maps E hA hB hC hI).multiplicity = Fintype.card I := rfl

@[simp] theorem finish_rankBound
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T)))
    (hA : 0 < Fintype.card (∀ h, A h)) (hB : 0 < Fintype.card (∀ h, B h))
    (hC : 0 < Fintype.card (∀ h, C h)) (hI : 0 < Fintype.card I) :
    (finish T A B C maps E hA hB hC hI).rankBound =
      AllFieldSource.rankBudget E.Copies K N := rfl

end MatrixMultiplication.AllFieldTerminal

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialZeroFinish

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldFiniteFamily
open AllFieldInitialLeafRates CWWindowedLeaves CWStrands CWZeroGeometry
open scoped BigOperators Classical

variable {K : ℕ}

abbrev Index (K : ℕ) := PopulationHistory K

local instance instDecidableEqIndex : DecidableEq (Index K) := Classical.decEq _

theorem shape_total (h : InitialZero K) : shapeTotal (initialShape h.val) = 16 :=
  (root_shape_spec _ (initialShape_mem h.val)).2

theorem has_zero (h : InitialZero K) : ∃ i, initialShape h.val i = 0 :=
  terminal_has_zero (.initial h.val) h.property

theorem canonical_axes_ne (h : InitialZero K) :
    zeroAxis (initialShape h.val) ≠ maxAxis (initialShape h.val) :=
  zero_ne_selected _ _ _ (by rw [shape_total]; norm_num)
    (zeroAxis_spec _ (has_zero h)) (maxAxis_spec _)

def zero (h : Index K) : Fin 3 := h.2 (zeroAxis (initialShape h.1.val))
def selected (h : Index K) : Fin 3 := h.2 (maxAxis (initialShape h.1.val))

theorem axes_ne (h : Index K) : zero h ≠ selected h :=
  fun he => canonical_axes_ne h.1 (h.2.injective he)

theorem weights_sum (h : InitialZero K) :
    shapeMax (initialShape h.val) + (16 - shapeMax (initialShape h.val)) = 2 * 8 := by
  simpa only [shape_total h] using max_add_complement (initialShape h.val)

theorem physical_shape_eq (h : Index K) :
    physicalShape h.2 (initialShape h.1.val) =
      CWOrientedZero.placedShape (zero h) (selected h)
        (shapeMax (initialShape h.1.val)) (16 - shapeMax (initialShape h.1.val)) := by
  simpa only [zero, selected, shape_total h.1] using
    physicalShape_eq_placedShape (initialShape h.1.val) h.2
      (zeroAxis (initialShape h.1.val)) (maxAxis (initialShape h.1.val))
      (zeroAxis_spec _ (has_zero h.1)) (maxAxis_spec _) (canonical_axes_ne h.1)

variable (allocation : Allocation) (dilation : ℕ)

def embed (h : Index K) (side : Fin 3) (w : Words allocation dilation h) :
    HistoryWord allocation dilation (.initial h.1.val, h.2) :=
  fun i => CWOrientedZero.sideWord (zero h) (selected h) side (w i)

theorem coefficient (F : Type*) [Field F] (ε : ℝ) (h : Index K)
    (x y z : Words allocation dilation h) :
    historyTensor F allocation dilation ε (.initial h.1.val, h.2)
      (embed allocation dilation h 0 x) (embed allocation dilation h 1 y)
      (embed allocation dilation h 2 z) =
      if CWOrientedZero.matched (zero h) x y z then 1 else 0 := by
  rw [historyTensor_initial, physical_shape_eq]
  exact CWOrientedZero.power_coefficient F 8 (shapeMax (initialShape h.1.val))
    (16 - shapeMax (initialShape h.1.val))
    (population allocation dilation (.initial h.1.val, h.2))
    (weights_sum h.1) (zero h) (selected h) (axes_ne h)
    (fun w : Words allocation dilation h => w) Function.injective_id x y z

abbrev RowIndex (h : Index K) := CWOrientedZero.Row (zero h) (Words allocation dilation h)
abbrev MiddleIndex (h : Index K) := CWOrientedZero.Middle (zero h) (Words allocation dilation h)
abbrev ColumnIndex (h : Index K) := CWOrientedZero.Column (zero h) (Words allocation dilation h)

def factorMap (F : Type*) [Field F] (ε : ℝ) (h : Index K) :
    LocalMap (historyTensor F allocation dilation ε (.initial h.1.val, h.2))
      (Tensor.matrixCoefficients (RowIndex allocation dilation h)
        (MiddleIndex allocation dilation h) (ColumnIndex allocation dilation h)) := by
  letI : Nonempty (Words allocation dilation h) :=
    Fintype.card_pos_iff.mp (card_words_pos allocation dilation h)
  exact CWOrientedZero.ofMatching F _ (zero h) (embed allocation dilation h)
    (coefficient allocation dilation F ε h)

theorem factor_volume (h : Index K) :
    Fintype.card (RowIndex allocation dilation h) *
      Fintype.card (MiddleIndex allocation dilation h) *
      Fintype.card (ColumnIndex allocation dilation h) =
      Fintype.card (Words allocation dilation h) :=
  CWOrientedZero.volume (zero h) (Words allocation dilation h)

abbrev RawWords := ∀ h : Index K,
  HistoryWord allocation dilation (.initial h.1.val, h.2)
abbrev Rows := ∀ h : Index K, RowIndex allocation dilation h
abbrev Middles := ∀ h : Index K, MiddleIndex allocation dilation h
abbrev Columns := ∀ h : Index K, ColumnIndex allocation dilation h

def source (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (RawWords (K := K) allocation dilation)
      (RawWords (K := K) allocation dilation) (RawWords (K := K) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : Index K =>
    historyTensor F allocation dilation ε (.initial h.1.val, h.2))

def finishMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (source (K := K) allocation dilation F ε)
      (Tensor.matrixCoefficients (Rows (K := K) allocation dilation)
        (Middles (K := K) allocation dilation) (Columns (K := K) allocation dilation)) :=
  AllFieldTerminal.terminalProductMap
    (H := Index K)
    (X := fun h => HistoryWord allocation dilation (.initial h.1.val, h.2))
    (Y := fun h => HistoryWord allocation dilation (.initial h.1.val, h.2))
    (Z := fun h => HistoryWord allocation dilation (.initial h.1.val, h.2))
    (fun h : Index K => historyTensor F allocation dilation ε (.initial h.1.val, h.2))
    (RowIndex allocation dilation) (MiddleIndex allocation dilation)
    (ColumnIndex allocation dilation) (factorMap allocation dilation F ε)

theorem volume_eq :
    Fintype.card (Rows (K := K) allocation dilation) *
      Fintype.card (Middles (K := K) allocation dilation) *
      Fintype.card (Columns (K := K) allocation dilation) =
      AllFieldInitialLeafRates.volume (K := K) allocation dilation := by
  rw [AllFieldInitialLeafRates.volume_eq_prod]
  simp only [Rows, Middles, Columns, Fintype.card_pi,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro h _
  simpa only [Words, Fintype.card_pi] using factor_volume allocation dilation h

end MatrixMultiplication.AllFieldInitialZeroFinish

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.CommonDimensions

namespace MatrixMultiplication.AllFieldStageCRegroup

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H B W F : Type*}

variable [Fintype H] [Fintype B] [CommSemiring F]

def splitTensor (count : H → B → Bool → ℕ) (T : H → B → Bool → Tensor F W W W) :
    Tensor F (SplitWords count W) (SplitWords count W) (SplitWords count W) :=
  familyProduct fun h => familyProduct fun b => familyProduct fun r =>
    Tensor.power (T h b r) (count h b r)

def pairedTensor (count : H → B → Bool → ℕ) (T : H → B → Bool → Tensor F W W W) :
    Tensor F (PairedWords count W) (PairedWords count W) (PairedWords count W) :=
  familyProduct fun h => familyProduct fun p : Positions count h =>
    Tensor.product (T h p.1 false) (T h p.1 true)

theorem pullback_unpair (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false)
    (T : H → B → Bool → Tensor F W W W) :
    Tensor.pullback (unpair count hc) (unpair count hc) (unpair count hc)
      (splitTensor count T) = pairedTensor count T := by
  funext x y z
  simp only [Tensor.pullback, splitTensor, pairedTensor, familyProduct]
  apply Finset.prod_congr rfl
  intro h _
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro b _
  rw [Fintype.prod_bool]
  change
    (∏ j : Fin (count h b true), T h b true
      (x h ⟨b, Fin.cast (hc h b true) j⟩).2
      (y h ⟨b, Fin.cast (hc h b true) j⟩).2
      (z h ⟨b, Fin.cast (hc h b true) j⟩).2) *
    (∏ j : Fin (count h b false), T h b false
      (x h ⟨b, j⟩).1 (y h ⟨b, j⟩).1 (z h ⟨b, j⟩).1) =
    ∏ j : Fin (count h b false),
      T h b false (x h ⟨b, j⟩).1 (y h ⟨b, j⟩).1 (z h ⟨b, j⟩).1 *
      T h b true (x h ⟨b, j⟩).2 (y h ⟨b, j⟩).2 (z h ⟨b, j⟩).2
  rw [prod_fin_cast (hc h b true) (fun j =>
    T h b true (x h ⟨b, j⟩).2 (y h ⟨b, j⟩).2 (z h ⟨b, j⟩).2),
    Finset.prod_mul_distrib]
  exact mul_comm _ _

end MatrixMultiplication.AllFieldStageCRegroup

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldStageCFinish

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters AllFieldFiniteFamily
open CWStageCProducts
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

def localMapWithFintypes_inline_MatrixMultiplication_AllFieldStageCFinish {F : Type*} [Field F]
    {X Y Z X' Y' Z' : Type} [newX : Fintype X] [newY : Fintype Y] [newZ : Fintype Z]
    {oldX : Fintype X} {oldY : Fintype Y} {oldZ : Fintype Z}
    {T : Tensor F X Y Z} {Q : Tensor F X' Y' Z'}
    (M : @LocalMap F _ X Y Z X' Y' Z' oldX oldY oldZ T Q) :
    @LocalMap F _ X Y Z X' Y' Z' newX newY newZ T Q := by
  cases Subsingleton.elim oldX newX
  cases Subsingleton.elim oldY newY
  cases Subsingleton.elim oldZ newZ
  exact M

def pairLocalMap {F : Type*} {H B W : Type} [Field F] [Fintype H]
    [Fintype B] [Fintype W] [DecidableEq H] [DecidableEq B] (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false)
    (T : H → B → Bool → Tensor F W W W) :
    LocalMap (AllFieldStageCRegroup.splitTensor count T)
      (AllFieldStageCRegroup.pairedTensor count T) where
  x := fun x s => if s = AllFieldStageCRegroup.unpair count hc x then 1 else 0
  y := fun y s => if s = AllFieldStageCRegroup.unpair count hc y then 1 else 0
  z := fun z s => if s = AllFieldStageCRegroup.unpair count hc z then 1 else 0
  coefficient := by
    have hp := Tensor.pullback_eq_restrict
      (AllFieldStageCRegroup.unpair (W := W) count hc)
      (AllFieldStageCRegroup.unpair (W := W) count hc)
      (AllFieldStageCRegroup.unpair (W := W) count hc)
      (AllFieldStageCRegroup.splitTensor count T)
    exact hp.symm.trans (AllFieldStageCRegroup.pullback_unpair count hc T)

def shapeFactorMap (F : Type*) [Field F] (side : Fin 3)
    (placement : Equiv.Perm (Fin 3)) (count : Fin 4 → ℕ) :
    LocalMap (placedShapeChildProducts F side placement count)
      (Tensor.matrixCoefficients (RowWords (placement side) count)
        (MiddleWords (placement side) count) (ColumnWords (placement side) count)) :=
  LocalMap.ofExists (placedShapeChildProducts_restriction F side placement count)

def shapeHistoryMap {F : Type*} {H : Type} [Field F] [Fintype H] [DecidableEq H]
    (side : H → Fin 3) (placement : H → Equiv.Perm (Fin 3))
    (count : H → Fin 4 → ℕ) :
    LocalMap (CommonDimensions.familyProduct (fun h =>
      placedShapeChildProducts F (side h) (placement h) (count h)))
      (Tensor.matrixCoefficients
        (HistoryRowWords (fun h => placement h (side h)) count)
        (HistoryMiddleWords (fun h => placement h (side h)) count)
        (HistoryColumnWords (fun h => placement h (side h)) count)) := by
  let M := AllFieldTerminal.terminalProductMap
    (F := F) (H := H)
    (X := fun h => Positions (count h) → ChildWords)
    (Y := fun h => Positions (count h) → ChildWords)
    (Z := fun h => Positions (count h) → ChildWords)
    (fun h => placedShapeChildProducts F (side h) (placement h) (count h))
    (fun h => RowWords (placement h (side h)) (count h))
    (fun h => MiddleWords (placement h (side h)) (count h))
    (fun h => ColumnWords (placement h (side h)) (count h))
    (fun h => LocalMap.redecideMatrix
      (shapeFactorMap F (side h) (placement h) (count h)) _ _ _)
  let N := localMapWithFintypes_inline_MatrixMultiplication_AllFieldStageCFinish (F := F)
    (X := ∀ h, Positions (count h) → ChildWords)
    (Y := ∀ h, Positions (count h) → ChildWords)
    (Z := ∀ h, Positions (count h) → ChildWords)
    (newX := inferInstance) (newY := inferInstance) (newZ := inferInstance) M
  exact LocalMap.redecideMatrix N _ _ _

variable {K : ℕ} (allocation : Allocation) (dilation : ℕ)

abbrev Index (K : ℕ) := AfterC K × Placement

abbrev RawWords := ∀ h : Index K,
  HistoryWord allocation dilation (.afterC h.1, h.2)

def source (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (RawWords (K := K) allocation dilation)
      (RawWords (K := K) allocation dilation) (RawWords (K := K) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : Index K =>
    historyTensor F allocation dilation ε (.afterC h.1, h.2))

def counts (h : PopulationHistory K) (b : Fin 4) (right : Bool) : ℕ :=
  population allocation dilation (.afterC (h.1, b, right), h.2)

theorem counts_half (h : PopulationHistory K) (b : Fin 4) (right : Bool) :
    counts allocation dilation h b right = counts allocation dilation h b false :=
  branchPopulation_half allocation dilation (.stageC h.1, h.2) b right

@[simp] theorem counts_false (h : PopulationHistory K) (b : Fin 4) :
    counts allocation dilation h b false = populationAtomCounts allocation dilation h b := rfl

def leaf (F : Type*) [Field F] (h : PopulationHistory K) (b : Fin 4) (right : Bool) :
    Tensor F SingleWord SingleWord SingleWord :=
  CWStrands.shapeTensor (Fin 1) (physicalShape h.2 (cShape (h.1, b, right)))

abbrev GroupedWords := AllFieldStageCRegroup.SplitWords
  (counts (K := K) allocation dilation) SingleWord

abbrev PairedWords := AllFieldStageCRegroup.PairedWords
  (counts (K := K) allocation dilation) SingleWord

def groupedSource (F : Type*) [Field F] :=
  AllFieldStageCRegroup.splitTensor (counts (K := K) allocation dilation) (leaf (K := K) F)

def pairedSource (F : Type*) [Field F] :
    Tensor F (PairedWords (K := K) allocation dilation)
      (PairedWords (K := K) allocation dilation) (PairedWords (K := K) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : PopulationHistory K =>
    placedShapeChildProducts F (stageCDistinguished (cShapeParent h.1)) h.2
      (populationAtomCounts allocation dilation h))

def indexEquiv : (PopulationHistory K × Fin 4 × Bool) ≃ Index K where
  toFun h := ((h.1.1, h.2.1, h.2.2), h.1.2)
  invFun h := ((h.1.1, h.2), h.1.2.1, h.1.2.2)
  left_inv h := by rcases h with ⟨⟨h, phi⟩, b, r⟩; rfl
  right_inv h := by rcases h with ⟨⟨h, b, r⟩, phi⟩; rfl

def toRaw (x : GroupedWords (K := K) allocation dilation) : RawWords (K := K) allocation dilation :=
  fun h => x (h.1.1, h.2) h.1.2.1 h.1.2.2

theorem regroup_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : GroupedWords (K := K) allocation dilation) :
    source allocation dilation F ε (toRaw allocation dilation x)
      (toRaw allocation dilation y) (toRaw allocation dilation z) =
      groupedSource allocation dilation F x y z := by
  change (∏ h : Index K, historyTensor F allocation dilation ε (.afterC h.1, h.2)
    (toRaw allocation dilation x h) (toRaw allocation dilation y h)
      (toRaw allocation dilation z h)) = _
  rw [← (indexEquiv (K := K)).prod_comp]
  simp only [Fintype.prod_prod_type]
  simp only [indexEquiv, Equiv.coe_fn_mk, toRaw, historyTensor_afterC,
    groupedSource, AllFieldStageCRegroup.splitTensor, CommonDimensions.familyProduct, leaf, counts,
    Fintype.prod_prod_type]

def regroupMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (source (K := K) allocation dilation F ε)
      (groupedSource (K := K) allocation dilation F) where
  x := fun x s => if s = toRaw allocation dilation x then 1 else 0
  y := fun y s => if s = toRaw allocation dilation y then 1 else 0
  z := fun z s => if s = toRaw allocation dilation z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    exact regroup_coefficient allocation dilation F ε x y z

theorem leaf_pair (F : Type*) [Field F] (h : PopulationHistory K) (b : Fin 4) :
    Tensor.product (leaf F h b false) (leaf F h b true) =
      placedShapeChildProduct F (stageCDistinguished (cShapeParent h.1)) h.2 b := by
  rw [placedShapeChildProduct_eq_stageC F (cShapeParent h.1)
    (bShape_size h.1.1.val) h.1.1.property]
  rfl

theorem pairedSource_eq (F : Type*) [Field F] :
    AllFieldStageCRegroup.pairedTensor (counts (K := K) allocation dilation) (leaf (K := K) F) =
      pairedSource (K := K) allocation dilation F := by
  funext x y z
  dsimp only [AllFieldStageCRegroup.pairedTensor, pairedSource, placedShapeChildProducts,
    CommonDimensions.familyProduct]
  apply Finset.prod_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro p _
  exact congrFun (congrFun (congrFun (leaf_pair F h p.1) (x h p)) (y h p)) (z h p)

attribute [local irreducible] AllFieldHistory.population

def pairMap (F : Type*) [Field F] :
    LocalMap (groupedSource (K := K) allocation dilation F)
      (pairedSource (K := K) allocation dilation F) := by
  let M := pairLocalMap (F := F) (H := PopulationHistory K) (B := Fin 4) (W := SingleWord)
    (counts (K := K) allocation dilation)
    (counts_half (K := K) allocation dilation) (leaf (K := K) F)
  let N : LocalMap (groupedSource (K := K) allocation dilation F)
      (AllFieldStageCRegroup.pairedTensor (counts (K := K) allocation dilation) (leaf (K := K) F)) :=
    localMapWithFintypes_inline_MatrixMultiplication_AllFieldStageCFinish
      (X := GroupedWords (K := K) allocation dilation)
      (Y := GroupedWords (K := K) allocation dilation)
      (Z := GroupedWords (K := K) allocation dilation)
      (X' := PairedWords (K := K) allocation dilation)
      (Y' := PairedWords (K := K) allocation dilation)
      (Z' := PairedWords (K := K) allocation dilation) M
  exact ⟨N.x, N.y, N.z, N.coefficient.trans (pairedSource_eq (K := K) allocation dilation F)⟩

abbrev Rows := HistoryRowWords (populationSide (K := K)) (populationAtomCounts allocation dilation)
abbrev Middles := HistoryMiddleWords (populationSide (K := K)) (populationAtomCounts allocation dilation)
abbrev Columns := HistoryColumnWords (populationSide (K := K)) (populationAtomCounts allocation dilation)

def terminalMap (F : Type*) [Field F] :
    LocalMap (pairedSource (K := K) allocation dilation F)
      (Tensor.matrixCoefficients (Rows (K := K) allocation dilation)
        (Middles (K := K) allocation dilation) (Columns (K := K) allocation dilation)) := by
  let M := shapeHistoryMap (F := F) (H := PopulationHistory K)
    (fun h : PopulationHistory K => stageCDistinguished (cShapeParent h.1))
    (fun h => h.2) (populationAtomCounts allocation dilation)
  exact LocalMap.redecideMatrix (localMapWithFintypes_inline_MatrixMultiplication_AllFieldStageCFinish M) _ _ _

def finishMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (source (K := K) allocation dilation F ε)
      (Tensor.matrixCoefficients (Rows (K := K) allocation dilation)
        (Middles (K := K) allocation dilation) (Columns (K := K) allocation dilation)) :=
  (regroupMap allocation dilation F ε).comp
    ((pairMap allocation dilation F).comp (terminalMap allocation dilation F))

theorem volume_eq_populationVolume :
    Fintype.card (Rows (K := K) allocation dilation) *
      Fintype.card (Middles (K := K) allocation dilation) *
        Fintype.card (Columns (K := K) allocation dilation) =
      populationVolume (K := K) allocation dilation := by
  simp only [Rows, Middles, Columns, populationVolume, historyVolume,
    HistoryRowWords, HistoryMiddleWords, HistoryColumnWords, Fintype.card_pi]

end MatrixMultiplication.AllFieldStageCFinish

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldFinishedWitness

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldTerminalStatisticLaws AllFieldTerminalRates
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

def localMapWithFintypes_inline_MatrixMultiplication_AllFieldFinishedWitness {F : Type*} [Field F]
    {X Y Z X' Y' Z' : Type} [newX : Fintype X] [newY : Fintype Y] [newZ : Fintype Z]
    {oldX : Fintype X} {oldY : Fintype Y} {oldZ : Fintype Z}
    {T : Tensor F X Y Z} {Q : Tensor F X' Y' Z'}
    (M : @LocalMap F _ X Y Z X' Y' Z' oldX oldY oldZ T Q) :
    @LocalMap F _ X Y Z X' Y' Z' newX newY newZ T Q := by
  cases Subsingleton.elim oldX newX
  cases Subsingleton.elim oldY newY
  cases Subsingleton.elim oldZ newZ
  exact M

def matrixProductMap (F : Type*) [Field F]
    (A B C D E G : Type) [Fintype A] [Fintype B] [Fintype C]
    [Fintype D] [Fintype E] [Fintype G] :
    LocalMap (Tensor.product (Tensor.matrixCoefficients (K := F) A B C)
      (Tensor.matrixCoefficients D E G))
      (Tensor.matrixCoefficients (A × D) (B × E) (C × G)) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
    (fun y : (B × E) × (C × G) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
    (fun z : (C × G) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2))) _).symm.trans ?_⟩
  funext x y z
  exact Tensor.matrixCoefficients_product x y z

def combineMatrixMaps {F : Type*} [Field F]
    {X Y Z U V W A B C D E G : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype G]
    {T : Tensor F X Y Z} {Q : Tensor F U V W}
    (first : LocalMap T (Tensor.matrixCoefficients A B C))
    (second : LocalMap Q (Tensor.matrixCoefficients D E G)) :
    LocalMap (Tensor.product T Q)
      (Tensor.matrixCoefficients (A × D) (B × E) (C × G)) :=
  (first.product second).comp (matrixProductMap F A B C D E G)

variable {K : ℕ} (allocation : Allocation) (m : ℕ)

abbrev ZeroRows := ∀ h : TerminalZero K, AllFieldZeroFinish.Row allocation m h
abbrev ZeroMiddles := ∀ h : TerminalZero K, AllFieldZeroFinish.Middle allocation m h
abbrev ZeroColumns := ∀ h : TerminalZero K, AllFieldZeroFinish.Column allocation m h

abbrev Rows := AllFieldInitialZeroFinish.Rows (K := K) allocation (terminalDilation K m) ×
  (ZeroRows (K := K) allocation m ×
    AllFieldStageCFinish.Rows (K := K) allocation (terminalDilation K m))
abbrev Middles := AllFieldInitialZeroFinish.Middles (K := K) allocation (terminalDilation K m) ×
  (ZeroMiddles (K := K) allocation m ×
    AllFieldStageCFinish.Middles (K := K) allocation (terminalDilation K m))
abbrev Columns := AllFieldInitialZeroFinish.Columns (K := K) allocation (terminalDilation K m) ×
  (ZeroColumns (K := K) allocation m ×
    AllFieldStageCFinish.Columns (K := K) allocation (terminalDilation K m))

local instance initialRowsFintype :
    Fintype (AllFieldInitialZeroFinish.Rows (K := K) allocation (terminalDilation K m)) := by
  letI : DecidableEq (AllFieldInitialZeroFinish.Index K) := Classical.decEq _
  exact inferInstanceAs (Fintype (∀ h : AllFieldInitialZeroFinish.Index K,
    AllFieldInitialZeroFinish.RowIndex allocation (terminalDilation K m) h))

local instance initialMiddlesFintype :
    Fintype (AllFieldInitialZeroFinish.Middles (K := K) allocation (terminalDilation K m)) := by
  letI : DecidableEq (AllFieldInitialZeroFinish.Index K) := Classical.decEq _
  exact inferInstanceAs (Fintype (∀ h : AllFieldInitialZeroFinish.Index K,
    AllFieldInitialZeroFinish.MiddleIndex allocation (terminalDilation K m) h))

local instance initialColumnsFintype :
    Fintype (AllFieldInitialZeroFinish.Columns (K := K) allocation (terminalDilation K m)) := by
  letI : DecidableEq (AllFieldInitialZeroFinish.Index K) := Classical.decEq _
  exact inferInstanceAs (Fintype (∀ h : AllFieldInitialZeroFinish.Index K,
    AllFieldInitialZeroFinish.ColumnIndex allocation (terminalDilation K m) h))

local instance stageCRowsFintype :
    Fintype (AllFieldStageCFinish.Rows (K := K) allocation (terminalDilation K m)) := by
  exact inferInstanceAs (Fintype (∀ h : CWStageCProducts.PopulationHistory K,
    CWStageCProducts.RowWords (CWStageCProducts.populationSide h)
      (CWStageCProducts.populationAtomCounts allocation (terminalDilation K m) h)))

local instance stageCMiddlesFintype :
    Fintype (AllFieldStageCFinish.Middles (K := K) allocation (terminalDilation K m)) := by
  exact inferInstanceAs (Fintype (∀ h : CWStageCProducts.PopulationHistory K,
    CWStageCProducts.MiddleWords (CWStageCProducts.populationSide h)
      (CWStageCProducts.populationAtomCounts allocation (terminalDilation K m) h)))

local instance stageCColumnsFintype :
    Fintype (AllFieldStageCFinish.Columns (K := K) allocation (terminalDilation K m)) := by
  exact inferInstanceAs (Fintype (∀ h : CWStageCProducts.PopulationHistory K,
    CWStageCProducts.ColumnWords (CWStageCProducts.populationSide h)
      (CWStageCProducts.populationAtomCounts allocation (terminalDilation K m) h)))

local instance rowsFintype : Fintype (Rows (K := K) allocation m) :=
  inferInstanceAs (Fintype
    (AllFieldInitialZeroFinish.Rows (K := K) allocation (terminalDilation K m) ×
      (ZeroRows (K := K) allocation m ×
        AllFieldStageCFinish.Rows (K := K) allocation (terminalDilation K m))))

local instance middlesFintype : Fintype (Middles (K := K) allocation m) :=
  inferInstanceAs (Fintype
    (AllFieldInitialZeroFinish.Middles (K := K) allocation (terminalDilation K m) ×
      (ZeroMiddles (K := K) allocation m ×
        AllFieldStageCFinish.Middles (K := K) allocation (terminalDilation K m))))

local instance columnsFintype : Fintype (Columns (K := K) allocation m) :=
  inferInstanceAs (Fintype
    (AllFieldInitialZeroFinish.Columns (K := K) allocation (terminalDilation K m) ×
      (ZeroColumns (K := K) allocation m ×
        AllFieldStageCFinish.Columns (K := K) allocation (terminalDilation K m))))

local instance initialRawFintype :
    Fintype (AllFieldFinalState.InitialWords (K := K) allocation (terminalDilation K m)) :=
  inferInstanceAs (Fintype (∀ h : AllFieldFinalState.InitialIndex K,
    HistoryWord allocation (terminalDilation K m) (.initial h.1.val, h.2)))

local instance zeroRawFintype :
    Fintype (AllFieldFinalState.ZeroWords (K := K) allocation (terminalDilation K m)) :=
  inferInstanceAs (Fintype (∀ h : TerminalZero K,
    HistoryWord allocation (terminalDilation K m) (AllFieldTerminalStatisticLaws.history h)))

local instance stageCRawFintype :
    Fintype (AllFieldFinalState.CWords (K := K) allocation (terminalDilation K m)) :=
  inferInstanceAs (Fintype (∀ h : AllFieldFinalState.CIndex K,
    HistoryWord allocation (terminalDilation K m) (.afterC h.1, h.2)))

theorem zero_volume :
    Fintype.card (ZeroRows (K := K) allocation m) *
      Fintype.card (ZeroMiddles (K := K) allocation m) *
        Fintype.card (ZeroColumns (K := K) allocation m) = zeroVolume (K := K) allocation m := by
  simp only [ZeroRows, ZeroMiddles, ZeroColumns, Fintype.card_pi, zeroVolume]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun h _ => AllFieldZeroFinish.volume allocation m h

theorem volume_eq :
    Fintype.card (Rows (K := K) allocation m) *
      Fintype.card (Middles (K := K) allocation m) *
        Fintype.card (Columns (K := K) allocation m) = terminalVolume (K := K) allocation m := by
  simp only [Rows, Middles, Columns, Fintype.card_prod]
  calc
    _ = (Fintype.card (AllFieldInitialZeroFinish.Rows (K := K) allocation (terminalDilation K m)) *
          Fintype.card (AllFieldInitialZeroFinish.Middles (K := K) allocation (terminalDilation K m)) *
          Fintype.card (AllFieldInitialZeroFinish.Columns (K := K) allocation (terminalDilation K m))) *
        (Fintype.card (ZeroRows (K := K) allocation m) *
          Fintype.card (ZeroMiddles (K := K) allocation m) *
          Fintype.card (ZeroColumns (K := K) allocation m)) *
        (Fintype.card (AllFieldStageCFinish.Rows (K := K) allocation (terminalDilation K m)) *
          Fintype.card (AllFieldStageCFinish.Middles (K := K) allocation (terminalDilation K m)) *
          Fintype.card (AllFieldStageCFinish.Columns (K := K) allocation (terminalDilation K m))) := by ring
    _ = _ := by rw [AllFieldInitialZeroFinish.volume_eq, zero_volume,
      AllFieldStageCFinish.volume_eq_populationVolume]; rfl

theorem dimensions_pos :
    0 < Fintype.card (Rows (K := K) allocation m) ∧
      0 < Fintype.card (Middles (K := K) allocation m) ∧
        0 < Fintype.card (Columns (K := K) allocation m) := by
  have hp := terminalVolume_pos (K := K) allocation m
  rw [← volume_eq allocation m] at hp
  have hab := Nat.pos_of_mul_pos_right hp
  exact ⟨Nat.pos_of_mul_pos_right hab, Nat.pos_of_mul_pos_left hab,
    Nat.pos_of_mul_pos_left hp⟩

def zeroMap (F : Type*) [Field F] {ε : ℝ} (hm : 0 < m) (hε : 0 ≤ ε) :
    LocalMap (AllFieldFinalState.zeroTensor (K := K) allocation (terminalDilation K m) F ε)
      (Tensor.matrixCoefficients (ZeroRows (K := K) allocation m)
        (ZeroMiddles (K := K) allocation m) (ZeroColumns (K := K) allocation m)) := by
  let result := AllFieldTerminal.terminalProductMap
    (fun h : TerminalZero K => historyTensor F allocation (terminalDilation K m) ε
      (AllFieldTerminalStatisticLaws.history h))
    (fun h => AllFieldZeroFinish.Row allocation m h)
    (fun h => AllFieldZeroFinish.Middle allocation m h)
    (fun h => AllFieldZeroFinish.Column allocation m h)
    (fun h => LocalMap.redecideMatrix
      (AllFieldZeroFinish.localMap F allocation hm hε h) _ _ _)
  let aligned := localMapWithFintypes_inline_MatrixMultiplication_AllFieldFinishedWitness (F := F)
    (X := AllFieldFinalState.ZeroWords (K := K) allocation (terminalDilation K m))
    (Y := AllFieldFinalState.ZeroWords (K := K) allocation (terminalDilation K m))
    (Z := AllFieldFinalState.ZeroWords (K := K) allocation (terminalDilation K m))
    (newX := inferInstance) (newY := inferInstance) (newZ := inferInstance) result
  exact LocalMap.redecideMatrix aligned _ _ _

def terminalMap (F : Type*) [Field F] {ε : ℝ} (hm : 0 < m) (hε : 0 ≤ ε) :
    LocalMap (stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))
      (Tensor.matrixCoefficients (Rows (K := K) allocation m)
        (Middles (K := K) allocation m) (Columns (K := K) allocation m)) := by
  let initialAligned := localMapWithFintypes_inline_MatrixMultiplication_AllFieldFinishedWitness (F := F)
    (X := AllFieldInitialZeroFinish.RawWords (K := K) allocation (terminalDilation K m))
    (Y := AllFieldInitialZeroFinish.RawWords (K := K) allocation (terminalDilation K m))
    (Z := AllFieldInitialZeroFinish.RawWords (K := K) allocation (terminalDilation K m))
    (newX := inferInstance) (newY := inferInstance) (newZ := inferInstance)
    (AllFieldInitialZeroFinish.finishMap (K := K) allocation (terminalDilation K m) F ε)
  let initial := LocalMap.redecideMatrix initialAligned
    (Classical.decEq _) (Classical.decEq _) (Classical.decEq _)
  let zeros := LocalMap.redecideMatrix (zeroMap (K := K) allocation m F hm hε)
    (Classical.decEq _) (Classical.decEq _) (Classical.decEq _)
  let interior := LocalMap.redecideMatrix
    (AllFieldStageCFinish.finishMap (K := K) allocation (terminalDilation K m) F ε)
    (Classical.decEq _) (Classical.decEq _) (Classical.decEq _)
  let second := LocalMap.redecideMatrix
    (combineMatrixMaps zeros interior)
    (Classical.decEq _) (Classical.decEq _) (Classical.decEq _)
  let third := combineMatrixMaps initial second
  exact LocalMap.redecideMatrix
    ((AllFieldFinalState.map (K := K) allocation (terminalDilation K m) F ε).comp third) _ _ _

variable {F : Type*} [Field F] {ε : ℝ} {I : Type} [Fintype I]

def execution (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2)))) :
    Execution (cwSource F K (terminalLength allocation K m))
      (AllFieldSource.matrixTarget F (Fintype.card (Rows (K := K) allocation m))
        (Fintype.card (Middles (K := K) allocation m))
        (Fintype.card (Columns (K := K) allocation m)) (Fintype.card I)) :=
  (E.restrict _ ((terminalMap allocation m F hm hε).parallelCopies I)).restrict _
    (LocalMap.ofExists (TerminalRelabel.directSum_matrix_restrict_fin (K := F)
      I (Rows (K := K) allocation m) (Middles (K := K) allocation m)
        (Columns (K := K) allocation m)))

def witness (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))))
    (hI : 0 < Fintype.card I) : AllFieldWitness F :=
  (execution allocation m hm hε E).toWitness
    (dimensions_pos allocation m).1 (dimensions_pos allocation m).2.1
    (dimensions_pos allocation m).2.2 hI

@[simp] theorem witness_volume (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))))
    (hI : 0 < Fintype.card I) :
    (witness allocation m hm hε E hI).volume = terminalVolume (K := K) allocation m :=
  volume_eq allocation m

@[simp] theorem witness_multiplicity (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))))
    (hI : 0 < Fintype.card I) :
    (witness allocation m hm hε E hI).multiplicity = Fintype.card I := rfl

@[simp] theorem witness_rankBound (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))))
    (hI : 0 < Fintype.card I) :
    (witness allocation m hm hε E hI).rankBound =
      AllFieldSource.rankBudget E.Copies K (terminalLength allocation K m) := rfl

end MatrixMultiplication.AllFieldFinishedWitness

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldConstructionData

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ}

structure Data (allocation : Allocation) (dilation : ℕ) (width slack : ℝ) where
  initial : AllFieldInitialChoice.Choice (K := K) allocation dilation slack
  groups : AllFieldHistoryIteration.ScheduleChoices
    (K := K) allocation dilation width slack
  threshold : ∀ t : Fin (K + 2),
    AllFieldHistoryRecovery.minimumDilation (K := K) (tick := t.val) allocation width ≤ dilation

variable (allocation : Allocation) (dilation : ℕ) (width slack : ℝ)

abbrev Tags (data : Data (K := K) allocation dilation width slack) :=
  AllFieldHistoryIteration.Tags allocation dilation width slack
    (AllFieldInitialChoice.Tags allocation dilation slack data.initial) data.groups

instance tagsFintype (data : Data (K := K) allocation dilation width slack) :
    Fintype (Tags allocation dilation width slack data) := inferInstance

theorem card_tags (data : Data (K := K) allocation dilation width slack) :
    Fintype.card (Tags allocation dilation width slack data) =
      Fintype.card (AllFieldConstructionRates.SelectedLabels
        (K := K) allocation slack dilation) := by
  rw [AllFieldHistoryIteration.card_tags, AllFieldInitialChoice.card_tags,
    AllFieldConstructionRates.card_selected]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  apply Finset.prod_congr rfl
  intro sigma _
  exact (AllFieldConstructionRates.groupCount_eq_native allocation slack dilation t sigma).symm

end MatrixMultiplication.AllFieldConstructionData

end
end

end MatrixAllFields

end OAI
end


