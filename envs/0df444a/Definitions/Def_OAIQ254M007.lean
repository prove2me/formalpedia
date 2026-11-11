-- Prove2me | Definitions.Def_OAIQ254M007
-- name    : OAIQ254M007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:53:11.593149+00:00
-- url     : https://prove2.me/theorems/267510e3-2783-4e52-86e4-acae3f049413
-- title:
--   Definitions bundle OAIQ254M007 of the split of OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1544 declarations of OpenAI's Lean: 1376 definitions, 1 inductive type or structure, 3 instances and 164 theorems. The definitions and types are `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.execution`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionFamily.yieldRate`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionRates.Copies`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupAssignmentRetention.assigned`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupAssignmentRetention.physicalAssignment`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupCompatibilityTransfer.halfLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupCompatibilityTransfer.halfShape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupCountRate.nativeCompatibilityRate`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeEnvelope.uniformDegree`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeEnvelope.variableDegree`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeLaws.nativeCount`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeLaws.nativeLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.maxNativeDegree`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.nativePairLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitPrefactor`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualKeep`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairEntropy.observedEntropy`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.Positions`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.base`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.classMass`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.pairCounts`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.parentBase`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.parentPair`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.parentStatistic`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.q`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.windowFactor`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.branchConditionalCost`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.branchHalfLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.maskedBranchMass`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupSelection.orbitPrefactor`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.canonicalActiveEquivOrder`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryGroupMasks.groupPreparedSource`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryGroupMasks.groupRawSource`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.incomingWord`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.received`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.stageCWeights`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.execution`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.run`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.passes` and 1337 more.
--
--   **Sources.** They come from these modules of lean/OAI/LinearAlgebra, in whole or in part: `MatrixFields_CapacityA_CapA1_1_14I1`, `MatrixFields_CapacityA_CapA1_1_14I2`, `MatrixFields_CapacityA_CapA1_2_13I1`, `MatrixFields_CapacityA_CapA1_2_13I2`, `MatrixFields_CapacityA_CapA1_3_12I1`, `MatrixFields_CapacityA_CapA1_3_12I2`, `MatrixFields_CapacityA_CapA1_4_11I1`, `MatrixFields_CapacityA_CapA1_4_11I2`, `MatrixFields_CapacityA_CapA1_5_10I1`, `MatrixFields_CapacityA_CapA1_5_10I2`, `MatrixFields_CapacityA_CapA1_5_10I2Pair`, `MatrixFields_CapacityA_CapA1_6_9I0`, `MatrixFields_CapacityA_CapA1_6_9I1`, `MatrixFields_CapacityA_CapA1_6_9I1Pair`, `MatrixFields_CapacityA_CapA1_6_9I2`, `MatrixFields_CapacityA_CapA1_6_9I2Pair`, `MatrixFields_CapacityA_CapA1_7_8I0`, `MatrixFields_CapacityA_CapA1_7_8I1`, `MatrixFields_CapacityA_CapA1_7_8I1Pair`, `MatrixFields_Certificates_Four0_3_5`, `MatrixFields_Certificates_Four0_4_4`, `MatrixFields_Certificates_Four0_5_3`, `MatrixFields_Certificates_Four0_7_1`, `MatrixFields_Certificates_Four0_8_0`, `MatrixFields_Certificates_Four1_0_7`, `MatrixFields_Certificates_Four1_7_0`, `MatrixFields_Certificates_Four2_0_6`, `MatrixFields_Certificates_Four2_6_0`, `MatrixFields_Certificates_Four3_0_5`, `MatrixFields_Certificates_Four3_5_0`, `MatrixFields_Certificates_Four4_0_4`, `MatrixFields_Certificates_Four4_4_0`, `MatrixFields_Certificates_Four5_0_3`, `MatrixFields_Certificates_Four5_3_0`, `MatrixFields_Certificates_Four6_0_2`, `MatrixFields_Certificates_Four6_2_0`, `MatrixFields_Certificates_Four7_0_1`, `MatrixFields_Certificates_Four7_1_0`, `MatrixFields_Certificates_Four8_0_0`, `MatrixFields_Certificates_LittleB1_3_4`, `MatrixFields_Certificates_LittleB1_4_3`, `MatrixFields_Certificates_LittleB1_5_2`, `MatrixFields_Certificates_LittleB2_3_3`, `MatrixFields_Certificates_LittleB2_5_1`, `MatrixFields_Certificates_NativeInterior`, `MatrixFields_Certificates_SplitA1_3_12`, `MatrixFields_Certificates_SplitB1_1_6`, `MatrixFields_Certificates_SupportedContraction`, `MatrixFields_Certificates_Terminal1_6_1`, `MatrixFields_Certificates_Terminal2_1_5`, `MatrixFields_Certificates_Terminal2_2_4`, `MatrixFields_Certificates_Terminal2_4_2`, `MatrixFields_Certificates_Terminal3_1_4`, `MatrixFields_Certificates_Terminal3_3_2`, `MatrixFields_Certificates_Terminal3_4_1`, `MatrixFields_Certificates_Terminal4_1_3`, `MatrixFields_Certificates_Terminal4_2_2`, `MatrixFields_Certificates_Terminal4_3_1`, `MatrixFields_Certificates_Terminal5_2_1`, `MatrixFields_Certificates_Zero0_1_7`, `MatrixFields_Construction_GroupAssignmentRetention`, `MatrixFields_Construction_GroupAssignments`, `MatrixFields_Construction_GroupDegreeEnvelope`, `MatrixFields_Construction_GroupNativeDegreeBound`, `MatrixFields_Construction_JointCanonicalMixed`, `MatrixFields_Construction_JointCanonicalSymmetry`, `MatrixFields_Construction_JointMaskedAssignment`, `MatrixFields_Construction_OrderedLimits`, `MatrixFields_Construction_Subdivision`, `MatrixFields_Entropy_ConstructionRates`, `MatrixFields_Entropy_GroupBranchLaws`, `MatrixFields_Entropy_GroupCountRate`, `MatrixFields_Entropy_GroupPairEntropy`, `MatrixFields_Entropy_GroupProjectedEntropy`, `MatrixFields_Entropy_InitialLeafRates`, `MatrixFields_Entropy_NativeLaws`, `MatrixFields_Entropy_ParametersHalfLaws`, `MatrixFields_Entropy_RateLimit`, `MatrixFields_Entropy_StageCTerminalRates`, `MatrixFields_Extraction_ConstructionLabels`, `MatrixFields_Extraction_GroupPairWindows`, `MatrixFields_Extraction_GroupSelection`, `MatrixFields_Histories_CWShapePhysicalPermutation`, `MatrixFields_Histories_GroupOrbitCount`, `MatrixFields_Histories_GroupOrbitTransport`, `MatrixFields_Histories_HistoryChildLaws`, `MatrixFields_Histories_HistoryGroupCore`, `MatrixFields_Histories_HistoryIteration`, `MatrixFields_Histories_HistoryRecovery`, `MatrixFields_Histories_HistoryRecoveryBudget`, `MatrixFields_Histories_HistorySourceAssignment`, `MatrixFields_Histories_InheritedMaskMargins`, `MatrixFields_Histories_InverseLinearRecovery`, `MatrixFields_Histories_JointScalarOrbitAdmissibility`, `MatrixFields_Histories_ScheduledPositivity`, `MatrixFields_Histories_ZeroHistorySums`, `MatrixFields_Parameters_GroupStatisticComplement`, `MatrixFields_Parameters_NativeCapacity`, `MatrixFields_Tensors_CWCompleteStatistics`, `MatrixFields_Tensors_CWStageCPlacements`, `MatrixFields_Tensors_CWStageCStatistics`, `MatrixFields_Tensors_CWStrandCompatibility`, `MatrixFields_Tensors_JointPopulationCWNonzero`.
--
--   **Imports.** It imports the bundles `OAIQ254M002`, `OAIQ254M003` and `OAIQ254M004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ254M012`; the statements `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionFamily.fixed_allocation_constraint`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.nativeCompatibilityRate_eq`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_2_5Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_6_1Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_1_5Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_2_4Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_1_4Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_2_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_3_1Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_2_1Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.halfTable_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeBBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeS1Ball_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeS2Ball_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeTBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_denominator_gap`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_sharp_rate_bound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_stageC_balanced_positive`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_stageC_feasible` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_volume_positive`; the proofs of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionFamily.fixed_allocation_constraint`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.nativeCompatibilityRate_eq`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_2_5Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_6_1Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_1_5Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_2_4Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_1_4Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_2_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_3_1Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_2_1Half_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_1_14I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_5_3H2H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.halfTable_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeBBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeS1Ball_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeS2Ball_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeTBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_denominator_gap`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_sharp_rate_bound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_stageC_balanced_positive`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_stageC_feasible` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_volume_positive`.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/LinearAlgebra at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M004

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ParametersHalfLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.canonicalChildShape_branchShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.decode_encodePhysicalShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.decode_encodeShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodePhysicalShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodeShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodeShape_total _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.physicalShape_complement _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.physicalShape_source _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldPairMarginals.halfWeightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

theorem halfLaw_nonnegative (t : Shape) (w : Fin 3) (ij : PairSlot) :
    0 ≤ halfLaw t w ij := by
  unfold halfLaw
  split_ifs
  · exact positiveHalfLaw_nonnegative t w ij
  · norm_num
  · exact le_rfl
  · exact zeroPairLaw_nonnegative t ij.1 ij.2
  · exact zeroPairLaw_nonnegative t (kappa ij.1) (kappa ij.2)

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InverseLinearRecovery
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

theorem repair_inverse_linear
    {K G X Y Z : Type*} [CommSemiring K] [Group G] [Fintype G]
    [MulAction G X] [MulAction G Y] [MulAction G Z]
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (Q : Tensor K X Y Z)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (hpreserve : ∀ (g : G) x y z, Q (g • x) (g • y) (g • z) = Q x y z)
    {b C : ℝ} {N : ℕ} (hb : 0 ≤ b) (hC : 0 < C) (hN : 3 * C < (N : ℝ))
    (hsupport : ((@Finset.filter (X × Y × Z)
      (fun p => Q p.1 p.2.1 p.2.2 ≠ 0) (Classical.decPred _) Finset.univ).card : ℝ) ≤
      Real.exp (b * N))
    (hx : ∀ x, (∃ y z, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) x).filter fun v => ¬px v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) x).card ≤ C / N)
    (hy : ∀ y, (∃ x z, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) y).filter fun v => ¬py v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) y).card ≤ C / N)
    (hz : ∀ z, (∃ x y, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) z).filter fun v => ¬pz v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) z).card ≤ C / N) :
    RecoveredBy Q (ExactRecovery.delete Q px py pz) (RecoveryGrowth.shiftCount b C N) := by
  classical
  apply OrbitRecovery.repair_from_orbit_loss Q px py pz hpreserve (C / N) hx hy hz
    (RecoveryGrowth.shiftCount b C N) (RecoveryGrowth.shiftCount_pos hb hC hN)
  apply RecoveryGrowth.cardinal_budget hC hN Fintype.card_pos hsupport
  simpa only [mul_div_assoc] using
    OrbitRecovery.floor_loss_fraction (G := G) (C / N)
      (div_nonneg hC.le (Nat.cast_nonneg N))

end MatrixMultiplication.InverseLinearRecovery

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InheritedMaskMargins
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
open MatrixMultiplication.PermutationMatching
open MatrixMultiplication.InheritedMasks

namespace MatrixMultiplication.HistorySymmetry

variable {C : Type*} {P X Y : C → Type*}

section Coefficients

variable {K : Type*} [CommSemiring K] [Fintype C] [∀ c, Fintype (P c)]
    {XL YL ZL XR YR ZR : C → Type*}

theorem pairClassProduct_smul
    (TL : ∀ c, Tensor K (XL c) (YL c) (ZL c))
    (TR : ∀ c, Tensor K (XR c) (YR c) (ZR c))
    (g : HalfClassPermutations P)
    (x : CompleteWordPair P XL XR) (y : CompleteWordPair P YL YR)
    (z : CompleteWordPair P ZL ZR) :
    pairClassProduct TL TR (g • x) (g • y) (g • z) = pairClassProduct TL TR x y z := by
  change classProduct TL (fun c => x.left c ∘ (g.1 c).symm)
      (fun c => y.left c ∘ (g.1 c).symm) (fun c => z.left c ∘ (g.1 c).symm) *
    classProduct TR (fun c => x.right c ∘ (g.2 c).symm)
      (fun c => y.right c ∘ (g.2 c).symm) (fun c => z.right c ∘ (g.2 c).symm) = _
  rw [classProduct_permutation, classProduct_permutation]
  rfl

end Coefficients

section Windows

variable [Fintype C] [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
    {SL SR : C → Type*} [∀ c, Fintype (SL c)] [∀ c, Fintype (SR c)]
    [∀ c, DecidableEq (SL c)] [∀ c, DecidableEq (SR c)]

omit [Fintype C] [∀ c, DecidableEq (P c)] [∀ c, Fintype (SL c)]
  [∀ c, Fintype (SR c)] in
theorem childWindows_smul
    (sl : ∀ c, X c → SL c) (sr : ∀ c, Y c → SR c)
    (νl : ∀ c, SL c → ℝ) (νr : ∀ c, SR c → ℝ) (ηl ηr : C → ℝ)
    (g : HalfClassPermutations P) (w : CompleteWordPair P X Y) :
    childWindows sl sr νl νr ηl ηr (g • w) ↔ childWindows sl sr νl νr ηl ηr w := by
  unfold childWindows
  change (∀ c, typeWindow (νl c) (ηl c) ((sl c ∘ w.left c) ∘ (g.1 c).symm) ∧
    typeWindow (νr c) (ηr c) ((sr c ∘ w.right c) ∘ (g.2 c).symm)) ↔ _
  simp only [typeWindow_permutation]

end Windows

end MatrixMultiplication.HistorySymmetry

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointMaskedAssignment
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.branchPositionEquiv_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodePhysicalShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodeShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.initialExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.terminalExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.sidePermutation_refl _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.retarget_copies
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

omit [Fintype H] [DecidableEq H] in
theorem activeLaw_of_pos {S : H → Type*}
    (ν : ∀ c : ClassKey (H := H), S c.1 → ℝ) (c : ClassKey (H := H))
    (hc : 0 < counts c.1 c.2) : activeLaw counts ν c = ν c := by
  funext a
  simp [activeLaw, hc]

omit [Fintype H] [DecidableEq H] in
theorem rawWindows_iff_childWindows (e : Target counts) (w : RawPairs counts L R) :
    rawWindows counts L R sl sr νl νr ηl ηr e w ↔
      childWindows sl sr (activeLaw counts νl) (activeLaw counts νr)
        (activeWidth counts ηl) (activeWidth counts ηr) (pairEquiv counts L R e w) := by
  unfold rawWindows childWindows
  conv_rhs => rw [Prod.forall]
  apply forall_congr'
  intro h
  apply forall_congr'
  intro u
  by_cases hp : 0 < counts h u
  · simp only [hp, true_implies, activeLaw_of_pos counts _ (h, u) hp,
      activeWidth]
    change (_ ∧ _) ↔
      (typeWindow (νl (h, u)) (ηl (h, u))
        ((fun i : Class counts e h u => sl (h, u) (w h i.val).1) ∘
          (fiberEquiv counts e h u).symm) ∧
      typeWindow (νr (h, u)) (ηr (h, u))
        ((fun i : Class counts e h u => sr (h, u) (w h i.val).2) ∘
          (fiberEquiv counts e h u).symm))
    rw [typeWindow_reindex, typeWindow_reindex]
  · have hn : counts h u = 0 := Nat.eq_zero_of_not_pos hp
    simp only [hp, false_implies, true_iff]
    simp only [activeLaw, activeWidth, typeWindow, empiricalLaw, ClassPositions,
      Fintype.card_fin, hn, Nat.cast_zero, div_zero]
    simp

end Windows

section Coefficients

variable {F : Type*} [CommSemiring F]
    (T : ∀ h, Tensor F (L h × R h) (L h × R h) (L h × R h))
    (coarse : Fin 3 → ∀ h, L h × R h → Fin 17)

def coarseIdeal (e : Target counts) : Tensor F (RawPairs counts L R)
    (RawPairs counts L R) (RawPairs counts L R) :=
  ExactRecovery.delete (sourceTensor counts L R T)
    (coarseMask counts L R coarse 0 e) (coarseMask counts L R coarse 1 e)
    (coarseMask counts L R coarse 2 e)

omit [DecidableEq H] in
theorem coarseIdeal_eq_canonicalBase (e : Target counts) (x y z : RawPairs counts L R) :
    coarseIdeal counts L R T coarse e x y z = canonicalBase counts L R T coarse
      (pairEquiv counts L R e x) (pairEquiv counts L R e y) (pairEquiv counts L R e z) := by
  unfold canonicalBase
  rw [product_pack counts L R e (fun h u => block L R T coarse (h, u))]
  simp [block, Fintype.prod_ite_zero, coarseIdeal, ExactRecovery.delete,
    sourceTensor, classProduct, coarseMask, shapeSide, Fin.isValue, ↓reduceIte,
    forall_and]

section ChildWindows

variable {SL SR : H → Type*}
    [∀ h, Fintype (SL h)] [∀ h, Fintype (SR h)]
    [∀ h, DecidableEq (SL h)] [∀ h, DecidableEq (SR h)]
    (sl : Fin 3 → ∀ c : ClassKey (H := H), L c.1 → SL c.1)
    (sr : Fin 3 → ∀ c : ClassKey (H := H), R c.1 → SR c.1)
    (νl : Fin 3 → ∀ c : ClassKey (H := H), SL c.1 → ℝ)
    (νr : Fin 3 → ∀ c : ClassKey (H := H), SR c.1 → ℝ)
    (ηl ηr : Fin 3 → ClassKey (H := H) → ℝ)

def ideal (e : Target counts) : Tensor F (RawPairs counts L R)
    (RawPairs counts L R) (RawPairs counts L R) :=
  ExactRecovery.delete (coarseIdeal counts L R T coarse e)
    (rawWindows counts L R (sl 0) (sr 0) (νl 0) (νr 0) (ηl 0) (ηr 0) e)
    (rawWindows counts L R (sl 1) (sr 1) (νl 1) (νr 1) (ηl 1) (ηr 1) e)
    (rawWindows counts L R (sl 2) (sr 2) (νl 2) (νr 2) (ηl 2) (ηr 2) e)

omit [DecidableEq H] in
theorem ideal_eq_canonicalIdeal (e : Target counts)
    (x y z : RawPairs counts L R) :
    ideal counts L R T coarse sl sr νl νr ηl ηr e x y z =
      canonicalIdeal counts L R T coarse sl sr νl νr ηl ηr
        (pairEquiv counts L R e x) (pairEquiv counts L R e y)
        (pairEquiv counts L R e z) := by
  simp only [ideal, canonicalIdeal, ExactRecovery.delete, rawWindows_iff_childWindows,
    coarseIdeal_eq_canonicalBase]

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
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section





noncomputable section

namespace MatrixMultiplication.CWCompatibilityTransfer

open MatrixMultiplication.Foundation CWLeafRestrictions InheritedMasks
open scoped BigOperators

theorem zeroY_word_match {F : Type*} [CommRing F] {n : ℕ}
    (x y z : Fin n → Fin 7)
    (h : Tensor.power (FieldCW.tensor F 5) n x y z ≠ 0)
    (hy : wordWeight y = 0) : z = wordComplement x := by
  funext i
  have hi := site_nonzero x y z h i
  rw [wordWeight_zero y hy i] at hi
  have heq : FieldCW.tensor F 5 (x i) 0 (z i) =
      if x i = complement 5 (z i) then 1 else 0 := by
    simpa only [complement_involution] using
      tensor_middle_zero_matching F 5 (x i) (complement 5 (z i))
  have hxz : x i = complement 5 (z i) := by
    by_contra hn
    rw [heq, ite_eq_right hn] at hi
    exact hi rfl
  have hh := congrArg (complement 5) hxz
  simpa only [wordComplement, complement_involution] using hh.symm

theorem zeroZ_word_match {F : Type*} [CommRing F] {n : ℕ}
    (x y z : Fin n → Fin 7)
    (h : Tensor.power (FieldCW.tensor F 5) n x y z ≠ 0)
    (hz : wordWeight z = 0) : y = wordComplement x := by
  funext i
  have hi := site_nonzero x y z h i
  rw [wordWeight_zero z hz i] at hi
  have heq : FieldCW.tensor F 5 (x i) (y i) 0 =
      if x i = complement 5 (y i) then 1 else 0 := by
    simpa only [complement_involution] using
      tensor_last_zero_matching F 5 (x i) (complement 5 (y i))
  have hxy : x i = complement 5 (y i) := by
    by_contra hn
    rw [heq, ite_eq_right hn] at hi
    exact hi rfl
  have hh := congrArg (complement 5) hxy
  simpa only [wordComplement, complement_involution] using hh.symm

theorem transfer_window {P A : Type*} [Fintype P] [DecidableEq P]
    [Fintype A] [DecidableEq A] {n : ℕ}
    (statistic : (Fin n → Fin 7) → A) (κ : A ≃ A)
    (hstatistic : ∀ w, statistic (wordComplement w) = κ (statistic w))
    (x y : P → (Fin n → Fin 7)) (hmatch : ∀ i, y i = wordComplement (x i))
    (ν : A → ℝ) (η : ℝ)
    (hx : typeWindow ν η (fun i => statistic (x i))) :
    typeWindow (ν ∘ κ.symm) η (fun i => statistic (y i)) := by
  have heq : (fun i => statistic (y i)) = κ ∘ (fun i => statistic (x i)) := by
    funext i
    rw [hmatch i, hstatistic]
    rfl
  rw [heq]
  exact (typeWindow_equiv ν η (fun i => statistic (x i)) κ).mpr hx

end MatrixMultiplication.CWCompatibilityTransfer






namespace MatrixMultiplication.CWCoarseIndices

open MatrixMultiplication.Foundation CWStrands
open scoped BigOperators

theorem split_coarse_support {F P Q : Type*} [CommRing F] [Fintype P] [Fintype Q]
    (hP : Fintype.card P ≤ 8) (g : Fin 3 → ℕ)
    (x : (P → Fin 7) × (Q → Fin 7))
    (y : (P → Fin 7) × (Q → Fin 7))
    (z : (P → Fin 7) × (Q → Fin 7))
    (h : shapeTensor (F := F) (P ⊕ Q) g (Sum.elim x.1 x.2)
      (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) ≠ 0) :
    ((coarseIndex hP x.1).val + (coarseIndex hP y.1).val +
        (coarseIndex hP z.1).val = 2 * Fintype.card P) ∧
      (coarseIndex hP x.1).val ≤ g 0 ∧ (coarseIndex hP y.1).val ≤ g 1 ∧
        (coarseIndex hP z.1).val ≤ g 2 := by
  have hshape := shapeTensor_support g _ _ _ h
  have ht : strand (F := F) (P ⊕ Q) (Sum.elim x.1 x.2)
      (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) ≠ 0 := by
    simpa only [shapeTensor, ite_eq_left hshape] using h
  rw [strand_sum_elim, Tensor.product] at ht
  have hl : strand (F := F) P x.1 y.1 z.1 ≠ 0 := by
    intro he
    exact ht (by rw [he, zero_mul])
  refine ⟨strand_coarse_support hP x.1 y.1 z.1 hl, ?_, ?_, ?_⟩
  · have hs := hshape.1
    rw [weight_sum_elim] at hs
    exact hs ▸ Nat.le_add_right (weight x.1) (weight x.2)
  · have hs := hshape.2.1
    rw [weight_sum_elim] at hs
    exact hs ▸ Nat.le_add_right (weight y.1) (weight y.2)
  · have hs := hshape.2.2
    rw [weight_sum_elim] at hs
    exact hs ▸ Nat.le_add_right (weight z.1) (weight z.2)

end MatrixMultiplication.CWCoarseIndices






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryChildLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.nativeSplitWeightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.half_unhalfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.unhalf_halfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.choiceAt_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
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

def boundaryDeficit (a b c : Capacity) (full : ℝ) : ℝ :=
  2 * full - minCapacity a - minCapacity (fun i => a i + b i) -
    minCapacity (fun i => b i + c i) - minCapacity c

end MatrixMultiplication.Staggering

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

def canonicalActiveEquivOrder (K tick : ℕ) (sigma : Placement) :
    CanonicalActive K tick ≃ ActiveOrder K tick sigma where
  toFun w := ⟨⟨(w.val, w.val.priority.symm.trans sigma), w.property⟩, by
    change w.val.priority.trans (w.val.priority.symm.trans sigma) = sigma
    ext i
    simp⟩
  invFun w := ⟨w.val.val.1, w.val.property⟩
  left_inv _ := rfl
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hw : w.val.val.1.priority.trans w.val.val.2 = sigma := w.property
      apply Equiv.ext
      intro i
      have hh := Equiv.congr_fun hw (w.val.val.1.priority.symm i)
      simpa using hh.symm

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

theorem Work.childLaw_nonnegative {K : ℕ} (w : Work K) (u : Shape)
    (side : Fin 3) (a : w.Statistic) : 0 ≤ w.childLaw u side a := by
  cases w with
  | stageA h => exact halfLaw_nonnegative u side a
  | stageB h => exact littleLaw_nonnegative (aShape h.val) u side a
  | stageC h => exact zero_le_one

theorem Work.childLaw_normalized {K : ℕ} (w : Work K) (u : Shape)
    (hu : u ∈ shapes (2 * w.halfLength)) (side : Fin 3) :
    ∑ a : w.Statistic, w.childLaw u side a = 1 := by
  cases w with
  | stageA h => exact halfLaw_normalized u hu side
  | stageB h => exact littleLaw_normalized (aShape h.val) u side
  | stageC h =>
      change (∑ _ : PUnit, (1 : ℚ)) = 1
      simp

theorem Work.halfShape_mem {K : ℕ} (w : Work K) (b : w.Branch) (right : Bool) :
    halfShape w.parentShape (w.splitShape b) right ∈ shapes (2 * w.halfLength) := by
  cases w with
  | stageA h => exact aShape_size ⟨h, b, right⟩
  | stageB h => exact bShape_size ⟨h, b, right⟩
  | stageC h =>
      have hi := stageCAtom_mem (cShapeParent h) (bShape_size h.1.val) h.1.property b
      have hs := stageC_children_geometry (cShapeParent h)
        (bShape_size h.1.val) h.1.property (stageCAtom (cShapeParent h) b)
        hi
      have ht : shapeTotal (cShapeParent h) = 4 := mem_shapes_total (bShape_size h.1.val)
      cases right
      · change stageCAtom (cShapeParent h) b ∈ shapes 2
        simpa only [ht, Nat.reduceDiv] using below_mem_shapes hi
      · change complement (cShapeParent h) (stageCAtom (cShapeParent h) b) ∈ shapes 2
        simpa only [ht, Nat.reduceDiv] using below_mem_shapes hs.1

theorem placedChildLawRat_nonnegative {K : ℕ} (w : PlacedWork K)
    (u : JointPopulation.Shape) (side : Fin 3) (right : Bool) (a : w.1.Statistic) :
    0 ≤ placedChildLawRat w u side right a :=
  w.1.childLaw_nonnegative _ _ a

theorem placedChildLawRat_normalized_of_pos {K : ℕ} (allocation : Allocation)
    (dilation : ℕ) (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : 0 < jointCounts allocation dilation w u) (side : Fin 3) (right : Bool) :
    ∑ a : w.1.Statistic, placedChildLawRat w u side right a = 1 := by
  obtain ⟨b, rfl, _⟩ := shapeCounts_positive _ _ u hu
  simp only [placedChildLawRat_branchShape]
  exact w.1.childLaw_normalized _ (w.1.halfShape_mem b right) _

theorem rightClassChildLaw_nonnegative {K tick : ℕ} (side : Fin 3)
    (c : Active K tick × JointPopulation.Shape) (a : ActiveStatistic c.1) :
    0 ≤ rightClassChildLaw side c a := by
  change (0 : ℝ) ≤ (placedChildLawRat c.1.val c.2 side true a : ℝ)
  exact_mod_cast placedChildLawRat_nonnegative c.1.val c.2 side true a

theorem rightClassChildLaw_normalized_of_pos {K tick : ℕ} (allocation : Allocation)
    (dilation : ℕ) (side : Fin 3) (c : Active K tick × JointPopulation.Shape)
    (hc : 0 < activeCounts allocation dilation c.1 c.2) :
    ∑ a : ActiveStatistic c.1, rightClassChildLaw side c a = 1 := by
  change (∑ a : c.1.val.1.Statistic,
    (placedChildLawRat c.1.val c.2 side true a : ℝ)) = 1
  exact_mod_cast placedChildLawRat_normalized_of_pos allocation dilation
    c.1.val c.2 hc side true

end MatrixMultiplication.AllFieldHistory

namespace MatrixMultiplication.AllFieldHistoryChildLaws

open AllFieldHistory
open scoped BigOperators

theorem rightLaw_nonnegative {K tick : ℕ} (h : Active K tick) (u : JointPopulation.Shape)
    (side : Fin 3) (a : Statistic h) : 0 ≤ rightLaw h u side a :=
  rightClassChildLaw_nonnegative side (h, u) a

theorem rightLaw_normalized {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation dilation h u) (side : Fin 3) :
    ∑ a : Statistic h, rightLaw h u side a = 1 :=
  rightClassChildLaw_normalized_of_pos allocation dilation side (h, u) hu

end MatrixMultiplication.AllFieldHistoryChildLaws

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCanonicalMixed
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.branchPositionEquiv_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodePhysicalShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodeShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.initialExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.terminalExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.sidePermutation_refl _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCoarseReorder.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.retarget_copies
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

def childRight (c : ClassKey (H := H)) :
    Tensor F (Right rightLength c.1) (Right rightLength c.1) (Right rightLength c.1) :=
  if sharing c.1 then rightTensor rightLength parentShape c
  else strand (Fin (rightLength c.1))

omit [Fintype H] [DecidableEq H] in
theorem block_eq_children (h : H) (u : Shape)
    (hu : sharing h = true → ∀ s, shapeNat u s ≤ parentShape h s) :
    block (Left leftLength) (Right rightLength)
      (inputTensor leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) (h, u) =
      Tensor.product (leftTensor (F := F) leftLength (h, u))
        (childRight rightLength parentShape sharing (h, u)) := by
  by_cases hs : sharing h = true
  · funext x y z
    have hh := congrFun (congrFun (congrFun
      (block_eq_product (F := F) leftLength rightLength parentShape hleft h u (hu hs)) x) y) z
    simpa only [block, inputTensor, childRight, hs, ↓reduceIte] using hh
  · funext x y z
    simp [block, inputTensor, childRight, hs, leftTensor, shapeTensor,
      coarse, CWCoarseIndices.coarseIndex, Fin.ext_iff, shapeNat, shapeSide,
      Tensor.product, ite_mul]

omit [DecidableEq H] in
theorem canonicalBase_eq_children
    (hsupport : ∀ h u, 0 < counts h u → sharing h = true →
      ∀ s, shapeNat u s ≤ parentShape h s) :
    canonicalBase counts (Left leftLength) (Right rightLength)
      (inputTensor leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) =
      pairClassProduct (leftTensor (F := F) leftLength)
        (childRight rightLength parentShape sharing) := by
  funext x y z
  unfold canonicalBase
  have hf : (∏ c : ClassKey (H := H), ∏ j : ClassPositions counts c,
      block (Left leftLength) (Right rightLength)
        (inputTensor leftLength rightLength parentShape sharing)
        (coarse leftLength rightLength hleft) c
        (x.left c j, x.right c j) (y.left c j, y.right c j) (z.left c j, z.right c j)) =
      ∏ c : ClassKey (H := H), ∏ j : ClassPositions counts c,
        (leftTensor (F := F) leftLength c (x.left c j) (y.left c j) (z.left c j) *
          childRight rightLength parentShape sharing c
            (x.right c j) (y.right c j) (z.right c j)) := by
    apply Finset.prod_congr rfl
    intro c _
    apply Finset.prod_congr rfl
    intro j _
    have hc : 0 < counts c.1 c.2 := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
    rw [block_eq_children leftLength rightLength parentShape sharing hleft c.1 c.2
      (hsupport c.1 c.2 hc)]
    rfl
  rw [hf]
  simp only [pairClassProduct, classProduct, Finset.prod_mul_distrib]

omit [Fintype H] [DecidableEq H] in
theorem coarse_support (h : H)
    (x y z : Left leftLength h × Right rightLength h)
    (hT : inputTensor (F := F) leftLength rightLength parentShape sharing h x y z ≠ 0) :
    (coarse leftLength rightLength hleft 0 h x).val +
      (coarse leftLength rightLength hleft 1 h y).val +
      (coarse leftLength rightLength hleft 2 h z).val = 2 * leftLength h := by
  by_cases hs : sharing h = true
  · have hp : parentTensor (F := F) leftLength rightLength parentShape h x y z ≠ 0 := by
      simpa [inputTensor, hs] using hT
    have hh := CWCoarseIndices.split_coarse_support
      (F := F) (by simpa using hleft h) (parentShape h) x y z hp
    simpa only [coarse, Fintype.card_fin] using hh.1
  · have ht : strand (F := F) (Fin (leftLength h)) x.1 y.1 z.1 ≠ 0 := by
      intro hz
      apply hT
      simp [inputTensor, hs, Tensor.product, hz]
    simpa only [coarse, Fintype.card_fin] using
      CWCoarseIndices.strand_coarse_support (F := F) (by simpa using hleft h) x.1 y.1 z.1 ht

def maskedSource : Tensor F (MixedWords counts leftLength rightLength)
    (MixedWords counts leftLength rightLength) (MixedWords counts leftLength rightLength) :=
  ExactRecovery.delete
    (sourceTensor counts (Left leftLength) (Right rightLength)
      (inputTensor leftLength rightLength parentShape sharing))
    (sideMask counts leftLength rightLength hleft 0)
    (sideMask counts leftLength rightLength hleft 1)
    (sideMask counts leftLength rightLength hleft 2)

theorem maskedSource_support (x y z : MixedWords counts leftLength rightLength)
    (hT : maskedSource (F := F) counts leftLength rightLength parentShape sharing hleft x y z ≠ 0) :
    (coarseWord counts leftLength rightLength hleft x,
      coarseWord counts leftLength rightLength hleft y,
      coarseWord counts leftLength rightLength hleft z) ∈
      ambientSet counts (fun h => 2 * leftLength h) := by
  have hm : sideMask counts leftLength rightLength hleft 0 x ∧
      sideMask counts leftLength rightLength hleft 1 y ∧
      sideMask counts leftLength rightLength hleft 2 z := by
    by_contra hn
    simp [maskedSource, ExactRecovery.delete, hn] at hT
  have hr : sourceTensor counts (Left leftLength) (Right rightLength)
      (inputTensor (F := F) leftLength rightLength parentShape sharing) x y z ≠ 0 := by
    simpa [maskedSource, ExactRecovery.delete, hm] using hT
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro i
    have hi : inputTensor (F := F) leftLength rightLength parentShape sharing i.1
        (x i.1 i.2) (y i.1 i.2) (z i.1 i.2) ≠ 0 := by
      intro hz
      apply hr
      unfold sourceTensor classProduct
      apply Finset.prod_eq_zero (Finset.mem_univ i.1)
      exact Finset.prod_eq_zero (Finset.mem_univ i.2) hz
    exact coarse_support leftLength rightLength parentShape sharing hleft i.1
      (x i.1 i.2) (y i.1 i.2) (z i.1 i.2) hi
  · intro h s a
    fin_cases s
    · exact hm.1 h a
    · exact hm.2.1 h a
    · exact hm.2.2 h a

omit [DecidableEq H] in
theorem coarseIdeal_support_masks (e : Target counts)
    (x y z : MixedWords counts leftLength rightLength)
    (hT : coarseIdeal counts (Left leftLength) (Right rightLength)
      (inputTensor (F := F) leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) e x y z ≠ 0) :
    sideMask counts leftLength rightLength hleft 0 x ∧
      sideMask counts leftLength rightLength hleft 1 y ∧
      sideMask counts leftLength rightLength hleft 2 z := by
  have hc : coarseMask counts (Left leftLength) (Right rightLength)
      (coarse leftLength rightLength hleft) 0 e x ∧
      coarseMask counts (Left leftLength) (Right rightLength)
        (coarse leftLength rightLength hleft) 1 e y ∧
      coarseMask counts (Left leftLength) (Right rightLength)
        (coarse leftLength rightLength hleft) 2 e z := by
    by_contra hn
    simp [coarseIdeal, ExactRecovery.delete, hn] at hT
  constructor
  · apply sideMask_of_target counts leftLength rightLength hleft 0 e x
    funext i
    exact hc.1 i.1 i.2
  constructor
  · apply sideMask_of_target counts leftLength rightLength hleft 1 e y
    funext i
    exact hc.2.1 i.1 i.2
  · apply sideMask_of_target counts leftLength rightLength hleft 2 e z
    funext i
    exact hc.2.2 i.1 i.2

omit [DecidableEq H] in
theorem ideal_support_masks (e : Target counts)
    (px py pz : MixedWords counts leftLength rightLength → Prop)
    (x y z : MixedWords counts leftLength rightLength)
    (hT : ExactRecovery.delete
      (coarseIdeal counts (Left leftLength) (Right rightLength)
        (inputTensor (F := F) leftLength rightLength parentShape sharing)
        (coarse leftLength rightLength hleft) e) px py pz x y z ≠ 0) :
    sideMask counts leftLength rightLength hleft 0 x ∧
      sideMask counts leftLength rightLength hleft 1 y ∧
      sideMask counts leftLength rightLength hleft 2 z := by
  apply coarseIdeal_support_masks (F := F) counts leftLength rightLength parentShape sharing hleft e x y z
  intro hz
  simp [ExactRecovery.delete, hz] at hT

end MatrixMultiplication.JointCanonicalMixed

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWStageCPlacements
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instDecidableEqResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instFintypeResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.CWStageCProducts

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type*} [Fintype H]

theorem populationAtomCounts_mass {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) (h : PopulationHistory K) (i : Fin 4) :
    (populationAtomCounts allocation dilation h i : ℚ) =
      (AllFieldHistory.populationLength (K := K) allocation dilation : ℚ) *
        AllFieldHistory.amount allocation (.partC h.1, h.2) *
          AllFieldHistory.stageCWeight (AllFieldHistory.cParameterParent h.1)
            (AllFieldHistory.cShapeParent h.1) i := by
  rw [populationAtomCounts, AllFieldHistory.population_cast]
  simp only [AllFieldHistory.amount, AllFieldHistory.canonicalAmount,
    AllFieldHistory.cAmount]
  ring

theorem populationAtomCounts_parent {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) (h : PopulationHistory K) (i : Fin 4) :
    (populationAtomCounts allocation dilation h i : ℚ) =
      (AllFieldHistory.population allocation dilation (.partC h.1, h.2) : ℚ) *
        AllFieldHistory.stageCWeight (AllFieldHistory.cParameterParent h.1)
          (AllFieldHistory.cShapeParent h.1) i := by
  rw [populationAtomCounts_mass, AllFieldHistory.population_cast]

end MatrixMultiplication.CWStageCProducts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWStageCStatistics
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
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

attribute [local instance] Classical.propDecidable Classical.decEq

theorem twoStatistic_of_side_weights (s : Fin 3) (b : Fin 4) (i : Fin 3)
    (w : Word)
    (hleft : CWLeafStatistics.weight (w 0) = branchAtom s b i)
    (hright : CWLeafStatistics.weight (w 1) = shape s i - branchAtom s b i) :
    CWCompleteStatistics.twoStatistic w = branchStatistic s b i := by
  change CWLeafStatistics.pairStatistic (w 0, w 1) = _
  unfold CWLeafStatistics.pairStatistic
  dsimp only
  rw [hleft, hright]
  fin_cases s <;> fin_cases b <;> fin_cases i <;> decide

theorem empiricalLaw_eq_littleLaw (counts : Fin 4 → ℕ)
    (t u : AllFieldParameters.Shape) (hu : u ∈ AllFieldParameters.shapes 4)
    (hpos : AllFieldParameters.positive u = true) (n : ℕ) (hn : 0 < n)
    (hc : ∀ b, (counts b : ℚ) = (n : ℚ) * AllFieldHistory.stageCWeight t u b)
    (i : Fin 3) (w : Positions counts → Fin 6)
    (hw : ∀ p, w p = branchStatistic (AllFieldHistory.stageCDistinguished u) p.1 i) :
    InheritedMasks.empiricalLaw w =
      fun a => (AllFieldParameters.littleLaw t u i a : ℝ) := by
  have hcard : Fintype.card (Positions counts) = n := by
    apply Nat.cast_injective (R := ℚ)
    calc
      (Fintype.card (Positions counts) : ℚ) = ∑ b, (counts b : ℚ) := by
        simp [Positions, Fintype.card_sigma]
      _ = n := by
        simp only [hc, ← Finset.mul_sum, AllFieldHistory.stageCWeight_normalized, mul_one]
  have hshape : u i = if i = AllFieldHistory.stageCDistinguished u then 2 else 1 := by
    exact congrFun (shape_eq_parent u hu hpos).symm i
  have hcount (a : Fin 6) : (wordPopulation w a : ℚ) =
      (n : ℚ) * AllFieldParameters.littleLaw t u i a := by
    rw [wordPopulation_of_branchStatistic counts _ i w hw a]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    simp_rw [hc]
    simp only [AllFieldParameters.littleLaw, hshape]
    by_cases hi : i = AllFieldHistory.stageCDistinguished u <;>
      fin_cases a <;>
      simp [branchStatistic, hi, Fin.sum_univ_succ,
        AllFieldParameters.singletonSlot,
        AllFieldHistory.stageCWeight] <;> ring
  funext a
  have hr : (wordPopulation w a : ℝ) =
      (n : ℝ) * (AllFieldParameters.littleLaw t u i a : ℝ) := by
    exact_mod_cast hcount a
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [InheritedMasks.empiricalLaw, hr, hcard]
  exact mul_div_cancel_left₀ _ hn'

theorem typeWindow_of_placed_side_weights (counts : Fin 4 → ℕ)
    (t u : AllFieldParameters.Shape) (hu : u ∈ AllFieldParameters.shapes 4)
    (hpos : AllFieldParameters.positive u = true) (n : ℕ) (hn : 0 < n)
    (hc : ∀ b, (counts b : ℚ) = (n : ℚ) * AllFieldHistory.stageCWeight t u b)
    (phi : Equiv.Perm (Fin 3)) (i : Fin 3) (w : Positions counts → Word)
    (hweights : ∀ p,
      CWLeafStatistics.weight (w p 0) =
        branchAtom (AllFieldHistory.stageCDistinguished u) p.1 (phi.symm i) ∧
      CWLeafStatistics.weight (w p 1) =
        shape (AllFieldHistory.stageCDistinguished u) (phi.symm i) -
          branchAtom (AllFieldHistory.stageCDistinguished u) p.1 (phi.symm i))
    (η : ℝ) (hη : 0 ≤ η) :
    InheritedMasks.typeWindow
      (fun a : Fin 6 => (AllFieldParameters.littleLaw t u (phi.symm i) a : ℝ)) η
      (fun p => CWCompleteStatistics.twoStatistic (w p)) := by
  have he := empiricalLaw_eq_littleLaw counts t u hu hpos n hn hc (phi.symm i)
    (fun p => CWCompleteStatistics.twoStatistic (w p)) (fun p =>
      twoStatistic_of_side_weights _ _ _ _ (hweights p).1 (hweights p).2)
  intro a
  rw [he]
  simpa only [sub_self, abs_zero] using hη

end MatrixMultiplication.CWStageCProducts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_GroupOrbitCount
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.nativeSplitWeightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.choiceAt_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.initialExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
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

abbrev selectedPositions {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (D : Finset (ActiveClass K tick)) (c : D) :=
  JointCanonicalization.ClassPositions (activeCounts allocation m) c.val

theorem selected_populationSize {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (D : Finset (ActiveClass K tick)) :
    PermutationMatching.populationSize (selectedPositions allocation m D) =
      selectedBasePopulation allocation D * (m : ℝ) := by
  simp only [PermutationMatching.populationSize, selectedPositions,
    JointCanonicalization.ClassPositions, Fintype.card_fin]
  rw [Finset.sum_coe_sort D
    (fun c : ActiveClass K tick => (activeCounts allocation m c.1 c.2 : ℝ))]
  simp only [activeCounts_dilation allocation m, Nat.cast_mul, ← Finset.mul_sum,
    selectedBasePopulation, selectedBaseCount, Nat.cast_sum]
  exact mul_comm _ _

theorem selected_two_le {K tick m : ℕ} (allocation : Allocation) (hm : 2 ≤ m)
    (D : Finset (ActiveClass K tick))
    (hpos : ∀ c ∈ D, 0 < activeCounts allocation 1 c.1 c.2) (c : D) :
    2 ≤ Fintype.card (selectedPositions allocation m D c) := by
  simpa only [selectedPositions, JointCanonicalization.ClassPositions, Fintype.card_fin] using
    two_le_activeCounts allocation hm c.val.1 c.val.2 (hpos c.val c.property)

theorem selected_classWeight_formula {K tick m : ℕ} (allocation : Allocation)
    (hm : 0 < m) (D : Finset (ActiveClass K tick)) (c : D) :
    PermutationMatching.classWeight (selectedPositions allocation m D) c =
      (activeCounts allocation 1 c.val.1 c.val.2 : ℝ) / selectedBasePopulation allocation D := by
  rw [PermutationMatching.classWeight, selected_populationSize]
  simp only [selectedPositions, JointCanonicalization.ClassPositions, Fintype.card_fin,
    activeCounts_dilation allocation m, Nat.cast_mul]
  rw [mul_comm (selectedBasePopulation allocation D) (m : ℝ)]
  exact mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))

theorem selected_classWeight_eq_one {K tick m : ℕ} (allocation : Allocation)
    (hm : 0 < m) (D : Finset (ActiveClass K tick)) (c : D) :
    PermutationMatching.classWeight (selectedPositions allocation m D) c =
      PermutationMatching.classWeight (selectedPositions allocation 1 D) c :=
  (selected_classWeight_formula allocation hm D c).trans
    (selected_classWeight_formula allocation (by decide : 0 < (1 : ℕ)) D c).symm

theorem selected_classProductMixture_eq_one {K tick m : ℕ} (allocation : Allocation)
    (hm : 0 < m) (D : Finset (ActiveClass K tick)) (left right : D → ℝ) :
    PermutationMatching.classProductMixture (selectedPositions allocation m D) left right =
      PermutationMatching.classProductMixture (selectedPositions allocation 1 D) left right := by
  unfold PermutationMatching.classProductMixture
  apply Finset.sum_congr rfl
  intro c _
  rw [selected_classWeight_eq_one allocation hm D c]

theorem work_source_population_pos {K m : ℕ} (allocation : Allocation) (hm : 0 < m)
    (w : PlacedWork K) : 0 < population allocation m (w.1.source, w.2) :=
  (AllFieldPopulationCounts.count_pos_iff (amount allocation) (amount_nonneg allocation)
    hm (w.1.source, w.2)).2 (work_source_amount_pos allocation w)

theorem positiveClasses_positive {K tick : ℕ} (allocation : Allocation) (h : Active K tick)
    (c : ActiveClass K tick) (hc : c ∈ positiveClasses allocation h) :
    0 < activeCounts allocation 1 c.1 c.2 := (Finset.mem_filter.mp hc).2.2

theorem positiveClasses_baseCount {K tick : ℕ} (allocation : Allocation) (h : Active K tick) :
    selectedBaseCount allocation (positiveClasses allocation h) =
      population allocation 1 (h.val.1.source, h.val.2) := by
  have hkeep (n : ℕ) : (if 0 < n then n else 0) = n := by
    split_ifs <;> omega
  calc
    selectedBaseCount allocation (positiveClasses allocation h) =
        ∑ u, activeCounts allocation 1 h u := by
      simp [selectedBaseCount, positiveClasses, Finset.sum_filter, ite_and, hkeep,
        Fintype.sum_prod_type]
    _ = population allocation 1 (h.val.1.source, h.val.2) :=
      jointCounts_sum allocation 1 h.val

theorem positiveClasses_basePopulation_pos {K tick : ℕ} (allocation : Allocation)
    (h : Active K tick) : 0 < selectedBasePopulation allocation (positiveClasses allocation h) := by
  unfold selectedBasePopulation
  rw [positiveClasses_baseCount]
  exact_mod_cast work_source_population_pos allocation (by decide : 0 < (1 : ℕ)) h.val

theorem positiveClasses_populationSize {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (h : Active K tick) :
    PermutationMatching.populationSize
      (selectedPositions allocation m (positiveClasses allocation h)) =
        (population allocation 1 (h.val.1.source, h.val.2) : ℝ) * m := by
  rw [selected_populationSize]
  simp only [selectedBasePopulation, positiveClasses_baseCount]

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

def incomingWord (allocation : Allocation) (m : ℕ) (h : Active K tick)
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) :
    HistoryWord allocation m (h.val.1.source, h.val.2) :=
  fun p => joinHalves h.val.1 (w h ((sourcePositionsEquiv allocation m h).symm p))

def received (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) : Prop :=
  ∀ h : Active K tick,
    residentMask allocation m ε (h.val.1.source, h.val.2) side
      (incomingWord allocation m h w)

end MatrixMultiplication.AllFieldHistoryIncomingMasks

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryBranchWeights

open AllFieldHistory AllFieldHistorySupport AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem stageB_branchWeight_real {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (h : APositive K) (b : BSplit h) (phi : Placement) :
    (branchPopulation allocation dilation (.stageB h, phi) b : ℝ) /
      (population allocation dilation (.afterA h.val, phi) : ℝ) =
        (stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩) : ℝ) := by
  have hpos := AllFieldHistorySupport.work_source_population_pos allocation hd (.stageB h, phi)
  have hden : (population allocation dilation (.afterA h.val, phi) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  apply (div_eq_iff hden).2
  rw [stageB_branchPopulation_real]
  exact mul_comm _ _

end MatrixMultiplication.AllFieldHistoryBranchWeights

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryStageCIncoming

open AllFieldHistory AllFieldHistorySupport AllFieldParameters
open CWStageCProducts InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def positionEquiv (allocation : Allocation) (dilation : ℕ) (h : PartC K)
    (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation dilation)) :
    JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation dilation) (stageCActive h phi ht) ≃
      CWStageCProducts.Positions (populationAtomCounts allocation dilation (h, phi)) :=
  (JointCanonicalization.positionEquiv (activeCounts (K := K) (tick := tick) allocation dilation) e
    (stageCActive h phi ht)).trans
      (branchPositionEquiv allocation dilation (.stageC h, phi))

theorem positionEquiv_shape (allocation : Allocation) (dilation : ℕ) (h : PartC K)
    (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation dilation))
    (j : JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation dilation) (stageCActive h phi ht)) :
    branchShape (.stageC h, phi) (positionEquiv allocation dilation h phi ht e j).1 =
      (e (stageCActive h phi ht)).val j := by
  exact (branchPositionEquiv_shape allocation dilation (.stageC h, phi)
    (JointCanonicalization.positionEquiv (activeCounts (K := K) (tick := tick) allocation dilation) e
      (stageCActive h phi ht) j)).trans
    (JointCanonicalization.positionEquiv_shape (activeCounts (K := K) (tick := tick) allocation dilation) e
      (stageCActive h phi ht) j)

theorem positionEquiv_symm_shape (allocation : Allocation) (dilation : ℕ) (h : PartC K)
    (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation dilation))
    (p : CWStageCProducts.Positions (populationAtomCounts allocation dilation (h, phi))) :
    (e (stageCActive h phi ht)).val ((positionEquiv allocation dilation h phi ht e).symm p) =
      branchShape (.stageC h, phi) p.1 := by
  have hp := positionEquiv_shape allocation dilation h phi ht e
    ((positionEquiv allocation dilation h phi ht e).symm p)
  simpa only [Equiv.apply_symm_apply] using hp.symm

theorem typeWindow_of_target_side_weights (allocation : Allocation) {dilation : ℕ}
    (hd : 0 < dilation) (h : PartC K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation dilation))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation dilation) (side : Fin 3)
    (hweights : ∀ j : JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation dilation)
        (stageCActive h phi ht),
      CWLeafStatistics.weight ((w (stageCActive h phi ht) j).1 (0 : Fin 1)) =
          (JointPopulation.shapeSide side ((e (stageCActive h phi ht)).val j)).val ∧
      CWLeafStatistics.weight ((w (stageCActive h phi ht) j).2 (0 : Fin 1)) =
          activeParentShape (stageCActive h phi ht) side -
            (JointPopulation.shapeSide side ((e (stageCActive h phi ht)).val j)).val)
    (η : ℝ) (hη : 0 ≤ η) :
    typeWindow
      (fun a : Fin 6 =>
        (littleLaw (cParameterParent h) (cShapeParent h) (phi.symm side) a : ℝ)) η
      (fun j => CWCompleteStatistics.twoStatistic
        (Matrix.vecCons ((w (stageCActive h phi ht) j).1 (0 : Fin 1)) (Matrix.vecCons ((w (stageCActive h phi ht) j).2 (0 : Fin 1)) Matrix.vecEmpty))) := by
  let p := positionEquiv allocation dilation h phi ht e
  let words : CWStageCProducts.Positions (populationAtomCounts allocation dilation (h, phi)) →
      CWStageCProducts.Word := fun j =>
    (Matrix.vecCons ((w (stageCActive h phi ht) (p.symm j)).1 (0 : Fin 1)) (Matrix.vecCons ((w (stageCActive h phi ht) (p.symm j)).2 (0 : Fin 1)) Matrix.vecEmpty))
  have hgeometry (j : CWStageCProducts.Positions
      (populationAtomCounts allocation dilation (h, phi))) :
      CWLeafStatistics.weight (words j 0) =
        branchAtom (stageCDistinguished (cShapeParent h)) j.1 (phi.symm side) ∧
      CWLeafStatistics.weight (words j 1) =
        CWStageCProducts.shape (stageCDistinguished (cShapeParent h)) (phi.symm side) -
          branchAtom (stageCDistinguished (cShapeParent h)) j.1 (phi.symm side) := by
    have hw := hweights (p.symm j)
    have hs := positionEquiv_symm_shape allocation dilation h phi ht e j
    change (e (stageCActive h phi ht)).val (p.symm j) = _ at hs
    rw [hs] at hw
    simpa only [words, Matrix.cons_val_zero, Matrix.cons_val_one,
      activeParentShape, stageCActive, Work.parentShape, branchShape,
      encodePhysicalShape_side, physicalShape, Work.splitShape, cSplit,
      branchAtom_eq_stageCAtom, shape_eq_parent (cShapeParent h) (bShape_size h.1.val)
        h.1.property] using hw
  have hwindow := typeWindow_of_placed_side_weights
    (populationAtomCounts allocation dilation (h, phi))
    (cParameterParent h) (cShapeParent h) (bShape_size h.1.val) h.1.property
    (population allocation dilation (.partC h, phi))
    (AllFieldHistorySupport.work_source_population_pos allocation hd (.stageC h, phi))
    (populationAtomCounts_parent allocation dilation (h, phi))
    phi side words hgeometry η hη
  exact (JointCanonicalization.typeWindow_reindex _ η
    (fun j => CWCompleteStatistics.twoStatistic
      (Matrix.vecCons ((w (stageCActive h phi ht) j).1 (0 : Fin 1)) (Matrix.vecCons ((w (stageCActive h phi ht) j).2 (0 : Fin 1)) Matrix.vecEmpty)))
    p.symm).mp hwindow

end MatrixMultiplication.AllFieldHistoryStageCIncoming

end
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

abbrev Positions {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (c : Classes K tick) :=
  JointCanonicalization.ClassPositions (activeCounts allocation m) c

def basePopulationBound {K tick : ℕ} (allocation : Allocation) : ℕ :=
  ∑ c : Classes K tick, activeCounts allocation 1 c.1 c.2

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

def groupOrbitPrefactor {K tick : ℕ} (allocation : Allocation) (sigma : Placement) : ℝ :=
  ((AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation + 1 : ℕ) : ℝ) ^
    groupDegree K tick sigma

end MatrixMultiplication.AllFieldGroupOrbitCount

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryRecoveryBudget
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.nativeSplitWeightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.initialExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldPairMarginals.halfWeightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
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

noncomputable instance permutationsFintype (allocation : Allocation) (m : ℕ) :
    Fintype (HalfClassPermutations (Positions (K := K) (tick := tick) allocation m)) := by
  letI : DecidableEq (Classes K tick) := Classical.decEq _
  letI : ∀ c : Classes K tick, DecidableEq (Positions allocation m c) :=
    fun _ => Classical.decEq _
  letI : Fintype (Classes K tick) := inferInstance
  letI : ∀ c : Classes K tick, Fintype (Equiv.Perm (Positions allocation m c)) :=
    fun c => Equiv.instFintype
  letI : Fintype ((c : Classes K tick) → Equiv.Perm (Positions allocation m c)) :=
    Pi.instFintype
  change Fintype (((c : Classes K tick) → Equiv.Perm (Positions allocation m c)) ×
    ((c : Classes K tick) → Equiv.Perm (Positions allocation m c)))
  infer_instance

def passes (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : Words (K := K) (tick := tick) allocation m) : Prop :=
  ∀ i : MaskIndex K tick, ¬ selectedWordPairMaskBad (testedClasses allocation i)
    classStatistic classStatistic (leftSymbol i) (rightSymbol i)
    (pairWidth ε i.1) (center allocation side i) w

theorem lossConstant_nonneg (allocation : Allocation) (ε : ℝ) :
    0 ≤ lossConstant (K := K) (tick := tick) allocation ε := by
  apply Finset.sum_nonneg
  intro i _
  change 0 ≤ 1 / (2 * (selectedBaseCount allocation (testedClasses allocation i) : ℝ) *
    (pairWidth ε i.1) ^ 2)
  exact div_nonneg zero_le_one
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _))

end MatrixMultiplication.AllFieldHistoryMasks






namespace MatrixMultiplication.AllFieldHistoryMaskLaws

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistorySupport
open AllFieldHistoryMasks AllFieldHistoryBranchWeights AllFieldParameters
open PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem center_eq_parentCenter (allocation : Allocation) (side : Fin 3)
    (i : MaskIndex K tick) :
    center allocation side i = parentCenter allocation side i.1 (i.2.1 i.1) (i.2.2 i.1) := by
  have hw (c : testedClasses allocation i) :
      classWeight (fun c : testedClasses allocation i => Positions allocation 1 c.val) c =
        (activeCounts allocation 1 c.val.1 c.val.2 : ℝ) /
          population allocation 1 (i.1.val.1.source, i.1.val.2) := by
    rw [selected_classWeight_formula allocation (by decide : 0 < (1 : ℕ))]
    simp only [selectedBasePopulation, testedClasses, positiveClasses_baseCount]
  unfold center classProductMixture
  simp_rw [hw]
  let f : Classes K tick → ℝ := fun c =>
    (activeCounts allocation 1 c.1 c.2 : ℝ) /
      population allocation 1 (i.1.val.1.source, i.1.val.2) *
        (leftProbability side i c * rightProbability side i c)
  change (∑ c : testedClasses allocation i, f c.val) = _
  rw [Finset.sum_coe_sort]
  have hzero (c : Classes K tick) :
      (if 0 < activeCounts allocation 1 c.1 c.2 then f c else 0) = f c := by
    split_ifs with hc
    · rfl
    · have hz : activeCounts allocation 1 c.1 c.2 = 0 := Nat.eq_zero_of_not_pos hc
      simp [f, hz]
  simp only [testedClasses, positiveClasses, Finset.sum_filter, ite_and, hzero]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i.1]
  · simp [f, parentCenter, leftProbability, rightProbability, leftSymbol, rightSymbol]
  · intro other _ hne
    simp only [hne, ite_false, if_false, Finset.sum_const_zero]
  · simp

theorem parentCenter_stageB (allocation : Allocation) (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick)
    (side : Fin 3) (a b : Fin 6) :
    parentCenter allocation side (stageBActive h phi ht) a b =
      (halfLaw (aShape h.val) (phi.symm side) (a, b) : ℝ) := by
  let w : PlacedWork K := (.stageB h, phi)
  let f : JointPopulation.Shape → ℝ := fun u =>
    leftLaw (stageBActive h phi ht) u side a * rightLaw (stageBActive h phi ht) u side b
  calc
    parentCenter allocation side (stageBActive h phi ht) a b =
        (∑ u, (jointCounts allocation 1 w u : ℝ) * f u) /
          population allocation 1 (.afterA h.val, phi) := by
      unfold parentCenter
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u _
      dsimp only [activeCounts, stageBActive, w, f, Work.source]
      ring
    _ = (∑ k : BSplit h, (branchPopulation allocation 1 w k : ℝ) * f (branchShape w k)) /
          population allocation 1 (.afterA h.val, phi) := by
      rw [jointCounts, shapeCounts_weighted_sum]
      rfl
    _ = ∑ k : BSplit h,
        (stageBLaw (aShape h.val) (bSplit ⟨h, k, false⟩) : ℝ) *
          (littleLaw (aShape h.val) (bSplit ⟨h, k, false⟩) (phi.symm side) a : ℝ) *
          (littleLaw (aShape h.val) (complement (aShape h.val) (bSplit ⟨h, k, false⟩))
            (phi.symm side) b : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [f, w]
      rw [stageB_leftLaw_branch, stageB_rightLaw_branch]
      rw [mul_div_right_comm,
        stageB_branchWeight_real allocation (by decide : 0 < (1 : ℕ)) h k phi]
      ring
    _ = (halfLaw (aShape h.val) (phi.symm side) (a, b) : ℝ) := by
      exact_mod_cast stageB_sum_laws h (phi.symm side) a b

theorem center_stageB (allocation : Allocation) (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick)
    (side : Fin 3) (a b : SymbolChoice K tick) :
    center allocation side (stageBActive h phi ht, a, b) =
      (halfLaw (aShape h.val) (phi.symm side)
        (a (stageBActive h phi ht), b (stageBActive h phi ht)) : ℝ) := by
  rw [center_eq_parentCenter]
  exact parentCenter_stageB allocation h phi ht side _ _

end MatrixMultiplication.AllFieldHistoryMaskLaws






namespace MatrixMultiplication.AllFieldHistoryRawMasks

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistorySupport AllFieldHistoryMasks
open JointCanonicalization PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def rawPairCount (allocation : Allocation) (m : ℕ) (i : MaskIndex K tick)
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) : ℝ :=
  ∑ j : JointPopulation.Positions (activeCounts allocation m) i.1,
    if statistic i.1 (w i.1 j).1 = i.2.1 i.1 ∧
      statistic i.1 (w i.1 j).2 = i.2.2 i.1 then 1 else 0

def rawPass (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) : Prop :=
  ∀ i : MaskIndex K tick,
    |rawPairCount allocation m i w /
      (population allocation m (i.1.val.1.source, i.1.val.2) : ℝ) -
        center allocation side i| ≤ pairWidth ε i.1

theorem sum_positiveClasses (allocation : Allocation) (m : ℕ) (h : Active K tick)
    (f : ∀ c : Classes K tick, Positions allocation m c → ℝ) :
    (∑ c : positiveClasses allocation h, ∑ j, f c.val j) =
      ∑ u : JointPopulation.Shape, ∑ j, f (h, u) j := by
  have hzero (c : Classes K tick) (hc : ¬0 < activeCounts allocation 1 c.1 c.2) :
      (∑ j, f c j) = 0 := by
    have hcount : activeCounts allocation m c.1 c.2 = 0 := by
      rw [activeCounts_dilation, Nat.eq_zero_of_not_pos hc, mul_zero]
    apply Finset.sum_eq_zero
    intro j _
    have hj : j.val < 0 := by simpa only [hcount] using j.isLt
    exact (Nat.not_lt_zero _ hj).elim
  rw [Finset.sum_coe_sort (positiveClasses allocation h)
    (fun c : Classes K tick => ∑ j, f c j)]
  unfold positiveClasses
  rw [Finset.sum_filter]
  calc
    (∑ c : Classes K tick,
        if c.1 = h ∧ 0 < activeCounts allocation 1 c.1 c.2 then ∑ j, f c j else 0) =
        ∑ c : Classes K tick, if c.1 = h then ∑ j, f c j else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : 0 < activeCounts allocation 1 c.1 c.2
      · simp only [hc, and_true]
      · rw [hzero c hc]
        simp
    _ = ∑ u : JointPopulation.Shape, ∑ j, f (h, u) j := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single h]
      · simp
      · intro other _ hne
        simp only [hne, ite_false, if_false, Finset.sum_const_zero]
      · simp

theorem selectedWordPairCount_pairEquiv (allocation : Allocation) (m : ℕ)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (i : MaskIndex K tick) (w : ActiveRawPairs (K := K) (tick := tick) allocation m) :
    selectedWordPairCount (testedClasses allocation i)
      (pairEquiv (activeCounts allocation m)
        (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength) e w)
      classStatistic classStatistic (leftSymbol i) (rightSymbol i) =
        rawPairCount allocation m i w := by
  let v : Words (K := K) (tick := tick) allocation m :=
    pairEquiv (activeCounts allocation m)
      (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength) e w
  have hsum := sum_positiveClasses allocation m i.1 (fun c j =>
    if classStatistic c (v.left c j) = leftSymbol i c ∧
      classStatistic c (v.right c j) = rightSymbol i c then (1 : ℝ) else 0)
  unfold selectedWordPairCount
  rw [testedClasses, hsum]
  unfold rawPairCount
  rw [← Fintype.sum_sigma']
  apply Fintype.sum_equiv (positionEquiv (activeCounts allocation m) e i.1).symm
  rintro ⟨u, j⟩
  rfl

theorem testedClasses_populationSize (allocation : Allocation) (m : ℕ)
    (i : MaskIndex K tick) :
    populationSize (fun c : testedClasses allocation i => Positions allocation m c.val) =
      (population allocation m (i.1.val.1.source, i.1.val.2) : ℝ) := by
  change populationSize (selectedPositions allocation m (positiveClasses allocation i.1)) = _
  rw [positiveClasses_populationSize, population_dilation allocation m, Nat.cast_mul]
  exact mul_comm _ _

theorem passes_pairEquiv_iff_rawPass (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) :
    passes allocation m ε side
      (pairEquiv (activeCounts allocation m)
        (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength) e w) ↔
      rawPass allocation m ε side w := by
  simp only [passes, selectedWordPairMaskBad, selectedWordPairCount_pairEquiv,
    testedClasses_populationSize, rawPass, not_lt]

end MatrixMultiplication.AllFieldHistoryRawMasks






namespace MatrixMultiplication.AllFieldHistoryIncomingMasks

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters
open AllFieldHistoryChildLaws AllFieldHistorySupport AllFieldHistoryMasks
open AllFieldHistoryMaskLaws AllFieldHistoryRawMasks InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem weight_append {m n : ℕ} (l : Fin m → Fin 7) (r : Fin n → Fin 7) :
    CWStrands.weight (Fin.append l r) = CWStrands.weight l + CWStrands.weight r := by
  simp [CWStrands.weight, Fin.sum_univ_add]

theorem shapeTensor_append {F : Type*} [CommRing F] {m n : ℕ} (g : Shape)
    (x y z : (Fin m → Fin 7) × (Fin n → Fin 7)) :
    CWStrands.shapeTensor (F := F) (Fin (m + n)) g
      (Fin.append x.1 x.2) (Fin.append y.1 y.2) (Fin.append z.1 z.2) =
        CWStrands.shapeTensor (Fin m ⊕ Fin n) g
          (Sum.elim x.1 x.2) (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) := by
  simp only [CWStrands.shapeTensor, weight_append, CWStrands.weight_sum_elim,
    strand_append, CWStrands.strand_sum_elim, Tensor.product]

theorem shapeTensor_joinHalves {F : Type*} [CommRing F] (w : Work K) (g : Shape)
    (x y z : (Fin w.halfLength → Fin 7) × (Fin w.halfLength → Fin 7)) :
    CWStrands.shapeTensor (F := F) (Fin (currentLength w.source)) g
      (joinHalves w x) (joinHalves w y) (joinHalves w z) =
        CWStrands.shapeTensor (Fin w.halfLength ⊕ Fin w.halfLength) g
          (Sum.elim x.1 x.2) (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) := by
  cases w <;> exact shapeTensor_append g x y z

theorem rawPairCount_eq_wordPopulation (allocation : Allocation) (m : ℕ)
    (i : MaskIndex K tick) (w : ActiveRawPairs (K := K) (tick := tick) allocation m) :
    rawPairCount allocation m i w =
      (wordPopulation (fun j => (statistic i.1 (w i.1 j).1,
        statistic i.1 (w i.1 j).2)) (i.2.1 i.1, i.2.2 i.1) : ℝ) := by
  simp only [rawPairCount, wordPopulation, Fintype.card_subtype, Prod.mk.injEq]
  exact Finset.sum_boole _ _

attribute [local irreducible] activeCounts population

theorem rawPass_stageB_typeWindow (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3) (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (hw : rawPass allocation m ε side w) (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick) :
    typeWindow (fun ij : PairSlot => (halfLaw (aShape h.val) (phi.symm side) ij : ℝ))
      (pairWidth ε (stageBActive h phi ht))
      (fun j => CWCompleteStatistics.fourStatistic
        (joinHalves (.stageB h) (w (stageBActive h phi ht) j))) := by
  intro ij
  have hp := hw (stageBActive h phi ht,
    choiceAt (stageBActive h phi ht) ij.1, choiceAt (stageBActive h phi ht) ij.2)
  rw [center_stageB] at hp
  rw [rawPairCount_eq_wordPopulation] at hp
  erw [choiceAt_self, choiceAt_self] at hp
  have hcard : Fintype.card (JointPopulation.Positions (activeCounts allocation m)
      (stageBActive h phi ht)) = population allocation m (.afterA h.val, phi) := by
    simp only [Fintype.card_eq_nat_card]
    simp only [JointPopulation.Positions, Nat.card_fin]
    simpa only [activeCounts, stageBActive, Work.source] using
      jointCounts_sum allocation m (.stageB h, phi)
  have hword : (fun j => CWCompleteStatistics.fourStatistic
      (joinHalves (.stageB h) (w (stageBActive h phi ht) j))) =
      (fun j => (statistic (stageBActive h phi ht) (w (stageBActive h phi ht) j).1,
        statistic (stageBActive h phi ht) (w (stageBActive h phi ht) j).2)) := by
    funext j
    rfl
  have he : empiricalLaw (fun j => CWCompleteStatistics.fourStatistic
      (joinHalves (.stageB h) (w (stageBActive h phi ht) j))) ij =
      empiricalLaw (fun j =>
        (statistic (stageBActive h phi ht) (w (stageBActive h phi ht) j).1,
          statistic (stageBActive h phi ht) (w (stageBActive h phi ht) j).2)) ij := by
    rw [hword]
    exact empiricalLaw_congr_decidable _ _ _ _
  rw [he]
  unfold empiricalLaw
  rw [hcard]
  dsimp only [stageBActive, Work.source] at hp
  erw [choiceAt_self, choiceAt_self] at hp
  exact hp

theorem incoming_stageA (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3) (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (h : InitialPositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageA h).lot (Work.stageA h).stage = tick) :
    residentMask allocation m ε ((Work.stageA h).source, phi) side
      (incomingWord allocation m ⟨(.stageA h, phi), ht⟩ w) := by
  trivial

theorem incoming_stageB (allocation : Allocation) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (side : Fin 3) (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (hw : rawPass allocation m ε side w) (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick) :
    residentMask allocation m ε ((Work.stageB h).source, phi) side
      (incomingWord allocation m (stageBActive h phi ht) w) := by
  intro _
  have hraw := rawPass_stageB_typeWindow allocation m ε side w hw h phi ht
  have htransport := (JointCanonicalization.typeWindow_reindex
    (fun ij : PairSlot => (halfLaw (aShape h.val) (phi.symm side) ij : ℝ))
    (pairWidth ε (stageBActive h phi ht))
    (fun j => CWCompleteStatistics.fourStatistic
      (joinHalves (.stageB h) (w (stageBActive h phi ht) j)))
    (sourcePositionsEquiv allocation m (stageBActive h phi ht)).symm).2 hraw
  have hwidth : pairWidth ε (stageBActive h phi ht) ≤ ε / 8 := by
    change ε / 16 ^ 1 ≤ ε / 8
    norm_num
    linarith
  dsimp only [Work.source, residentLaw, residentLawRat, residentWidth, residentStatistic]
  exact typeWindow_mono_decidable _ _ _ hwidth _ htransport

theorem incoming_stageC (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (h : PartC K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (hweights : ∀ j,
      CWLeafStatistics.weight ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).1 (0 : Fin 1)) =
        (JointPopulation.shapeSide side ((e (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).val j)).val ∧
      CWLeafStatistics.weight ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).2 (0 : Fin 1)) =
        activeParentShape (AllFieldHistoryStageCIncoming.stageCActive h phi ht) side -
          (JointPopulation.shapeSide side ((e (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).val j)).val) :
    residentMask allocation m ε ((Work.stageC h).source, phi) side
      (incomingWord allocation m (AllFieldHistoryStageCIncoming.stageCActive h phi ht) w) := by
  intro _
  have hraw := AllFieldHistoryStageCIncoming.typeWindow_of_target_side_weights
    allocation hm h phi ht e w side hweights (ε / 256) (div_nonneg hε (by norm_num))
  have htransport := (JointCanonicalization.typeWindow_reindex
    (fun a : Fin 6 => (littleLaw (cParameterParent h) (cShapeParent h) (phi.symm side) a : ℝ))
    (ε / 256)
    (fun j => CWCompleteStatistics.twoStatistic
      (Matrix.vecCons ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).1 (0 : Fin 1)) (Matrix.vecCons ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).2 (0 : Fin 1)) Matrix.vecEmpty)))
    (sourcePositionsEquiv allocation m (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).symm).2 hraw
  have hword : incomingWord allocation m
      (AllFieldHistoryStageCIncoming.stageCActive h phi ht) w =
      fun position => Matrix.vecCons
        ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht)
          ((sourcePositionsEquiv allocation m
            (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).symm position)).1 (0 : Fin 1))
        (Matrix.vecCons
          ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht)
            ((sourcePositionsEquiv allocation m
              (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).symm position)).2 (0 : Fin 1))
          Matrix.vecEmpty) := by
    funext position
    exact append_singletons _ _
  rw [hword]
  dsimp only [Work.source, residentLaw, residentLawRat, residentWidth, residentStatistic]
  exact typeWindow_mono_decidable _ _ _ le_rfl _ htransport

def stageCWeights (allocation : Allocation) (m : ℕ) (side : Fin 3)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) : Prop :=
  ∀ (h : PartC K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick) j,
      CWLeafStatistics.weight ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).1 (0 : Fin 1)) =
        (JointPopulation.shapeSide side ((e (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).val j)).val ∧
      CWLeafStatistics.weight ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).2 (0 : Fin 1)) =
        activeParentShape (AllFieldHistoryStageCIncoming.stageCActive h phi ht) side -
          (JointPopulation.shapeSide side ((e (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).val j)).val

theorem received_of_rawPass (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (hw : rawPass allocation m ε side w) (hc : stageCWeights allocation m side e w) :
    received allocation m ε side w := by
  rintro ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA h => exact incoming_stageA allocation m ε side w h phi ht
  | stageB h => exact incoming_stageB allocation m hε side w hw h phi ht
  | stageC h => exact incoming_stageC allocation hm hε side e w h phi ht (hc h phi ht)

end MatrixMultiplication.AllFieldHistoryIncomingMasks

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

def rawSource (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) :
    Tensor F (Raw (K := K) (tick := tick) allocation m)
      (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  sourceTensor (activeCounts allocation m) (Left activeHalfLength)
    (Right activeHalfLength) (parents F)

def ideal (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (e : Targets (K := K) (tick := tick) allocation m) :
    Tensor F (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  JointCanonicalization.ideal (activeCounts allocation m)
    (Left activeHalfLength) (Right activeHalfLength) (parents F)
    (coarse activeHalfLength activeHalfLength halfLength_le_eight)
    childStatistic childStatistic leftPrescription rightPrescription
    (outputWidth ε) (outputWidth ε) e

def completeKeep (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : Raw (K := K) (tick := tick) allocation m) : Prop :=
  JointCanonicalMixed.sideMask (activeCounts allocation m)
      activeHalfLength activeHalfLength halfLength_le_eight side w ∧
    AllFieldHistoryIncomingMasks.received allocation m ε side w ∧
    AllFieldHistoryRawMasks.rawPass allocation m ε side w

def idealSide (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m) (w : Raw (K := K) (tick := tick) allocation m) : Prop :=
  coarseMask (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
      (coarse activeHalfLength activeHalfLength halfLength_le_eight) side e w ∧
    rawWindows (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
      (childStatistic side) (childStatistic side) (leftPrescription side)
      (rightPrescription side) (outputWidth ε side) (outputWidth ε side) e w

end MatrixMultiplication.AllFieldHistoryRecovery






namespace MatrixMultiplication.AllFieldHistoryRecovery

open AllFieldHistory AllFieldHistorySupport

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem minimumDilation_spec (allocation : Allocation) (ε : ℝ) {m : ℕ}
    (hm : minimumDilation (K := K) (tick := tick) allocation ε ≤ m) :
    2 ≤ m ∧
      3 * (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6) <
        (m : ℝ) := by
  constructor
  · exact (Nat.le_add_left 2 _).trans hm
  · have hc := Nat.le_ceil
      (3 * (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6))
    have hm' : (Nat.ceil
        (3 * (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6)) : ℝ) + 2 ≤ m := by
      exact_mod_cast hm
    linarith

def shiftCount (allocation : Allocation) (ε : ℝ) (m : ℕ) : ℕ :=
  RecoveryGrowth.shiftCount (supportRate (K := K) (tick := tick) allocation)
    (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6) m

end MatrixMultiplication.AllFieldHistoryRecovery

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryGroupCore
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
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
open AllFieldHistoryMasks AllFieldHistoryRawMasks AllFieldHistoryIncomingMasks
open JointPopulation JointCanonicalization JointCanonicalCW InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem marginal_project (allocation : Allocation) (m : ℕ) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : JointCanonicalMixed.sideMask (activeCounts allocation m)
      activeHalfLength activeHalfLength AllFieldHistoryRecovery.halfLength_le_eight side w)
    (sigma : Placement) : marginal allocation m side sigma (projectRaw allocation m sigma w) := by
  intro h a
  exact hw h.val a

theorem received_project (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryIncomingMasks.received allocation m ε side w)
    (sigma : Placement) : received allocation m ε side sigma (projectRaw allocation m sigma w) := by
  intro h
  exact hw h.val

theorem rawPass_project (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryRawMasks.rawPass allocation m ε side w)
    (sigma : Placement) : rawPass allocation m ε side sigma (projectRaw allocation m sigma w) := by
  intro i hi
  exact hw i

theorem completeKeep_project (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryRecovery.completeKeep allocation m ε side w)
    (sigma : Placement) : completeKeep allocation m ε side sigma
      (projectRaw allocation m sigma w) :=
  ⟨marginal_project allocation m side w hw.1 sigma,
    received_project allocation m ε side w hw.2.1 sigma,
    rawPass_project allocation m ε side w hw.2.2 sigma⟩

theorem completeKeep_iff_all_groups (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3) (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    AllFieldHistoryRecovery.completeKeep allocation m ε side w ↔
      ∀ sigma, completeKeep allocation m ε side sigma (projectRaw allocation m sigma w) := by
  refine ⟨fun hw sigma => completeKeep_project allocation m ε side w hw sigma, ?_⟩
  intro hw
  refine ⟨?_, ?_, ?_⟩
  · intro h a
    exact (hw h.val.physicalOrder).1 ⟨h, rfl⟩ a
  · intro h
    exact (hw h.val.physicalOrder).2.1 ⟨h, rfl⟩
  · intro i
    exact (hw i.1.val.physicalOrder).2.2 i rfl

def groupRawSource (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ)
    (sigma : Placement) : Tensor F
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) :=
  sourceTensor (groupCounts allocation m sigma)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => AllFieldHistoryRecovery.parents F h.val)

def groupPreparedSource (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ)
    (ε : ℝ) (sigma : Placement) : Tensor F
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) :=
  ExactRecovery.delete (groupRawSource F allocation m sigma)
    (completeKeep allocation m ε 0 sigma) (completeKeep allocation m ε 1 sigma)
    (completeKeep allocation m ε 2 sigma)

theorem rawSource_factor (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ)
    (x y z : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    AllFieldHistoryRecovery.rawSource F allocation m x y z =
      ∏ sigma : Placement, groupRawSource F allocation m sigma
        (projectRaw allocation m sigma x) (projectRaw allocation m sigma y)
        (projectRaw allocation m sigma z) :=
  prod_active_eq_prod_orders (fun h => ∏ j,
    AllFieldHistoryRecovery.parents F h (x h j) (y h j) (z h j))

theorem preparedSource_factor (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ)
    (x y z : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    ExactRecovery.delete (AllFieldHistoryRecovery.rawSource F allocation m)
      (AllFieldHistoryRecovery.completeKeep allocation m ε 0)
      (AllFieldHistoryRecovery.completeKeep allocation m ε 1)
      (AllFieldHistoryRecovery.completeKeep allocation m ε 2) x y z =
      ∏ sigma : Placement, groupPreparedSource F allocation m ε sigma
        (projectRaw allocation m sigma x) (projectRaw allocation m sigma y)
        (projectRaw allocation m sigma z) := by
  have heq :
      (AllFieldHistoryRecovery.completeKeep allocation m ε 0 x ∧
        AllFieldHistoryRecovery.completeKeep allocation m ε 1 y ∧
        AllFieldHistoryRecovery.completeKeep allocation m ε 2 z) ↔
      ∀ sigma : Placement,
        completeKeep allocation m ε 0 sigma (projectRaw allocation m sigma x) ∧
        completeKeep allocation m ε 1 sigma (projectRaw allocation m sigma y) ∧
        completeKeep allocation m ε 2 sigma (projectRaw allocation m sigma z) := by
    rw [completeKeep_iff_all_groups, completeKeep_iff_all_groups, completeKeep_iff_all_groups]
    exact ⟨fun h sigma => ⟨h.1 sigma, h.2.1 sigma, h.2.2 sigma⟩,
      fun h => ⟨fun sigma => (h sigma).1, fun sigma => (h sigma).2.1,
        fun sigma => (h sigma).2.2⟩⟩
  by_cases h : AllFieldHistoryRecovery.completeKeep allocation m ε 0 x ∧
      AllFieldHistoryRecovery.completeKeep allocation m ε 1 y ∧
      AllFieldHistoryRecovery.completeKeep allocation m ε 2 z
  · rw [ExactRecovery.delete, ite_eq_left h, rawSource_factor]
    apply Finset.prod_congr rfl
    intro sigma _
    exact (ite_eq_left (heq.mp h sigma)).symm
  · rw [ExactRecovery.delete, ite_eq_right h]
    have hn : ¬∀ sigma : Placement,
        completeKeep allocation m ε 0 sigma (projectRaw allocation m sigma x) ∧
        completeKeep allocation m ε 1 sigma (projectRaw allocation m sigma y) ∧
        completeKeep allocation m ε 2 sigma (projectRaw allocation m sigma z) :=
      fun hh => h (heq.mpr hh)
    obtain ⟨sigma, hs⟩ := not_forall.mp hn
    exact (Finset.prod_eq_zero (Finset.mem_univ sigma) (ite_eq_right hs)).symm

end MatrixMultiplication.AllFieldHistoryGroupMasks

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistorySource

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldHistoryRegrouping AllFieldHistoryIncomingMasks
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ)

def toActive (w : Raw (K := K) (tick := tick) allocation m) :
    ActiveWords (K := K) (tick := tick) allocation m := fun h => incomingWord allocation m h w

theorem parent_coefficient (F : Type*) [Field F] (h : Active K tick)
    (x y z : Raw (K := K) (tick := tick) allocation m) :
    Tensor.power
      (CWStrands.shapeTensor (Fin (currentLength h.val.1.source))
        (currentPhysicalShape (h.val.1.source, h.val.2)))
      (population allocation m (h.val.1.source, h.val.2))
      (incomingWord allocation m h x) (incomingWord allocation m h y)
      (incomingWord allocation m h z) =
    ∏ i : JointPopulation.Positions (activeCounts allocation m) h,
      AllFieldHistoryRecovery.parents F h (x h i) (y h i) (z h i) := by
  change (∏ p : Fin (population allocation m (h.val.1.source, h.val.2)),
    CWStrands.shapeTensor _ _ (incomingWord allocation m h x p)
      (incomingWord allocation m h y p) (incomingWord allocation m h z p)) = _
  refine ((sourcePositionsEquiv allocation m h).prod_comp (fun p =>
    CWStrands.shapeTensor (Fin (currentLength h.val.1.source))
      (currentPhysicalShape (h.val.1.source, h.val.2))
      (incomingWord allocation m h x p) (incomingWord allocation m h y p)
      (incomingWord allocation m h z p))).symm.trans ?_
  apply Finset.prod_congr rfl
  intro i _
  simp only [incomingWord, Equiv.symm_apply_apply]
  erw [shapeTensor_joinHalves]
  unfold AllFieldHistoryRecovery.parents JointCanonicalMixed.inputTensor
  rw [ite_eq_left rfl]
  unfold JointCanonicalCW.parentTensor currentPhysicalShape
  rw [source_shape]
  rfl

def receivedSource (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  ExactRecovery.delete (AllFieldHistoryRecovery.rawSource F (K := K) (tick := tick) allocation m)
    (received allocation m ε 0) (received allocation m ε 1) (received allocation m ε 2)

theorem received_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : Raw (K := K) (tick := tick) allocation m) :
    activeTensor (K := K) (tick := tick) allocation m F ε (toActive allocation m x) (toActive allocation m y)
      (toActive allocation m z) = receivedSource (K := K) (tick := tick) allocation m F ε x y z := by
  change (∏ h : Active K tick, historyTensor F allocation m ε
    (h.val.1.source, h.val.2) (incomingWord allocation m h x)
      (incomingWord allocation m h y) (incomingWord allocation m h z)) = _
  unfold receivedSource ExactRecovery.delete
  by_cases hp : received allocation m ε 0 x ∧ received allocation m ε 1 y ∧
      received allocation m ε 2 z
  · rw [ite_eq_left hp]
    change _ = ∏ h : Active K tick, ∏ i : JointPopulation.Positions (activeCounts allocation m) h,
      AllFieldHistoryRecovery.parents F h (x h i) (y h i) (z h i)
    apply Finset.prod_congr rfl
    intro h _
    unfold historyTensor ExactRecovery.delete
    rw [ite_eq_left ⟨hp.1 h, hp.2.1 h, hp.2.2 h⟩]
    exact parent_coefficient allocation m F h x y z
  · rw [ite_eq_right hp]
    have hh : ∃ h : Active K tick,
        ¬(residentMask allocation m ε (h.val.1.source, h.val.2) 0 (incomingWord allocation m h x) ∧
          residentMask allocation m ε (h.val.1.source, h.val.2) 1 (incomingWord allocation m h y) ∧
          residentMask allocation m ε (h.val.1.source, h.val.2) 2 (incomingWord allocation m h z)) := by
      by_contra hn
      apply hp
      push Not at hn
      exact ⟨fun h => (hn h).1, fun h => (hn h).2.1, fun h => (hn h).2.2⟩
    obtain ⟨h, hh⟩ := hh
    apply Finset.prod_eq_zero (Finset.mem_univ h)
    exact ite_eq_right hh

def receivedMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (activeTensor (K := K) (tick := tick) allocation m F ε)
      (receivedSource (K := K) (tick := tick) allocation m F ε) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (toActive (K := K) (tick := tick) allocation m)
    (toActive (K := K) (tick := tick) allocation m)
    (toActive (K := K) (tick := tick) allocation m) _).symm.trans ?_⟩
  funext x y z
  exact received_coefficient allocation m F ε x y z

def preparedSource (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  ExactRecovery.delete (receivedSource (K := K) (tick := tick) allocation m F ε)
    (fun x => marginal (K := K) (tick := tick) allocation m 0 x ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 0 x)
    (fun y => marginal (K := K) (tick := tick) allocation m 1 y ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 1 y)
    (fun z => marginal (K := K) (tick := tick) allocation m 2 z ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 2 z)

theorem preparedSource_eq_delete (F : Type*) [Field F] (ε : ℝ) :
    preparedSource (K := K) (tick := tick) allocation m F ε =
      ExactRecovery.delete (AllFieldHistoryRecovery.rawSource F (K := K) (tick := tick) allocation m)
        (AllFieldHistoryRecovery.completeKeep allocation m ε 0)
        (AllFieldHistoryRecovery.completeKeep allocation m ε 1)
        (AllFieldHistoryRecovery.completeKeep allocation m ε 2) := by
  funext x y z
  unfold preparedSource receivedSource marginal AllFieldHistoryRecovery.completeKeep
    ExactRecovery.delete
  split_ifs <;> simp_all only [and_true, true_and, not_false_eq_true]
  all_goals tauto

def preparedMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (activeTensor (K := K) (tick := tick) allocation m F ε)
      (preparedSource (K := K) (tick := tick) allocation m F ε) :=
  (receivedMap (K := K) (tick := tick) allocation m F ε).comp (deleteWithPred (receivedSource (K := K) (tick := tick) allocation m F ε)
    (fun x => marginal (K := K) (tick := tick) allocation m 0 x ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 0 x)
    (fun y => marginal (K := K) (tick := tick) allocation m 1 y ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 1 y)
    (fun z => marginal (K := K) (tick := tick) allocation m 2 z ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 2 z))

end MatrixMultiplication.AllFieldHistorySource

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCanonicalSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCanonicalSymmetry

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization JointCanonicalCW
open JointCanonicalMixed HistorySymmetry PermutationMatching

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [CommRing F]
    (counts : H → Shape → ℕ) (leftLength rightLength : H → ℕ)
    (parentShape : H → Fin 3 → ℕ) (sharing : H → Bool)
    (hleft : ∀ h, leftLength h ≤ 8)
    {SL SR : H → Type*}
    [∀ h, Fintype (SL h)] [∀ h, Fintype (SR h)]
    [∀ h, DecidableEq (SL h)] [∀ h, DecidableEq (SR h)]
    (sl : Fin 3 → ∀ c : ClassKey (H := H), Left leftLength c.1 → SL c.1)
    (sr : Fin 3 → ∀ c : ClassKey (H := H), Right rightLength c.1 → SR c.1)
    (νl : Fin 3 → ∀ c : ClassKey (H := H), SL c.1 → ℝ)
    (νr : Fin 3 → ∀ c : ClassKey (H := H), SR c.1 → ℝ)
    (ηl ηr : Fin 3 → ClassKey (H := H) → ℝ)
    (hsupport : ∀ h u, 0 < counts h u → sharing h = true →
      ∀ s, shapeNat u s ≤ parentShape h s)

include hsupport

omit [DecidableEq H] [∀ h, Fintype (SL h)] [∀ h, Fintype (SR h)] in
theorem canonicalIdeal_smul
    (g : HalfClassPermutations (ClassPositions counts))
    (x y z : CanonicalPairs counts (Left leftLength) (Right rightLength)) :
    canonicalIdeal counts (Left leftLength) (Right rightLength)
      (inputTensor (F := F) leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) sl sr νl νr ηl ηr
      (g • x) (g • y) (g • z) =
    canonicalIdeal counts (Left leftLength) (Right rightLength)
      (inputTensor leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) sl sr νl νr ηl ηr x y z := by
  simp only [canonicalIdeal,
    JointCanonicalMixed.canonicalBase_eq_children counts leftLength rightLength
      parentShape sharing hleft hsupport,
    ExactRecovery.delete, childWindows_smul, pairClassProduct_smul]

omit [DecidableEq H] in
theorem rawIdeal_smul (e : Target counts) :
    letI rawInst : MulAction (HalfClassPermutations (ClassPositions counts))
        (RawPairs counts (Left leftLength) (Right rightLength)) :=
      EquivOrbitTransport.action (pairEquiv counts (Left leftLength) (Right rightLength) e)
    ∀ (g : HalfClassPermutations (ClassPositions counts))
      (x y z : RawPairs counts (Left leftLength) (Right rightLength)),
      JointCanonicalization.ideal counts (Left leftLength) (Right rightLength)
        (inputTensor (F := F) leftLength rightLength parentShape sharing)
        (coarse leftLength rightLength hleft) sl sr νl νr ηl ηr e
        (@SMul.smul _ _ rawInst.toSMul g x)
        (@SMul.smul _ _ rawInst.toSMul g y)
        (@SMul.smul _ _ rawInst.toSMul g z) =
      JointCanonicalization.ideal counts (Left leftLength) (Right rightLength)
        (inputTensor leftLength rightLength parentShape sharing)
        (coarse leftLength rightLength hleft) sl sr νl νr ηl ηr e x y z := by
  refine EquivOrbitTransport.coefficients_preserved
    (G := HalfClassPermutations (ClassPositions counts))
    (pairEquiv counts (Left leftLength) (Right rightLength) e)
    (pairEquiv counts (Left leftLength) (Right rightLength) e)
    (pairEquiv counts (Left leftLength) (Right rightLength) e)
    (JointCanonicalization.ideal counts (Left leftLength) (Right rightLength)
      (inputTensor (F := F) leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) sl sr νl νr ηl ηr e)
    (canonicalIdeal counts (Left leftLength) (Right rightLength)
      (inputTensor (F := F) leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) sl sr νl νr ηl ηr) ?_ ?_
  · exact ideal_eq_canonicalIdeal counts (Left leftLength) (Right rightLength)
      (inputTensor leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) sl sr νl νr ηl ηr e
  · exact canonicalIdeal_smul counts leftLength rightLength parentShape sharing hleft
      sl sr νl νr ηl ηr hsupport

end MatrixMultiplication.JointCanonicalSymmetry

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryRecovery
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.nativeSplitWeightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.initialExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.terminalExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.sidePermutation_refl _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.retarget_copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryMasks

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistorySupport
open JointCanonicalization InheritedMasks PermutationMatching HistorySymmetry
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem testedClasses_parent (allocation : Allocation) (i : MaskIndex K tick)
    (c : Classes K tick) (hc : c ∈ testedClasses allocation i) : c.1 = i.1 :=
  (Finset.mem_filter.mp hc).2.1

theorem rightProbability_le_one (allocation : Allocation) (side : Fin 3)
    (i : MaskIndex K tick) (c : Classes K tick) (hc : c ∈ testedClasses allocation i) :
    rightProbability side i c ≤ 1 := by
  have hsum := rightLaw_normalized allocation 1 c.1 c.2
    (positiveClasses_positive allocation i.1 c hc) side
  rw [← hsum]
  exact Finset.single_le_sum (fun a _ => rightLaw_nonnegative c.1 c.2 side a)
    (Finset.mem_univ _)

theorem left_density_le (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (side : Fin 3) (w : Words (K := K) (tick := tick) allocation m)
    (hw : childWindows allocation m ε side w) (i : MaskIndex K tick)
    (c : Classes K tick) (hc : c ∈ testedClasses allocation i) :
    |classDensity (wordPairLeftPositions w classStatistic (leftSymbol i)) c -
      leftProbability side i c| ≤ childWidth ε i.1 := by
  have hp : 0 < activeCounts allocation m c.1 c.2 :=
    (activeCounts_pos_iff allocation hm c.1 c.2).2
      (positiveClasses_positive allocation i.1 c hc)
  have ht := (hw c).1 (leftSymbol i c)
  have hh := testedClasses_parent allocation i c hc
  have ht' : |empiricalLaw (classStatistic c ∘ w.left c) (leftSymbol i c) -
      leftProbability side i c| ≤ childWidth ε c.1 := by
    simpa only [activeLaw, activeWidth, ite_eq_left hp, leftProbability] using ht
  have hd := classDensity_statisticPositions w.left classStatistic (leftSymbol i) c
  change classDensity (wordPairLeftPositions w classStatistic (leftSymbol i)) c = _ at hd
  rw [hd]
  exact ht'.trans_eq (congrArg (childWidth ε) hh)

theorem right_density_le (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (side : Fin 3) (w : Words (K := K) (tick := tick) allocation m)
    (hw : childWindows allocation m ε side w) (i : MaskIndex K tick)
    (c : Classes K tick) (hc : c ∈ testedClasses allocation i) :
    |classDensity (wordPairRightPositions w classStatistic (rightSymbol i)) c -
      rightProbability side i c| ≤ childWidth ε i.1 := by
  have hp : 0 < activeCounts allocation m c.1 c.2 :=
    (activeCounts_pos_iff allocation hm c.1 c.2).2
      (positiveClasses_positive allocation i.1 c hc)
  have ht := (hw c).2 (rightSymbol i c)
  have hh := testedClasses_parent allocation i c hc
  have ht' : |empiricalLaw (classStatistic c ∘ w.right c) (rightSymbol i c) -
      rightProbability side i c| ≤ childWidth ε c.1 := by
    simpa only [activeLaw, activeWidth, ite_eq_left hp, rightProbability] using ht
  have hd := classDensity_statisticPositions w.right classStatistic (rightSymbol i) c
  change classDensity (wordPairRightPositions w classStatistic (rightSymbol i)) c = _ at hd
  rw [hd]
  exact ht'.trans_eq (congrArg (childWidth ε) hh)

theorem mixture_error_zero (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (side : Fin 3) (i : MaskIndex K tick) :
    |classProductMixture (fun c : testedClasses allocation i => Positions allocation m c.val)
      (fun c => leftProbability side i c.val) (fun c => rightProbability side i c.val) -
        center allocation side i| ≤ (0 : ℝ) := by
  rw [selected_classProductMixture_eq_one allocation hm]
  simp only [center, sub_self, abs_zero, le_refl]

attribute [local irreducible] activeCounts

theorem full_filter_loss_le (allocation : Allocation) {m : ℕ} (hm : 2 ≤ m)
    {ε : ℝ} (hε : 0 < ε) (side : Fin 3)
    (w : Words (K := K) (tick := tick) allocation m)
    (hw : childWindows allocation m ε side w) :
    ((rejectedFilter
      (fullOrbitFilter (HalfClassPermutations (Positions (K := K) (tick := tick) allocation m)) w)
      (fun v => ∃ i : MaskIndex K tick,
        selectedWordPairMaskBad (testedClasses allocation i) classStatistic classStatistic
          (leftSymbol i) (rightSymbol i) (pairWidth ε i.1) (center allocation side i) v)).card : ℝ) /
      (fullOrbitFilter
        (HalfClassPermutations (Positions (K := K) (tick := tick) allocation m)) w).card ≤
      lossConstant (K := K) (tick := tick) allocation ε / m := by
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hsize (i : MaskIndex K tick) :
      populationSize (fun c : testedClasses allocation i => Positions allocation m c.val) =
        selectedBasePopulation allocation (testedClasses allocation i) * m :=
    selected_populationSize allocation m (testedClasses allocation i)
  have hn (i : MaskIndex K tick) (c : Classes K tick)
      (hc : c ∈ testedClasses allocation i) : 2 ≤ Fintype.card (Positions allocation m c) := by
    exact selected_two_le allocation hm (testedClasses allocation i)
      (positiveClasses_positive allocation i.1) ⟨c, hc⟩
  have hmass (i : MaskIndex K tick) :
      0 < selectedBasePopulation allocation (testedClasses allocation i) :=
    positiveClasses_basePopulation_pos allocation i.1
  have hright0 (i : MaskIndex K tick) (c : Classes K tick)
      (_hc : c ∈ testedClasses allocation i) : 0 ≤ rightProbability side i c :=
    rightLaw_nonnegative c.1 c.2 side _
  have h := finite_selectedWordPair_full_filter_inverse_linear_of_windows
    (C := Classes K tick) (P := Positions (K := K) (tick := tick) allocation m)
    (X := Letters) (Y := Letters) (I := MaskIndex K tick)
    (SL := fun _ c => Statistic c.1) (SR := fun _ c => Statistic c.1)
    (testedClasses allocation) w (fun _ => classStatistic) (fun _ => classStatistic)
    leftSymbol rightSymbol hn
    (fun i => selectedBasePopulation allocation (testedClasses allocation i)) (m : ℝ)
    (by exact_mod_cast hmpos) hmass hsize
    (leftProbability side) (rightProbability side)
    (fun i => pairWidth ε i.1) (fun i => childWidth ε i.1) (fun _ => 0)
    (center allocation side) (fun i => pairWidth_pos hε i.1)
    hright0 (rightProbability_le_one allocation side)
    (left_density_le allocation hmpos ε side w hw)
    (right_density_le allocation hmpos ε side w hw)
    (mixture_error_zero allocation hmpos side) (fun _ => le_rfl)
    (fun i => (div_pos (pairWidth_pos hε i.1) (by norm_num : (0 : ℝ) < 4)).le)
  simpa only [lossConstant] using h

end MatrixMultiplication.AllFieldHistoryMasks

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryRecovery

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistoryChildLaws
open AllFieldHistorySupport JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem ideal_coordinates (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (e : Targets (K := K) (tick := tick) allocation m)
    (x y z : Raw (K := K) (tick := tick) allocation m) :
    ideal F allocation m ε e x y z = canonical F allocation m ε
      (coordinates allocation m e x) (coordinates allocation m e y)
      (coordinates allocation m e z) :=
  ideal_eq_canonicalIdeal (activeCounts allocation m) (Left activeHalfLength)
    (Right activeHalfLength) (parents F)
    (coarse activeHalfLength activeHalfLength halfLength_le_eight)
    childStatistic childStatistic leftPrescription rightPrescription
    (outputWidth ε) (outputWidth ε) e x y z

theorem ideal_support_windows (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (e : Targets (K := K) (tick := tick) allocation m)
    (x y z : Raw (K := K) (tick := tick) allocation m) (hq : ideal F allocation m ε e x y z ≠ 0) :
    AllFieldHistoryMasks.childWindows allocation m ε 0 (coordinates allocation m e x) ∧
    AllFieldHistoryMasks.childWindows allocation m ε 1 (coordinates allocation m e y) ∧
    AllFieldHistoryMasks.childWindows allocation m ε 2 (coordinates allocation m e z) := by
  by_contra hn
  apply hq
  rw [ideal_coordinates]
  change (if AllFieldHistoryMasks.childWindows allocation m ε 0 (coordinates allocation m e x) ∧
      AllFieldHistoryMasks.childWindows allocation m ε 1 (coordinates allocation m e y) ∧
      AllFieldHistoryMasks.childWindows allocation m ε 2 (coordinates allocation m e z)
    then _ else 0) = 0
  exact ite_eq_right hn

theorem raw_pair_loss_le (allocation : Allocation) {m : ℕ} (hm : 2 ≤ m)
    {ε : ℝ} (hε : 0 < ε) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m) (w : Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryMasks.childWindows allocation m ε side
      (coordinates allocation m e w)) :
    letI _rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
    (((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => ¬AllFieldHistoryRawMasks.rawPass allocation m ε side v)).card : ℝ) /
        (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).card ≤
      AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε / m := by
  let rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
  have htransport := EquivOrbitTransport.rejected_fraction
    (G := Symmetries (K := K) (tick := tick) allocation m) (coordinates allocation m e)
    (fun v => ¬AllFieldHistoryRawMasks.rawPass allocation m ε side v) w
  have hcanonical := orbit_bad_fraction_eq_fullOrbitFilter_of_iff
    (G := Symmetries (K := K) (tick := tick) allocation m)
    (coordinates allocation m e w)
    ((fun v => ¬AllFieldHistoryRawMasks.rawPass allocation m ε side v) ∘
      (coordinates allocation m e).symm)
    (fun v => ∃ i : AllFieldHistoryMasks.MaskIndex K tick,
      selectedWordPairMaskBad (AllFieldHistoryMasks.testedClasses allocation i)
        AllFieldHistoryMasks.classStatistic AllFieldHistoryMasks.classStatistic
        (AllFieldHistoryMasks.leftSymbol i) (AllFieldHistoryMasks.rightSymbol i)
        (AllFieldHistoryMasks.pairWidth ε i.1) (AllFieldHistoryMasks.center allocation side i) v)
    (fun v => by
      change ¬AllFieldHistoryRawMasks.rawPass allocation m ε side
        ((coordinates allocation m e).symm v) ↔ _
      rw [← AllFieldHistoryRawMasks.passes_pairEquiv_iff_rawPass allocation m ε side e]
      change ¬AllFieldHistoryMasks.passes allocation m ε side
        ((coordinates allocation m e) ((coordinates allocation m e).symm v)) ↔ _
      rw [Equiv.apply_symm_apply]
      simp only [AllFieldHistoryMasks.passes, not_forall, not_not])
  exact htransport.trans_le (hcanonical.trans_le
    (AllFieldHistoryMasks.full_filter_loss_le allocation hm hε side
      (coordinates allocation m e w) hw))

theorem ideal_support_marginals (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (e : Targets (K := K) (tick := tick) allocation m)
    (x y z : Raw (K := K) (tick := tick) allocation m) (hq : ideal F allocation m ε e x y z ≠ 0) :
    JointCanonicalMixed.sideMask (activeCounts allocation m)
        activeHalfLength activeHalfLength halfLength_le_eight 0 x ∧
    JointCanonicalMixed.sideMask (activeCounts allocation m)
        activeHalfLength activeHalfLength halfLength_le_eight 1 y ∧
    JointCanonicalMixed.sideMask (activeCounts allocation m)
        activeHalfLength activeHalfLength halfLength_le_eight 2 z := by
  exact JointCanonicalMixed.ideal_support_masks (activeCounts allocation m)
    activeHalfLength activeHalfLength activeParentShape (fun _ => true)
    halfLength_le_eight e _ _ _ x y z hq

theorem ideal_support_weights (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (e : Targets (K := K) (tick := tick) allocation m)
    (x y z : Raw (K := K) (tick := tick) allocation m) (hq : ideal F allocation m ε e x y z ≠ 0) :
    sideWeights allocation m 0 e x ∧ sideWeights allocation m 1 e y ∧
      sideWeights allocation m 2 e z := by
  have hb : coarseIdeal (activeCounts allocation m)
      (Left activeHalfLength) (Right activeHalfLength) (parents F)
      (coarse activeHalfLength activeHalfLength halfLength_le_eight) e x y z ≠ 0 := by
    intro hz
    apply hq
    simp only [ideal, JointCanonicalization.ideal, ExactRecovery.delete, hz, ite_self]
  have hc :
      coarseMask (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
        (coarse activeHalfLength activeHalfLength halfLength_le_eight) 0 e x ∧
      coarseMask (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
        (coarse activeHalfLength activeHalfLength halfLength_le_eight) 1 e y ∧
      coarseMask (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
        (coarse activeHalfLength activeHalfLength halfLength_le_eight) 2 e z := by
    by_contra hn
    exact hb (by simp only [coarseIdeal, ExactRecovery.delete, ite_eq_right hn])
  have hs : rawSource F allocation m x y z ≠ 0 := by
    intro hz
    apply hb
    change (if _ then rawSource F allocation m x y z else 0) = 0
    simp only [hz, ite_self]
  have ht (h : Active K tick) (j : JointPopulation.Positions (activeCounts allocation m) h) :
      parents F h (x h j) (y h j) (z h j) ≠ 0 := by
    intro hz
    apply hs
    unfold rawSource sourceTensor InheritedMasks.classProduct
    exact Finset.prod_eq_zero (Finset.mem_univ h)
      (Finset.prod_eq_zero (Finset.mem_univ j) hz)
  have hp (h : Active K tick) (j : JointPopulation.Positions (activeCounts allocation m) h) :
      CWStrands.weight (x h j).1 + CWStrands.weight (x h j).2 = activeParentShape h 0 ∧
      CWStrands.weight (y h j).1 + CWStrands.weight (y h j).2 = activeParentShape h 1 ∧
      CWStrands.weight (z h j).1 + CWStrands.weight (z h j).2 = activeParentShape h 2 := by
    have hh := ht h j
    change CWStrands.shapeTensor
      (Fin (activeHalfLength h) ⊕ Fin (activeHalfLength h)) (activeParentShape h)
      (Sum.elim (x h j).1 (x h j).2) (Sum.elim (y h j).1 (y h j).2)
      (Sum.elim (z h j).1 (z h j).2) ≠ 0 at hh
    simpa only [CWStrands.weight_sum_elim] using
      CWStrands.shapeTensor_support (activeParentShape h) _ _ _ hh
  have hx (h : Active K tick) (j : JointPopulation.Positions (activeCounts allocation m) h) :
      CWStrands.weight (x h j).1 = (shapeSide 0 ((e h).val j)).val :=
    congrArg Fin.val (hc.1 h j)
  have hy (h : Active K tick) (j : JointPopulation.Positions (activeCounts allocation m) h) :
      CWStrands.weight (y h j).1 = (shapeSide 1 ((e h).val j)).val :=
    congrArg Fin.val (hc.2.1 h j)
  have hz (h : Active K tick) (j : JointPopulation.Positions (activeCounts allocation m) h) :
      CWStrands.weight (z h j).1 = (shapeSide 2 ((e h).val j)).val :=
    congrArg Fin.val (hc.2.2 h j)
  refine ⟨?_, ?_, ?_⟩
  · intro h j
    refine ⟨hx h j, ?_⟩
    have hh := (hp h j).1
    rw [hx h j] at hh
    omega
  · intro h j
    refine ⟨hy h j, ?_⟩
    have hh := (hp h j).2.1
    rw [hy h j] at hh
    omega
  · intro h j
    refine ⟨hz h j, ?_⟩
    have hh := (hp h j).2.2
    rw [hz h j] at hh
    omega

theorem stageCWeights_of_sideWeights (allocation : Allocation) (m : ℕ) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m) (w : Raw (K := K) (tick := tick) allocation m)
    (hw : sideWeights allocation m side e w) :
    AllFieldHistoryIncomingMasks.stageCWeights allocation m side e w := by
  intro h phi ht j
  have hh := hw (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j
  change (∑ index : Fin 1, CWLeafStatistics.weight
      ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).1 index)) = _ ∧
    (∑ index : Fin 1, CWLeafStatistics.weight
      ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).2 index)) = _ at hh
  simpa only [Fin.sum_univ_one] using hh

theorem completeKeep_of_supported (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m) (w : Raw (K := K) (tick := tick) allocation m)
    (hmarginal : JointCanonicalMixed.sideMask (activeCounts allocation m)
      activeHalfLength activeHalfLength halfLength_le_eight side w)
    (hweights : sideWeights allocation m side e w)
    (hpass : AllFieldHistoryRawMasks.rawPass allocation m ε side w) :
    completeKeep allocation m ε side w :=
  ⟨hmarginal, AllFieldHistoryIncomingMasks.received_of_rawPass allocation hm hε side e w
    hpass (stageCWeights_of_sideWeights allocation m side e w hweights), hpass⟩

theorem occupied_split_le (allocation : Allocation) (m : ℕ)
    (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) :
    ∀ s, shapeNat u s ≤ activeParentShape h s :=
  jointCounts_support_le allocation m h.val u hu

theorem ideal_smul (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (e : Targets (K := K) (tick := tick) allocation m) :
    letI rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
    ∀ (g : Symmetries (K := K) (tick := tick) allocation m) (x y z : Raw (K := K) (tick := tick) allocation m),
      ideal F allocation m ε e ((@SMul.smul _ _ rawInst.toSMul g x)) ((@SMul.smul _ _ rawInst.toSMul g y)) ((@SMul.smul _ _ rawInst.toSMul g z)) = ideal F allocation m ε e x y z := by
  exact JointCanonicalSymmetry.rawIdeal_smul (activeCounts allocation m)
    activeHalfLength activeHalfLength activeParentShape (fun _ => true)
    halfLength_le_eight childStatistic childStatistic leftPrescription rightPrescription
    (outputWidth ε) (outputWidth ε)
    (fun h u hu _ => occupied_split_le allocation m h u hu) e

def Used (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (e : Targets (K := K) (tick := tick) allocation m) (side : Fin 3)
    (w : Raw (K := K) (tick := tick) allocation m) : Prop :=
  ∃ x y z, ideal F allocation m ε e x y z ≠ 0 ∧ sideVariable side x y z = w

theorem used_windows (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (e : Targets (K := K) (tick := tick) allocation m)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m) (hw : Used F allocation m ε e side w) :
    AllFieldHistoryMasks.childWindows allocation m ε side (coordinates allocation m e w) := by
  obtain ⟨x, y, z, hq, rfl⟩ := hw
  have hh := ideal_support_windows F allocation m ε e x y z hq
  fin_cases side
  · exact hh.1
  · exact hh.2.1
  · exact hh.2.2

theorem used_keep_iff_rawPass (F : Type*) [CommRing F] (allocation : Allocation)
    {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 ≤ ε)
    (e : Targets (K := K) (tick := tick) allocation m)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m) (hw : Used F allocation m ε e side w) :
    completeKeep allocation m ε side w ↔ AllFieldHistoryRawMasks.rawPass allocation m ε side w := by
  refine ⟨fun h => h.2.2, ?_⟩
  intro hp
  obtain ⟨x, y, z, hq, rfl⟩ := hw
  have hmg := ideal_support_marginals F allocation m ε e x y z hq
  have hwt := ideal_support_weights F allocation m ε e x y z hq
  fin_cases side
  · exact completeKeep_of_supported allocation hm hε 0 e x hmg.1 hwt.1 hp
  · exact completeKeep_of_supported allocation hm hε 1 e y hmg.2.1 hwt.2.1 hp
  · exact completeKeep_of_supported allocation hm hε 2 e z hmg.2.2 hwt.2.2 hp

theorem used_smul (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (e : Targets (K := K) (tick := tick) allocation m)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m) :
    letI rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
    ∀ g : Symmetries (K := K) (tick := tick) allocation m, Used F allocation m ε e side w →
      Used F allocation m ε e side ((@SMul.smul _ _ rawInst.toSMul g w)) := by
  let rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
  intro g hw
  obtain ⟨x, y, z, hq, rfl⟩ := hw
  refine ⟨(@SMul.smul _ _ rawInst.toSMul g x), (@SMul.smul _ _ rawInst.toSMul g y), (@SMul.smul _ _ rawInst.toSMul g z), ?_, ?_⟩
  · rwa [ideal_smul]
  · fin_cases side <;> rfl

theorem deterministic_loss_le (F : Type*) [CommRing F] (allocation : Allocation)
    {m : ℕ} (hm : 2 ≤ m) {ε : ℝ} (hε : 0 < ε)
    (e : Targets (K := K) (tick := tick) allocation m)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m) (hw : Used F allocation m ε e side w) :
    letI _rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
    (((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => ¬completeKeep allocation m ε side v)).card : ℝ) /
        (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).card ≤
      AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε / m := by
  let rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have heq : ((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => ¬completeKeep allocation m ε side v)) =
      ((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => ¬AllFieldHistoryRawMasks.rawPass allocation m ε side v)) := by
    apply Finset.filter_congr
    intro v hv
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hv
    exact not_congr (used_keep_iff_rawPass F allocation hmpos hε.le e side _
      (used_smul F allocation m ε e side w g hw))
  rw [heq]
  exact raw_pair_loss_le allocation hm hε side e w
    (used_windows F allocation m ε e side w hw)

def holedIdeal (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (e : Targets (K := K) (tick := tick) allocation m)
    (assigned : Fin 3 → Raw (K := K) (tick := tick) allocation m → Prop) :
    Tensor F (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  ExactRecovery.delete (ideal F allocation m ε e)
    (fun w => assigned 0 w ∧ completeKeep allocation m ε 0 w)
    (fun w => assigned 1 w ∧ completeKeep allocation m ε 1 w)
    (fun w => assigned 2 w ∧ completeKeep allocation m ε 2 w)

theorem ideal_eq_delete_source (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (e : Targets (K := K) (tick := tick) allocation m) :
    ideal F allocation m ε e = ExactRecovery.delete (rawSource F allocation m)
      (idealSide allocation m ε 0 e) (idealSide allocation m ε 1 e)
      (idealSide allocation m ε 2 e) := by
  funext x y z
  simp only [ideal, JointCanonicalization.ideal, coarseIdeal, rawSource,
    idealSide, ExactRecovery.delete]
  split_ifs <;> simp_all
  rename_i hnot
  symm
  apply ite_eq_right
  intro hkeep
  exact hnot hkeep.1.2 hkeep.2.1.2 hkeep.2.2.2

theorem branch_eq_holedIdeal {I : Type*} (F : Type*) [CommRing F]
    (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (a : JointExtraction.Assignment (Raw (K := K) (tick := tick) allocation m)
      (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) I)
    (i : I) (e : Targets (K := K) (tick := tick) allocation m)
    (hx : ∀ w, a.x w = some i → idealSide allocation m ε 0 e w)
    (hy : ∀ w, a.y w = some i → idealSide allocation m ε 1 e w)
    (hz : ∀ w, a.z w = some i → idealSide allocation m ε 2 e w) :
    JointExtraction.branch
      (ExactRecovery.delete (rawSource F allocation m)
        (completeKeep allocation m ε 0) (completeKeep allocation m ε 1)
        (completeKeep allocation m ε 2)) a i =
      holedIdeal F allocation m ε e
        (fun side w => sideVariable side (a.x w = some i) (a.y w = some i) (a.z w = some i)) := by
  funext x y z
  simp only [holedIdeal, sideVariable_zero, sideVariable_one, sideVariable_two]
  by_cases ha : a.x x = some i ∧ a.y y = some i ∧ a.z z = some i
  · have hix := hx x ha.1
    have hiy := hy y ha.2.1
    have hiz := hz z ha.2.2
    rw [JointExtraction.branch, ite_eq_left ha, ideal_eq_delete_source]
    simp only [ExactRecovery.delete, hix, hiy, hiz, ha.1, ha.2.1, ha.2.2,
      true_and, ite_true, if_true]
  · have hnot : ¬((a.x x = some i ∧ completeKeep allocation m ε 0 x) ∧
        (a.y y = some i ∧ completeKeep allocation m ε 1 y) ∧
        (a.z z = some i ∧ completeKeep allocation m ε 2 z)) :=
      fun h => ha ⟨h.1.1, h.2.1.1, h.2.2.1⟩
    rw [JointExtraction.branch, ite_eq_right ha]
    simp only [ExactRecovery.delete, ite_eq_right hnot]

theorem repair_selected (F : Type*) [CommRing F] (allocation : Allocation)
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hm : minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (e : Targets (K := K) (tick := tick) allocation m)
    (assigned : Fin 3 → Raw (K := K) (tick := tick) allocation m → Prop)
    (hcollision :
      letI _rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
      ∀ side w, Used F allocation m ε e side w →
        (((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
          (fun v => completeKeep allocation m ε side v ∧ ¬assigned side v)).card : ℝ) /
          (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).card ≤ 6 / m) :
    InverseLinearRecovery.RecoveredBy (ideal F allocation m ε e)
      (holedIdeal F allocation m ε e assigned) (shiftCount (K := K) (tick := tick) allocation ε m) := by
  let rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
  have hm' := minimumDilation_spec allocation ε hm
  have hc : 0 < AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6 := by
    have := AllFieldHistoryMasks.lossConstant_nonneg (K := K) (tick := tick) allocation ε
    linarith
  have hloss (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m)
      (hw : Used F allocation m ε e side w) :
      (((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
        (fun v => ¬(assigned side v ∧ completeKeep allocation m ε side v))).card : ℝ) /
        (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).card ≤
      (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6) / m := by
    have heq : ((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
        (fun v => ¬(assigned side v ∧ completeKeep allocation m ε side v))) =
        ((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
        (fun v => ¬(completeKeep allocation m ε side v ∧ assigned side v))) := by
      ext v
      simp only [Finset.mem_filter]
      exact and_congr Iff.rfl (not_congr and_comm)
    rw [heq]
    rw [OrbitLoss.missing_fraction_partition
      (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w)
      (completeKeep allocation m ε side) (assigned side), add_div]
    exact add_le_add (deterministic_loss_le F allocation hm'.1 hε e side w hw)
      (hcollision side w hw)
  unfold holedIdeal shiftCount
  refine InverseLinearRecovery.repair_inverse_linear (G := Symmetries (K := K) (tick := tick) allocation m)
    (ideal F allocation m ε e)
    (fun w => assigned 0 w ∧ completeKeep allocation m ε 0 w)
    (fun w => assigned 1 w ∧ completeKeep allocation m ε 1 w)
    (fun w => assigned 2 w ∧ completeKeep allocation m ε 2 w)
    (ideal_smul F allocation m ε e) (supportRate_pos (K := K) (tick := tick) allocation).le hc hm'.2 ?_ ?_ ?_ ?_
  · rw [support_filter_eq]
    exact raw_support_card_le_exp allocation m (ideal F allocation m ε e)
  · intro x hx
    obtain ⟨y, z, hq⟩ := hx
    exact hloss 0 x ⟨x, y, z, hq, rfl⟩
  · intro y hy
    obtain ⟨x, z, hq⟩ := hy
    exact hloss 1 y ⟨x, y, z, hq, rfl⟩
  · intro z hz
    obtain ⟨x, y, hq⟩ := hz
    exact hloss 2 z ⟨x, y, z, hq, rfl⟩

theorem repair_selected_branch {I : Type*} (F : Type*) [CommRing F]
    (allocation : Allocation) {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hm : minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (a : JointExtraction.Assignment (Raw (K := K) (tick := tick) allocation m)
      (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) I)
    (i : I) (e : Targets (K := K) (tick := tick) allocation m)
    (hx : ∀ w, a.x w = some i → idealSide allocation m ε 0 e w)
    (hy : ∀ w, a.y w = some i → idealSide allocation m ε 1 e w)
    (hz : ∀ w, a.z w = some i → idealSide allocation m ε 2 e w)
    (hcollision :
      letI _rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
      ∀ side w, Used F allocation m ε e side w →
        (((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
          (fun v => completeKeep allocation m ε side v ∧
            ¬sideVariable side (a.x v = some i) (a.y v = some i) (a.z v = some i))).card : ℝ) /
          (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).card ≤ 6 / m) :
    InverseLinearRecovery.RecoveredBy (ideal F allocation m ε e)
      (JointExtraction.branch
        (ExactRecovery.delete (rawSource F allocation m)
          (completeKeep allocation m ε 0) (completeKeep allocation m ε 1)
          (completeKeep allocation m ε 2)) a i) (shiftCount (K := K) (tick := tick) allocation ε m) := by
  rw [branch_eq_holedIdeal F allocation m ε a i e hx hy hz]
  exact repair_selected F allocation hε hm e _ hcollision

end MatrixMultiplication.AllFieldHistoryRecovery

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistorySourceAssignment
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.nativeSplitWeightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial




section





noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupedRecovery

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem idealSide_iff_all_groups (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    AllFieldHistoryRecovery.idealSide allocation m ε side e w ↔
      ∀ sigma, groupIdealSide allocation m ε side sigma
        (projectTarget allocation m sigma e) (projectRaw allocation m sigma w) := by
  constructor
  · intro hw sigma
    exact ⟨fun h j => hw.1 h.val j, fun h u hu => hw.2 h.val u hu⟩
  · intro hw
    exact ⟨fun h j => (hw h.val.physicalOrder).1 ⟨h, rfl⟩ j,
      fun h u hu => (hw h.val.physicalOrder).2 ⟨h, rfl⟩ u hu⟩

theorem groupedAssignment_sound (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (i : ∀ sigma, E sigma) (e : ∀ sigma, GroupTarget (K := K) (tick := tick) allocation m sigma)
    (hx : ∀ sigma w, (a sigma).x w = some (i sigma) →
      groupIdealSide allocation m ε 0 sigma (e sigma) w)
    (hy : ∀ sigma w, (a sigma).y w = some (i sigma) →
      groupIdealSide allocation m ε 1 sigma (e sigma) w)
    (hz : ∀ sigma w, (a sigma).z w = some (i sigma) →
      groupIdealSide allocation m ε 2 sigma (e sigma) w) :
    (∀ w, (groupedAssignment allocation m E a).x w = some i →
      AllFieldHistoryRecovery.idealSide allocation m ε 0
        (joinGroupTargets (activeCounts allocation m) e) w) ∧
    (∀ w, (groupedAssignment allocation m E a).y w = some i →
      AllFieldHistoryRecovery.idealSide allocation m ε 1
        (joinGroupTargets (activeCounts allocation m) e) w) ∧
    (∀ w, (groupedAssignment allocation m E a).z w = some i →
      AllFieldHistoryRecovery.idealSide allocation m ε 2
        (joinGroupTargets (activeCounts allocation m) e) w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    apply (idealSide_iff_all_groups allocation m ε 0 _ w).2
    intro sigma
    rw [project_joinGroupTargets]
    exact hx sigma _ ((GroupAssignment.collect_eq_some _ _ _).mp hw sigma)
  · intro w hw
    apply (idealSide_iff_all_groups allocation m ε 1 _ w).2
    intro sigma
    rw [project_joinGroupTargets]
    exact hy sigma _ ((GroupAssignment.collect_eq_some _ _ _).mp hw sigma)
  · intro w hw
    apply (idealSide_iff_all_groups allocation m ε 2 _ w).2
    intro sigma
    rw [project_joinGroupTargets]
    exact hz sigma _ ((GroupAssignment.collect_eq_some _ _ _).mp hw sigma)

theorem grouped_collision_le (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (i : ∀ sigma, E sigma) (e : ∀ sigma, GroupTarget (K := K) (tick := tick) allocation m sigma)
    (side : Fin 3) (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hbound : ∀ sigma,
      (((localOrbit allocation m sigma (e sigma) (projectRaw allocation m sigma w)).filter
        (fun v => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma v ∧
          ¬localAssigned allocation m sigma (a sigma) (i sigma) side v)).card : ℝ) /
        (localOrbit allocation m sigma (e sigma) (projectRaw allocation m sigma w)).card ≤ 1 / m) :
    letI : MulAction (AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m)
      (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :=
        AllFieldHistoryRecovery.rawAction allocation m (joinGroupTargets (activeCounts allocation m) e)
    (((OrbitCounting.orbitSet (G := AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => AllFieldHistoryRecovery.completeKeep allocation m ε side v ∧
        ¬AllFieldHistoryRecovery.sideVariable side
          ((groupedAssignment allocation m E a).x v = some i)
          ((groupedAssignment allocation m E a).y v = some i)
          ((groupedAssignment allocation m E a).z v = some i))).card : ℝ) /
      (OrbitCounting.orbitSet (G := AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m) w).card ≤ 6 / m := by
  let target := joinGroupTargets (activeCounts allocation m) e
  let : MulAction (AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m)
      (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) := AllFieldHistoryRecovery.rawAction allocation m target
  have hb (sigma : Placement) :
      ((rejectedFilter (GroupOrbitProjection.rawOrbit
        (GroupOrbitProjection.groupCounts (activeCounts allocation m)
          (fun h : Active K tick => h.val.physicalOrder = sigma))
        (fun h => Left activeHalfLength h.val) (fun h => Right activeHalfLength h.val)
        (GroupOrbitProjection.projectTarget (activeCounts allocation m)
          (fun h => h.val.physicalOrder = sigma) target)
        (projectRaw allocation m sigma w))
        (fun v => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma v ∧
          ¬localAssigned allocation m sigma (a sigma) (i sigma) side v)).card : ℝ) /
        (GroupOrbitProjection.rawOrbit
          (GroupOrbitProjection.groupCounts (activeCounts allocation m)
            (fun h : Active K tick => h.val.physicalOrder = sigma))
          (fun h => Left activeHalfLength h.val) (fun h => Right activeHalfLength h.val)
          (GroupOrbitProjection.projectTarget (activeCounts allocation m)
            (fun h => h.val.physicalOrder = sigma) target)
          (projectRaw allocation m sigma w)).card ≤ 1 / m := by
    change ((rejectedFilter
      (localOrbit allocation m sigma (projectTarget allocation m sigma target)
        (projectRaw allocation m sigma w))
      (fun v => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma v ∧
        ¬localAssigned allocation m sigma (a sigma) (i sigma) side v)).card : ℝ) /
      (localOrbit allocation m sigma (projectTarget allocation m sigma target)
        (projectRaw allocation m sigma w)).card ≤ 1 / m
    dsimp only [target]
    rw [project_joinGroupTargets]
    have hb0 := hbound sigma
    rw [filter_eq_rejected] at hb0
    exact hb0
  have hh := GroupOrbitProjection.raw_group_passing_rejection_fraction_le
    (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
    (fun h : Active K tick => h.val.physicalOrder) target w
    (AllFieldHistoryRecovery.completeKeep allocation m ε side)
    (fun sigma => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma)
    (fun sigma => localAssigned allocation m sigma (a sigma) (i sigma) side)
    (fun v hv sigma => completeKeep_project allocation m ε side v hv sigma)
    (fun _ => (1 : ℝ) / m) hb
  have hcard : Fintype.card Placement = 6 := by
    norm_num [Placement, Fintype.card_perm, Nat.factorial]
  have horbit :
      OrbitCounting.orbitSet
        (G := AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m) w =
      GroupOrbitProjection.rawOrbit (activeCounts allocation m)
        (Left activeHalfLength) (Right activeHalfLength) target w := by
    exact RecoveryOrbitDecisions.orbitSet_eq_transportedOrbit
      (G := AllFieldHistoryRecovery.Symmetries (K := K) (tick := tick) allocation m)
      _ _ _ (AllFieldHistoryRecovery.coordinates allocation m target) w
  rw [filter_eq_rejected, horbit]
  simp only [target, grouped_assigned_iff, Finset.sum_const, Finset.card_univ,
    hcard, nsmul_eq_mul, Nat.cast_ofNat, mul_one_div] at hh ⊢
  exact hh

theorem repair_grouped (F : Type*) [CommRing F] (allocation : Allocation)
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (i : ∀ sigma, E sigma) (e : ∀ sigma, GroupTarget (K := K) (tick := tick) allocation m sigma)
    (hx : ∀ sigma w, (a sigma).x w = some (i sigma) →
      groupIdealSide allocation m ε 0 sigma (e sigma) w)
    (hy : ∀ sigma w, (a sigma).y w = some (i sigma) →
      groupIdealSide allocation m ε 1 sigma (e sigma) w)
    (hz : ∀ sigma w, (a sigma).z w = some (i sigma) →
      groupIdealSide allocation m ε 2 sigma (e sigma) w)
    (hbound : ∀ side w,
      AllFieldHistoryRecovery.Used F allocation m ε
        (joinGroupTargets (activeCounts allocation m) e) side w → ∀ sigma,
      (((localOrbit allocation m sigma (e sigma) (projectRaw allocation m sigma w)).filter
        (fun v => AllFieldHistoryGroupMasks.completeKeep allocation m ε side sigma v ∧
          ¬localAssigned allocation m sigma (a sigma) (i sigma) side v)).card : ℝ) /
        (localOrbit allocation m sigma (e sigma) (projectRaw allocation m sigma w)).card ≤ 1 / m) :
    InverseLinearRecovery.RecoveredBy
      (AllFieldHistoryRecovery.ideal F allocation m ε (joinGroupTargets (activeCounts allocation m) e))
      (JointExtraction.branch
        (ExactRecovery.delete (AllFieldHistoryRecovery.rawSource F allocation m)
          (AllFieldHistoryRecovery.completeKeep allocation m ε 0)
          (AllFieldHistoryRecovery.completeKeep allocation m ε 1)
          (AllFieldHistoryRecovery.completeKeep allocation m ε 2))
        (groupedAssignment allocation m E a) i)
      (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m) := by
  have hs := groupedAssignment_sound allocation m ε E a i e hx hy hz
  apply AllFieldHistoryRecovery.repair_selected_branch F allocation hε hm
    (groupedAssignment allocation m E a) i (joinGroupTargets (activeCounts allocation m) e)
    hs.1 hs.2.1 hs.2.2
  intro side w hw
  exact grouped_collision_le allocation m ε E a i e side w (hbound side w hw)

end MatrixMultiplication.AllFieldHistoryGroupedRecovery






namespace MatrixMultiplication.AllFieldHistorySource

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ)

theorem groupedAssignment_coherent (F : Type*) [Field F] (ε : ℝ)
    (E : Placement → Type)
    (a : ∀ sigma, JointExtraction.Assignment
      (AllFieldHistoryGroupMasks.GroupRaw (K := K) (tick := tick) allocation m sigma)
      (AllFieldHistoryGroupMasks.GroupRaw (K := K) (tick := tick) allocation m sigma)
      (AllFieldHistoryGroupMasks.GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (ha : ∀ sigma, JointExtraction.Coherent
      (AllFieldHistoryGroupMasks.groupPreparedSource F allocation m ε sigma) (a sigma)) :
    JointExtraction.Coherent (preparedSource (K := K) (tick := tick) allocation m F ε)
      (AllFieldHistoryGroupedRecovery.groupedAssignment allocation m E a) := by
  intro x y z i j k hT hx hy hz
  have hprod : CommonDimensions.familyProduct
      (fun sigma => AllFieldHistoryGroupMasks.groupPreparedSource F allocation m ε sigma)
      (fun sigma => AllFieldHistoryGroupMasks.projectRaw allocation m sigma x)
      (fun sigma => AllFieldHistoryGroupMasks.projectRaw allocation m sigma y)
      (fun sigma => AllFieldHistoryGroupMasks.projectRaw allocation m sigma z) ≠ 0 := by
    rw [preparedSource_eq_delete] at hT
    exact fun hzero => hT ((AllFieldHistoryGroupMasks.preparedSource_factor
      F allocation m ε x y z).trans hzero)
  exact GroupAssignment.product_coherent _ a ha _ _ _ i j k hprod hx hy hz

end MatrixMultiplication.AllFieldHistorySource

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_InitialLeafRates
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open MatrixMultiplication.Foundation
open scoped BigOperators

noncomputable section

def statisticRate (d : ℚ) (k : Fin 5) : ℝ :=
  finiteEntropy (fun i : Fin 6 => (statisticLaw d k i : ℝ)) +
    ∑ i : Fin 6, (statisticLaw d k i : ℝ) * Real.log (multiplicity i : ℝ)

end

end MatrixMultiplication.AllFieldParameters

noncomputable section

namespace MatrixMultiplication.AllFieldTerminalRates

open AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def S1 : ℝ :=
  (zeroSecond.map (fun t => (secondMass t : ℝ) * AllFieldZeroLeafRates.fourRate t)).sum

def S2 : ℝ :=
  (positiveSecond.map (fun t =>
    ((below t).map (fun u => (littleMass t u : ℝ) * secondLeafRate t u)).sum)).sum

def S : ℝ := (S0 + S1) + S2

end MatrixMultiplication.AllFieldTerminalRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWStrandCompatibility
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.CWStrandCompatibility

open MatrixMultiplication.Foundation CWStrands CWCompatibilityTransfer InheritedMasks
open scoped BigOperators

variable {F : Type*} [CommRing F]

section Classes

variable {P A : Type*} [Fintype P] [DecidableEq P]
    [Fintype A] [DecidableEq A] {n : ℕ}
    (g : P → Fin 3 → ℕ) (x y z : P → (Fin n → Fin 7))
    (h : (∏ i, shapeTensor (F := F) (Fin n) (g i) (x i) (y i) (z i)) ≠ 0)
    (statistic : (Fin n → Fin 7) → A) (κ : A ≃ A)
    (hstatistic : ∀ w, statistic (wordComplement w) = κ (statistic w))
    (ν : A → ℝ) (η : ℝ)

include h

include hstatistic

theorem zeroZ_transfer (hg : ∀ i, g i 2 = 0)
    (hx : typeWindow ν η (fun i => statistic (x i))) :
    typeWindow (ν ∘ κ.symm) η (fun i => statistic (y i)) := by
  apply transfer_window statistic κ hstatistic x y _ ν η hx
  intro i
  have hi := class_coefficient_nonzero g x y z h i
  have hm := shapeTensor_support (g i) (x i) (y i) (z i) hi
  have hz : wordWeight (z i) = 0 := by
    change weight (z i) = 0
    exact hm.2.2.trans (hg i)
  exact zeroZ_word_match (x i) (y i) (z i)
    (shape_nonzero_power (g i) (x i) (y i) (z i) hi) hz

theorem zeroY_transfer (hg : ∀ i, g i 1 = 0)
    (hx : typeWindow ν η (fun i => statistic (x i))) :
    typeWindow (ν ∘ κ.symm) η (fun i => statistic (z i)) := by
  apply transfer_window statistic κ hstatistic x z _ ν η hx
  intro i
  have hi := class_coefficient_nonzero g x y z h i
  have hm := shapeTensor_support (g i) (x i) (y i) (z i) hi
  have hy : wordWeight (y i) = 0 := by
    change weight (y i) = 0
    exact hm.2.1.trans (hg i)
  exact zeroY_word_match (x i) (y i) (z i)
    (shape_nonzero_power (g i) (x i) (y i) (z i) hi) hy

theorem zeroX_transfer (hg : ∀ i, g i 0 = 0)
    (hy : typeWindow ν η (fun i => statistic (y i))) :
    typeWindow (ν ∘ κ.symm) η (fun i => statistic (z i)) := by
  apply transfer_window statistic κ hstatistic y z _ ν η hy
  intro i
  have hi := class_coefficient_nonzero g x y z h i
  have hm := shapeTensor_support (g i) (x i) (y i) (z i) hi
  have hx : wordWeight (x i) = 0 := by
    change weight (x i) = 0
    exact hm.1.trans (hg i)
  exact zeroX_word_match (x i) (y i) (z i)
    (shape_nonzero_power (g i) (x i) (y i) (z i) hi) hx

end Classes

end MatrixMultiplication.CWStrandCompatibility

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_GroupOrbitTransport
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
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

def actualKeep (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (v : Variable (K := K) (tick := tick) allocation m sigma) : Prop :=
  completeKeep allocation m ε (sigma v.1) sigma v.2

theorem competitor_coverage (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma)
    (he : Compatible allocation m ε sigma v.1 e v.2)
    (t : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (hne : t ≠ coarse allocation m sigma e)
    (hc : actualCompatible allocation m ε sigma t v) :
    t ∈ (data allocation m ε sigma).competitors e o v := by
  obtain ⟨f, hf, hcomp⟩ := hc
  apply Finset.mem_filter.mpr
  refine ⟨?_, hne, ?_, f, hf, hcomp⟩
  · simp only [Finset.mem_image]
    exact ⟨f, Finset.mem_univ _, hf⟩
  · rw [← hf]
    exact hcomp.1.trans he.1.symm

theorem mem_passing (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma) :
    v ∈ (data allocation m ε sigma).passing e o ↔
      v ∈ (data allocation m ε sigma).full e o ∧ actualKeep allocation m ε sigma v :=
  Finset.mem_filter

end MatrixMultiplication.AllFieldGroupOrbitData

end




end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_NativeCapacity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
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

def nativeT : ℝ := (interiorPairs.map interiorMass).sum

def nativeB : ℝ :=
  (interiorPairs.map fun tu => interiorMass tu *
    (2 * Real.log 2 + interiorEntropy tu)).sum / 3

def nativeHigh : ℝ := nativeT * Real.log 2

def nativeCstar : ℝ := Staggering.totalCapacity nativeLA nativeLB nativeB

def nativeLambda : Fin 3 → ℝ :=
  Staggering.balanceFraction nativeLA nativeLB nativeHigh nativeB

def nativeBeta : ℝ :=
  Staggering.boundaryDeficit nativeLA nativeLB (nativeLC nativeLambda) nativeCstar

end MatrixMultiplication.AllFieldNativeCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_NativeLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldPairMarginals.halfWeightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
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

def halfFiniteLaw (t : Shape) (ht : t ∈ shapes 8) (side : Fin 3) : FiniteLaw PairSlot where
  mass a := (halfLaw t side a : ℝ)
  nonneg a := by exact_mod_cast halfLaw_nonnegative t side a
  total := by exact_mod_cast halfLaw_normalized t ht side

def littleFiniteLaw (t u : Shape) (side : Fin 3) : FiniteLaw (Fin 6) where
  mass a := (littleLaw t u side a : ℝ)
  nonneg a := by exact_mod_cast littleLaw_nonnegative t u side a
  total := by exact_mod_cast littleLaw_normalized t u side

def stageAPairLaw (g : Shape) (hg : g ∈ positiveInitial) (side : Fin 3) :
    FiniteLaw (PairSlot × PairSlot) :=
  pairFiniteLaw (below g) g (fun u => (stageALaw g u : ℝ))
    (fun u a => (halfLaw u side a : ℝ))
    (fun u hu => Rat.cast_nonneg.mpr (stageALaw_positive g u hu).le)
    (by rw [← list_rat_cast_inline_MatrixMultiplication_AllFieldNativeLaws, stageALaw_normalized g hg]; norm_num)
    (fun u a => Rat.cast_nonneg.mpr (halfLaw_nonnegative u side a))
    (fun u hu => (halfFiniteLaw u (stageA_children_size g hg u hu) side).total)
    (fun u hu => (halfFiniteLaw (complement g u)
      (stageA_children_size g hg _ (stageA_support_complement g hg u hu).1) side).total)

def stageBPairLaw (t : Shape) (ht : t ∈ positiveSecond) (side : Fin 3) :
    FiniteLaw (Fin 6 × Fin 6) :=
  pairFiniteLaw (below t) t (fun u => (stageBLaw t u : ℝ))
    (fun u a => (littleLaw t u side a : ℝ))
    (fun u hu => Rat.cast_nonneg.mpr (stageBLaw_positive t u hu).le)
    (by rw [← list_rat_cast_inline_MatrixMultiplication_AllFieldNativeLaws, stageBLaw_normalized t ht]; norm_num)
    (fun u a => Rat.cast_nonneg.mpr (littleLaw_nonnegative t u side a))
    (fun u _ => (littleFiniteLaw t u side).total)
    (fun u _ => (littleFiniteLaw t (complement t u) side).total)

end MatrixMultiplication.AllFieldNativeCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupBranchLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section






namespace MatrixMultiplication.AllFieldGroupNativeLaws

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldActiveLaws
open AllFieldNativeCapacity AllFieldPairMarginals AllFieldPairConditionalEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem childLaw_complementary_sides {K : ℕ} (w : Work K)
    (u : Shape) (hu : u ∈ shapes (2 * w.halfLength))
    (source target : Fin 3) (hne : source ≠ target)
    (hsum : u source + u target = 2 * w.halfLength) (a : w.Statistic) :
    w.childLaw u source ((statisticComplement w).symm a) = w.childLaw u target a := by
  cases w with
  | stageA h => exact halfLaw_complementary_sides u hu source target hne hsum a
  | stageB h =>
      exact littleLaw_complement (aShape h.val) u source target
        (lt_of_le_of_lt (mem_shapes_bound hu source) (by norm_num [Work.halfLength]))
        (lt_of_le_of_lt (mem_shapes_bound hu target) (by norm_num [Work.halfLength]))
        hsum a
  | stageC h => rfl

theorem halfShape_mem_of_counts_pos {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) :
    halfShape h.val.1.parentShape (canonicalChildShape h.val u) right ∈
      shapes (2 * h.val.1.halfLength) := by
  obtain ⟨b, rfl, _⟩ := shapeCounts_positive _ _ u hu
  rw [canonicalChildShape_branchShape]
  exact h.val.1.halfShape_mem b right

theorem childWeight_sum {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) (sigma : Placement) :
    childWeight right h u (sigma 0) + childWeight right h u (sigma 1) +
      childWeight right h u (sigma 2) = 2 * h.val.1.halfLength := by
  let v := halfShape h.val.1.parentShape (canonicalChildShape h.val u) right
  have ht := mem_shapes_total (halfShape_mem_of_counts_pos allocation m right h u hu)
  have hp := Equiv.sum_comp (sigma.trans h.val.2.symm) v
  have he : (∑ i : Fin 3, v (h.val.2.symm (sigma i))) = 2 * h.val.1.halfLength := by
    calc
      _ = ∑ i : Fin 3, v i := hp
      _ = _ := by simpa [v, shapeTotal, Fin.sum_univ_succ, Nat.add_assoc] using ht
  simpa [v, halfShape_childWeight, Fin.sum_univ_succ, Nat.add_assoc] using he

theorem designated_source_geometry (weight : Fin 3 → ℕ) (total : ℕ)
    (htotal : weight 0 + weight 1 + weight 2 = total) (side : Fin 3)
    (hd : if side = 1 then weight 2 = 0
      else if side = 2 then weight 0 * weight 1 = 0 else False) :
    let source : Fin 3 := if side = 2 ∧ weight 1 ≠ 0 then 1 else 0
    source ≠ side ∧ weight source + weight side = total := by
  fin_cases side
  · simp at hd
  · simp at hd ⊢
    omega
  · by_cases hzero : weight 1 = 0
    · simp [hzero] at hd ⊢
      omega
    · have hz : weight 0 = 0 := by simpa [hzero] using hd
      simp [hzero]
      omega

theorem compatibilityLaw_eq {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (sigma : Placement) (right : Bool) (side : Fin 3)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape)
    (hu : 0 < Counts allocation m sigma h u)
    (hd : designated right side sigma h u) :
    compatibilityLaw right side sigma h u =
      if right then rightLaw h.val u (sigma side) else leftLaw h.val u (sigma side) := by
  let weight : Fin 3 → ℕ := fun i => childWeight right h.val u (sigma i)
  let source : Fin 3 := if side = 2 ∧ weight 1 ≠ 0 then 1 else 0
  have hdesignated : if side = 1 then weight 2 = 0
      else if side = 2 then weight 0 * weight 1 = 0 else False := by
    simpa only [AllFieldGroupOrbitData.designated, weight, childWeight] using hd.2
  have hgeom := designated_source_geometry weight (2 * h.val.val.1.halfLength)
    (childWeight_sum allocation m right h.val u hu sigma) side hdesignated
  have hsource : (if side = 2 ∧ weight 1 ≠ 0 then sigma 1 else sigma 0) = sigma source := by
    dsimp only [source]
    split_ifs <;> rfl
  have hne : h.val.val.2.symm (sigma source) ≠ h.val.val.2.symm (sigma side) := by
    intro heq
    exact hgeom.1 (sigma.injective (h.val.val.2.symm.injective heq))
  have hsum :
      (halfShape h.val.val.1.parentShape (canonicalChildShape h.val.val u) right)
          (h.val.val.2.symm (sigma source)) +
        (halfShape h.val.val.1.parentShape (canonicalChildShape h.val.val u) right)
          (h.val.val.2.symm (sigma side)) = 2 * h.val.val.1.halfLength := by
    simpa only [halfShape_childWeight] using hgeom.2
  funext a
  have hlaw := childLaw_complementary_sides h.val.val.1
    (halfShape h.val.val.1.parentShape (canonicalChildShape h.val.val u) right)
    (halfShape_mem_of_counts_pos allocation m right h.val u hu)
    (h.val.val.2.symm (sigma source)) (h.val.val.2.symm (sigma side)) hne hsum a
  have hre : halfLawAt right h.val u (sigma source)
      ((statisticComplement h.val.val.1).symm a) =
        halfLawAt right h.val u (sigma side) a := by
    rw [halfLawAt_eq, halfLawAt_eq]
    exact_mod_cast hlaw
  change ((if right then rightLaw h.val u
      (if side = 2 ∧ weight 1 ≠ 0 then sigma 1 else sigma 0)
    else leftLaw h.val u
      (if side = 2 ∧ weight 1 ≠ 0 then sigma 1 else sigma 0))
      ((statisticComplement h.val.val.1).symm a)) = _
  rw [hsource]
  exact hre

def nativePairLaw {K : ℕ} (w : Work K) (side : Fin 3) :
    FiniteLaw (w.Statistic × w.Statistic) :=
  match w with
  | .stageA h => stageAPairLaw (initialShape h.val) h.property side
  | .stageB h => stageBPairLaw (aShape h.val) h.property side
  | .stageC parent =>
      { mass := fun _ => 1
        nonneg := fun _ => zero_le_one
        total := by
          let : Unique (Work.stageC parent).Statistic := inferInstanceAs (Unique PUnit)
          simp }

end MatrixMultiplication.AllFieldGroupNativeLaws






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
def Z0_0_8Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 5, 5 => ⟨1, 0⟩
  | _, _ => (.exact 0)

def Z0_0_8Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 0 0 8) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 0 0 8) then Z0_0_8Probs ij
  else Z0_0_8Probs (kappa ij.1, kappa ij.2)
def Z0_1_7Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 4, 5 => ⟨(1 / 2), 0⟩
  | 5, 4 => ⟨(1 / 2), 0⟩
  | _, _ => (.exact 0)

def Z0_1_7Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 0 1 7) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 0 1 7) then Z0_1_7Probs ij
  else Z0_1_7Probs (kappa ij.1, kappa ij.2)

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
def Z0_3_5Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 1, 5 => ⟨(1324789218043180893556977378811 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 2, 4 => ⟨(43077488265096366404092710992583 / 100000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(854586659763454361758666849959 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 2 => ⟨(43077488265096366404092710992583 / 100000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(854586659763454361758666849959 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 5, 1 => ⟨(1324789218043180893556977378811 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z0_3_5Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 0 3 5) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 0 3 5) then Z0_3_5Probs ij
  else Z0_3_5Probs (kappa ij.1, kappa ij.2)

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
def Z0_4_4Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 5 => ⟨(7494452423922705001235812089 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 4 => ⟨(1261243984157612676036813528611 / 10000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 2, 2 => ⟨(61165519013116834840287783186423 / 100000000000000000000000000000000), (7 / 6250000000000000000000000000000)⟩
  | 2, 3 => ⟨(784932206749518952016351104847 / 12500000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 3, 2 => ⟨(784932206749518952016351104847 / 12500000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 3, 3 => ⟨(675963374542473156652537959353 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 1 => ⟨(1261243984157612676036813528611 / 10000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 5, 0 => ⟨(7494452423922705001235812089 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z0_4_4Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 0 4 4) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 0 4 4) then Z0_4_4Probs ij
  else Z0_4_4Probs (kappa ij.1, kappa ij.2)

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
def Z0_6_2Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 2, 5 => ⟨(15790050502703409550191718781019 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 3, 5 => ⟨(1133125820533948503508356844879 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 4, 4 => ⟨(16538411838381320973149962187051 / 25000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 5, 2 => ⟨(15790050502703409550191718781019 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 5, 3 => ⟨(1133125820533948503508356844879 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z0_6_2Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 0 6 2) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 0 6 2) then Z0_6_2Probs ij
  else Z0_6_2Probs (kappa ij.1, kappa ij.2)

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
def Z0_2_6Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 2, 5 => ⟨(9657537875187848339599195720457 / 50000000000000000000000000000000), (39 / 100000000000000000000000000000000)⟩
  | 3, 5 => ⟨(312906143484347380943417643667 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 4, 4 => ⟨(58240787064405132832169040681501 / 100000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
  | 5, 2 => ⟨(9657537875187848339599195720457 / 50000000000000000000000000000000), (39 / 100000000000000000000000000000000)⟩
  | 5, 3 => ⟨(312906143484347380943417643667 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z0_2_6Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 0 2 6) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 0 2 6) then Z0_2_6Probs ij
  else Z0_2_6Probs (kappa ij.1, kappa ij.2)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB1_3_4
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
def B1_1_6Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 1 => ⟨(1 / 2), (3 / 50000000000000000000000000000000)⟩
  | 0, 1, 0 => ⟨(1 / 2), (3 / 50000000000000000000000000000000)⟩
  | 1, 0, 1 => ⟨(1 / 2), (3 / 50000000000000000000000000000000)⟩
  | 1, 1, 0 => ⟨(1 / 2), (3 / 50000000000000000000000000000000)⟩
  | 2, 5, 2 => ⟨(23395434846455848905473447711 / 2500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 5, 3 => ⟨(58960210306318037278141611 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 4 => ⟨(49064123645931459725743783949949 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 2, 5 => ⟨(23395434846455848905473447711 / 2500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 3, 5 => ⟨(58960210306318037278141611 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_2_5Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 1 => ⟨(1 / 2), (1 / 2000000000000000000000000000000)⟩
  | 0, 1, 0 => ⟨(1 / 2), (1 / 2000000000000000000000000000000)⟩
  | 1, 0, 2 => ⟨(3297719669499762242862115497643 / 20000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(355998814646362178458756161701 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 1, 1 => ⟨(396642594740867223667445521291 / 625000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 1, 2, 0 => ⟨(3297719669499762242862115497643 / 20000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(355998814646362178458756161701 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(36249118515191988245121850051 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(9630112437092073853782692487793 / 20000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 2, 4, 3 => ⟨(1776939577509246754596293860933 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(9630112437092073853782692487793 / 20000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 2, 3, 4 => ⟨(1776939577509246754596293860933 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(36249118515191988245121850051 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B1_3_4Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 1 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | 0, 1, 0 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | 1, 0, 4 => ⟨(132732360120937838226056869067 / 10000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(22225619795436123996567854910187 / 50000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 1, 3 => ⟨(1055359201979593406150930372239 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(22225619795436123996567854910187 / 50000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 3, 1 => ⟨(1055359201979593406150930372239 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 4, 0 => ⟨(132732360120937838226056869067 / 10000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 5, 0 => ⟨(18376602916823826473515371739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 1 => ⟨(1456119070923005006600137580027 / 20000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 2, 2 => ⟨(77369303606423225289931508632371 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 2, 2, 3 => ⟨(4011596667753851198216770545993 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 3, 2 => ⟨(4011596667753851198216770545993 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(4779571502687297343271865947 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 4 => ⟨(1456119070923005006600137580027 / 20000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 0, 5 => ⟨(18376602916823826473515371739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB1_4_3
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
def B1_4_3Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 1 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | 0, 1, 0 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | 1, 1, 4 => ⟨(1966519024111033745643559687113 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 1, 2, 2 => ⟨(18979543218321732038291109031929 / 25000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 1, 2, 3 => ⟨(4129064322164561216004098570321 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 3, 2 => ⟨(4129064322164561216004098570321 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 3, 3 => ⟨(3076084781593046714415474453 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 4, 1 => ⟨(1966519024111033745643559687113 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 1, 5, 0 => ⟨(33468805621467537981782719557 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 5 => ⟨(33468805621467537981782719557 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 0 => ⟨(1305555413502823769500199931759 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 2, 1 => ⟨(44394219774093180020469714786281 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 2, 3, 1 => ⟨(107505620310099905250752132049 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 1, 2 => ⟨(44394219774093180020469714786281 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 2, 1, 3 => ⟨(107505620310099905250752132049 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 0, 4 => ⟨(1305555413502823769500199931759 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB1_5_2
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
def B1_5_2Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 1 => ⟨(1 / 2), (51 / 100000000000000000000000000000000)⟩
  | 0, 1, 0 => ⟨(1 / 2), (51 / 100000000000000000000000000000000)⟩
  | 1, 2, 4 => ⟨(944296764805115665482085327337 / 2000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(518340583815889402541057141607 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 4, 2 => ⟨(944296764805115665482085327337 / 2000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(518340583815889402541057141607 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 5, 1 => ⟨(355899712240329557865752533361 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 1, 5 => ⟨(355899712240329557865752533361 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(2064129144151554264168571077709 / 12500000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 2, 3, 0 => ⟨(1985286600756920686097122080759 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(31501680246030645200554309297569 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(2064129144151554264168571077709 / 12500000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 2, 0, 3 => ⟨(1985286600756920686097122080759 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB2_3_3
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
def B2_3_3Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 2 => ⟨(8811526653339407816212002016803 / 50000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 0, 0, 3 => ⟨(173415754401812546184280998437 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 1, 1 => ⟨(31509867921312121636654590974209 / 50000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 0, 2, 0 => ⟨(8811526653339407816212002016803 / 50000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 0, 3, 0 => ⟨(173415754401812546184280998437 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(45457112926707713088575555921683 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 1, 1, 3 => ⟨(3220843048653859968603717052973 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(45457112926707713088575555921683 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 1, 3, 1 => ⟨(3220843048653859968603717052973 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 4, 0 => ⟨(20656937884975420981573859771 / 1562500000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 0, 4 => ⟨(20656937884975420981573859771 / 1562500000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 4, 0 => ⟨(163911127094417036878035098501 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 2, 1 => ⟨(46643247536423404746233613795319 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 2, 3, 1 => ⟨(2045463446821258958742105416673 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 1, 2 => ⟨(46643247536423404746233613795319 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 2, 1, 3 => ⟨(2045463446821258958742105416673 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 0, 4 => ⟨(163911127094417036878035098501 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB2_5_1
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
def B2_5_1Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 2 => ⟨(16500511368438802565759232435939 / 100000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 0, 0, 3 => ⟨(993526583999480062128659640117 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 1, 1 => ⟨(31512435463562237309983448283827 / 50000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 0, 2, 0 => ⟨(16500511368438802565759232435939 / 100000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 0, 3, 0 => ⟨(993526583999480062128659640117 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 4, 2 => ⟨(9444123177522509382296864374047 / 20000000000000000000000000000000), (39 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(2070184148321972828859570473807 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 5, 1 => ⟨(354599982032740129828053827979 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 2, 4 => ⟨(9444123177522509382296864374047 / 20000000000000000000000000000000), (39 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(2070184148321972828859570473807 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 1, 5 => ⟨(354599982032740129828053827979 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 1, 0 => ⟨(1 / 2), (9 / 20000000000000000000000000000000)⟩
  | 2, 0, 1 => ⟨(1 / 2), (9 / 20000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
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
def Z0_5_3Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 1, 5 => ⟨(2157810797800214543118318532199 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 4 => ⟨(4382455112007387232015528108533 / 10000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(4017638082125913136726400382471 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 4, 2 => ⟨(4382455112007387232015528108533 / 10000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(4017638082125913136726400382471 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 5, 1 => ⟨(2157810797800214543118318532199 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z0_5_3Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 0 5 3) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 0 5 3) then Z0_5_3Probs ij
  else Z0_5_3Probs (kappa ij.1, kappa ij.2)

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
def Z0_7_1Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 4, 5 => ⟨(1 / 2), 0⟩
  | 5, 4 => ⟨(1 / 2), 0⟩
  | _, _ => (.exact 0)

def Z0_7_1Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 0 7 1) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 0 7 1) then Z0_7_1Probs ij
  else Z0_7_1Probs (kappa ij.1, kappa ij.2)

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
def Z0_8_0Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 5, 5 => ⟨1, 0⟩
  | _, _ => (.exact 0)

def Z0_8_0Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 0 8 0) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 0 8 0) then Z0_8_0Probs ij
  else Z0_8_0Probs (kappa ij.1, kappa ij.2)

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
def Z1_0_7Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 4, 5 => ⟨(1 / 2), 0⟩
  | 5, 4 => ⟨(1 / 2), 0⟩
  | _, _ => (.exact 0)

def Z1_0_7Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 1 0 7) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 1 0 7) then Z1_0_7Probs ij
  else Z1_0_7Probs (kappa ij.1, kappa ij.2)

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
def Z1_7_0Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 4, 5 => ⟨(1 / 2), 0⟩
  | 5, 4 => ⟨(1 / 2), 0⟩
  | _, _ => (.exact 0)

def Z1_7_0Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 1 7 0) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 1 7 0) then Z1_7_0Probs ij
  else Z1_7_0Probs (kappa ij.1, kappa ij.2)

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
def Z2_0_6Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 2, 5 => ⟨(10457964405071752630514678883453 / 50000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
  | 3, 5 => ⟨(1708150169428319858018410671529 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 4, 4 => ⟨(5475184204085634976190446312313 / 10000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 5, 2 => ⟨(10457964405071752630514678883453 / 50000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
  | 5, 3 => ⟨(1708150169428319858018410671529 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z2_0_6Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 2 0 6) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 2 0 6) then Z2_0_6Probs ij
  else Z2_0_6Probs (kappa ij.1, kappa ij.2)

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
def Z2_6_0Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 2, 5 => ⟨(8700304788653067056094286446733 / 50000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩
  | 3, 5 => ⟨(1594093504259596830505224830177 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 4, 4 => ⟨(12402118767373707622922480910543 / 20000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 5, 2 => ⟨(8700304788653067056094286446733 / 50000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩
  | 5, 3 => ⟨(1594093504259596830505224830177 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z2_6_0Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 2 6 0) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 2 6 0) then Z2_6_0Probs ij
  else Z2_6_0Probs (kappa ij.1, kappa ij.2)

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
def Z3_0_5Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 1, 5 => ⟨(3851794993380545981064826935537 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 4 => ⟨(41361035729160865645318261676507 / 100000000000000000000000000000000), (17 / 20000000000000000000000000000000)⟩
  | 3, 4 => ⟨(1196792319364647093404227846989 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 2 => ⟨(41361035729160865645318261676507 / 100000000000000000000000000000000), (17 / 20000000000000000000000000000000)⟩
  | 4, 3 => ⟨(1196792319364647093404227846989 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 5, 1 => ⟨(3851794993380545981064826935537 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z3_0_5Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 3 0 5) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 3 0 5) then Z3_0_5Probs ij
  else Z3_0_5Probs (kappa ij.1, kappa ij.2)

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
def Z3_5_0Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 1, 5 => ⟨(645274206658629135363561930529 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 4 => ⟨(21453059186785379874419022991011 / 50000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(2256392399897361854853853147931 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 2 => ⟨(21453059186785379874419022991011 / 50000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(2256392399897361854853853147931 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 5, 1 => ⟨(645274206658629135363561930529 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z3_5_0Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 3 5 0) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 3 5 0) then Z3_5_0Probs ij
  else Z3_5_0Probs (kappa ij.1, kappa ij.2)

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
def Z4_0_4Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 5 => ⟨(55190951304569688595534186513 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 4 => ⟨(6632849277085335226067309879167 / 50000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 2, 2 => ⟨(5855588794422561384849059336303 / 10000000000000000000000000000000), (121 / 100000000000000000000000000000000)⟩
  | 2, 3 => ⟨(3407007932926322989871260497747 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 3, 2 => ⟨(3407007932926322989871260497747 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 3, 3 => ⟨(146554740536411280359956652837 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 1 => ⟨(6632849277085335226067309879167 / 50000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 5, 0 => ⟨(55190951304569688595534186513 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z4_0_4Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 4 0 4) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 4 0 4) then Z4_0_4Probs ij
  else Z4_0_4Probs (kappa ij.1, kappa ij.2)

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
def Z4_4_0Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 5 => ⟨(13333388289568308767749416709 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 4 => ⟨(12864926472604064794547580018297 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 2, 2 => ⟨(59823869115870383240874620994737 / 100000000000000000000000000000000), (123 / 100000000000000000000000000000000)⟩
  | 2, 3 => ⟨(1661981174399030590448466000577 / 25000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 3, 2 => ⟨(1661981174399030590448466000577 / 25000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 3, 3 => ⟨(180940029615764141468627407341 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 4, 1 => ⟨(12864926472604064794547580018297 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 5, 0 => ⟨(13333388289568308767749416709 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z4_4_0Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 4 4 0) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 4 4 0) then Z4_4_0Probs ij
  else Z4_4_0Probs (kappa ij.1, kappa ij.2)

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
def Z5_0_3Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 1, 5 => ⟨(2208598281054095678468725843991 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 4 => ⟨(42968103111757469343913723803283 / 100000000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩
  | 3, 4 => ⟨(2411649303594217488808775176363 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 2 => ⟨(42968103111757469343913723803283 / 100000000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩
  | 4, 3 => ⟨(2411649303594217488808775176363 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 5, 1 => ⟨(2208598281054095678468725843991 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z5_0_3Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 5 0 3) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 5 0 3) then Z5_0_3Probs ij
  else Z5_0_3Probs (kappa ij.1, kappa ij.2)

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
def Z5_3_0Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 1, 5 => ⟨(2212727093860282562448201536591 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 4 => ⟨(43733995727072191717374739083017 / 100000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(506659647383440715022132422549 / 12500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 4, 2 => ⟨(43733995727072191717374739083017 / 100000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(506659647383440715022132422549 / 12500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 5, 1 => ⟨(2212727093860282562448201536591 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z5_3_0Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 5 3 0) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 5 3 0) then Z5_3_0Probs ij
  else Z5_3_0Probs (kappa ij.1, kappa ij.2)

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
def Z6_0_2Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 2, 5 => ⟨(19726120793130810407094355236181 / 100000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 3, 5 => ⟨(20245725524523564193484784547927 / 100000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 4, 4 => ⟨(20056307364691250798841720431783 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 5, 2 => ⟨(19726120793130810407094355236181 / 100000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 5, 3 => ⟨(20245725524523564193484784547927 / 100000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z6_0_2Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 6 0 2) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 6 0 2) then Z6_0_2Probs ij
  else Z6_0_2Probs (kappa ij.1, kappa ij.2)

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
def Z6_2_0Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 2, 5 => ⟨(19924044508891583790197036118597 / 100000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 3, 5 => ⟨(4012399160127629130320676344027 / 20000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 4, 4 => ⟨(10013959690470270558199582161267 / 50000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 5, 2 => ⟨(19924044508891583790197036118597 / 100000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 5, 3 => ⟨(4012399160127629130320676344027 / 20000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)

def Z6_2_0Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 6 2 0) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 6 2 0) then Z6_2_0Probs ij
  else Z6_2_0Probs (kappa ij.1, kappa ij.2)

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
def Z7_0_1Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 4, 5 => ⟨(1 / 2), 0⟩
  | 5, 4 => ⟨(1 / 2), 0⟩
  | _, _ => (.exact 0)

def Z7_0_1Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 7 0 1) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 7 0 1) then Z7_0_1Probs ij
  else Z7_0_1Probs (kappa ij.1, kappa ij.2)

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
def Z7_1_0Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 4, 5 => ⟨(1 / 2), 0⟩
  | 5, 4 => ⟨(1 / 2), 0⟩
  | _, _ => (.exact 0)

def Z7_1_0Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 7 1 0) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 7 1 0) then Z7_1_0Probs ij
  else Z7_1_0Probs (kappa ij.1, kappa ij.2)

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
def Z8_0_0Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 5, 5 => ⟨1, 0⟩
  | _, _ => (.exact 0)

def Z8_0_0Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 8 0 0) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 8 0 0) then Z8_0_0Probs ij
  else Z8_0_0Probs (kappa ij.1, kappa ij.2)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_6_1
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
def B1_6_1Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 1 => ⟨(1 / 2), (17 / 50000000000000000000000000000000)⟩
  | 0, 1, 0 => ⟨(1 / 2), (17 / 50000000000000000000000000000000)⟩
  | 1, 4, 4 => ⟨(476830025998288559780831570863 / 625000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(11355853489872446010634026210329 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 5, 3 => ⟨(497744430264469206899448120631 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(11355853489872446010634026210329 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 3, 5 => ⟨(497744430264469206899448120631 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 1, 0 => ⟨(1 / 2), (17 / 50000000000000000000000000000000)⟩
  | 2, 0, 1 => ⟨(1 / 2), (17 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal2_1_5
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
def B2_1_5Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 2 => ⟨(8240786865581452095028265002887 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 0, 0, 3 => ⟨(919021127692499707011485447387 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 1, 1 => ⟨(7920096003363024098980124774863 / 12500000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 0, 2, 0 => ⟨(8240786865581452095028265002887 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 0, 3, 0 => ⟨(919021127692499707011485447387 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 0, 1 => ⟨(1 / 2), (49 / 100000000000000000000000000000000)⟩
  | 1, 1, 0 => ⟨(1 / 2), (49 / 100000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(45454225515120282149964459091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(48074850858946887693214975069309 / 100000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 2, 4, 3 => ⟨(1834240690022871742485096012509 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(48074850858946887693214975069309 / 100000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 2, 3, 4 => ⟨(1834240690022871742485096012509 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(45454225515120282149964459091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal2_2_4
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
def B2_2_4Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 2 => ⟨(8377545014499415800266058795763 / 50000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 0, 0, 3 => ⟨(335543914232754127540362560533 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 0, 1, 1 => ⟨(3156719039983739776176606960581 / 5000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
  | 0, 2, 0 => ⟨(8377545014499415800266058795763 / 50000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 0, 3, 0 => ⟨(335543914232754127540362560533 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 0, 2 => ⟨(16755339902810166110201422814999 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(209683712169054516004063447399 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 1, 1 => ⟨(3156719039983739776176606960581 / 5000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
  | 1, 2, 0 => ⟨(16755339902810166110201422814999 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(209683712169054516004063447399 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 2, 5, 0 => ⟨(22170729407421252075742212347 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 1 => ⟨(1877555123344146106224953559491 / 25000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 2, 2, 2 => ⟨(1563542695666112973568998103859 / 2000000000000000000000000000000), (149 / 100000000000000000000000000000000)⟩
  | 2, 2, 3 => ⟨(3219564442457119163781284689913 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 2, 3, 2 => ⟨(3219564442457119163781284689913 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(79738471553025410009103131651 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 1, 4 => ⟨(1877555123344146106224953559491 / 25000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 2, 0, 5 => ⟨(22170729407421252075742212347 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal2_4_2
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
def B2_4_2Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 2 => ⟨(16757946325341947750940189356037 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 0, 0, 3 => ⟨(843481929912591696232100262703 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 0, 1, 1 => ⟨(31555089814832868856595610118557 / 50000000000000000000000000000000), (19 / 20000000000000000000000000000000)⟩
  | 0, 2, 0 => ⟨(16757946325341947750940189356037 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 0, 3, 0 => ⟨(843481929912591696232100262703 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 2, 2 => ⟨(38593837517531901492832074284017 / 50000000000000000000000000000000), (73 / 50000000000000000000000000000000)⟩
  | 1, 2, 3 => ⟨(84117846883879413836036378887 / 2500000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 3, 2 => ⟨(84117846883879413836036378887 / 2500000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 3, 3 => ⟨(8154626406161167721949080479 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 4, 1 => ⟨(3922744904992762908135236404901 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 1, 5, 0 => ⟨(32866269004172783017016141121 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 4 => ⟨(3922744904992762908135236404901 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 1, 0, 5 => ⟨(32866269004172783017016141121 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(16761382587425625619496074982197 / 100000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 2, 3, 0 => ⟨(842940622306945887952632457291 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(31552736167960482604598660103221 / 50000000000000000000000000000000), (93 / 100000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(16761382587425625619496074982197 / 100000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 2, 0, 3 => ⟨(842940622306945887952632457291 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_1_4
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
def B3_1_4Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 4 => ⟨(331794662118768313410096879501 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 0, 1, 2 => ⟨(8878737487603738207391907834341 / 20000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(4279133913506235709400073310291 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 2, 1 => ⟨(8878737487603738207391907834341 / 20000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(4279133913506235709400073310291 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(331794662118768313410096879501 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 0, 1 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | 1, 1, 0 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | 2, 5, 0 => ⟨(6274072805784506214853963141 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 1 => ⟨(3820996886917273539060027346381 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 2, 2 => ⟨(76473060096193834122862009176151 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 2, 2, 3 => ⟨(408752583274976468404048388933 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 3, 2 => ⟨(408752583274976468404048388933 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(17708108191266303098081954537 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 4 => ⟨(3820996886917273539060027346381 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 0, 5 => ⟨(6274072805784506214853963141 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_3_2
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
def B3_3_2Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 4 => ⟨(330535454043745680088327227499 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 0, 1, 2 => ⟨(11364381072153531634707882333201 / 25000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(3220333895210890740815161757201 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 2, 1 => ⟨(11364381072153531634707882333201 / 25000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(3220333895210890740815161757201 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(330535454043745680088327227499 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(2914142085981020950846212413557 / 6250000000000000000000000000000), (1 / 2000000000000000000000000000000)⟩
  | 1, 3, 1 => ⟨(1026894192444005991017039212513 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 4, 0 => ⟨(1319938239415652804426522958063 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(2914142085981020950846212413557 / 6250000000000000000000000000000), (1 / 2000000000000000000000000000000)⟩
  | 1, 1, 3 => ⟨(1026894192444005991017039212513 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 0, 4 => ⟨(1319938239415652804426522958063 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(352404218026259944720747217461 / 2000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 2, 3, 0 => ⟨(869669780516483806804489600199 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(984691228692828717411192172711 / 1562500000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(352404218026259944720747217461 / 2000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 2, 0, 3 => ⟨(869669780516483806804489600199 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_4_1
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
def B3_4_1Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 4 => ⟨(82952079780722940626225466023 / 6250000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 0, 1, 2 => ⟨(44353533976166490223624096589007 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(34553861978735541810850367637 / 800000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 2, 1 => ⟨(44353533976166490223624096589007 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(34553861978735541810850367637 / 800000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(82952079780722940626225466023 / 6250000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 4, 1 => ⟨(3928825098347934527147869357681 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 1, 5, 0 => ⟨(520812135624222942175390833 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 2 => ⟨(9488535396717968040641412979023 / 12500000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 1, 2, 3 => ⟨(517867354813334309888438519539 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 3, 2 => ⟨(517867354813334309888438519539 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 3, 3 => ⟨(4774960498253614292750479569 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 4 => ⟨(3928825098347934527147869357681 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 1, 0, 5 => ⟨(520812135624222942175390833 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 0 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | 2, 0, 1 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal4_1_3
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
def B4_1_3Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 5 => ⟨(33446547050938077933247687037 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 4 => ⟨(7864636411117022342973839771027 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(75912799250947798122822246208417 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 0, 2, 3 => ⟨(4133302117167199798769837390289 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 2 => ⟨(4133302117167199798769837390289 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 3 => ⟨(24430598381881437823904094877 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 4, 1 => ⟨(7864636411117022342973839771027 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 5, 0 => ⟨(33446547050938077933247687037 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 0 => ⟨(1 / 2), (13 / 50000000000000000000000000000000)⟩
  | 1, 0, 1 => ⟨(1 / 2), (13 / 50000000000000000000000000000000)⟩
  | 2, 4, 0 => ⟨(662466132560089079394730321331 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 2, 1 => ⟨(44369774122421474207741998278713 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 2, 3, 1 => ⟨(34442348899666781067748328629 / 800000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 1, 2 => ⟨(44369774122421474207741998278713 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 2, 1, 3 => ⟨(34442348899666781067748328629 / 800000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 0, 4 => ⟨(662466132560089079394730321331 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal4_2_2
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
def B4_2_2Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 5 => ⟨(32925283989199048774667657891 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 4 => ⟨(3924290670247618121826431431639 / 50000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(77179955630623675545342364672979 / 100000000000000000000000000000000), (147 / 100000000000000000000000000000000)⟩
  | 0, 2, 3 => ⟨(3365567162619738339457547396989 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 3, 2 => ⟨(3365567162619738339457547396989 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 3, 3 => ⟨(20368549697998574430467468169 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 4, 1 => ⟨(3924290670247618121826431431639 / 50000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 0, 5, 0 => ⟨(32925283989199048774667657891 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 0 => ⟨(8378300301784769988516089892097 / 50000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(1687321586797401660591628215999 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 1, 1 => ⟨(63112155619266116724752383999613 / 100000000000000000000000000000000), (93 / 100000000000000000000000000000000)⟩
  | 1, 0, 2 => ⟨(8378300301784769988516089892097 / 50000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(1687321586797401660591628215999 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(8381053538293561989694981145863 / 50000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 2, 3, 0 => ⟨(1683384830026987155576128449497 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(63109016186771777730067818517553 / 100000000000000000000000000000000), (93 / 100000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(8381053538293561989694981145863 / 50000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 2, 0, 3 => ⟨(1683384830026987155576128449497 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal4_3_1
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
def B4_3_1Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 5 => ⟨(33445776876645910225502339149 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 4 => ⟨(7861396357689534306132328191817 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(1517934657342094088384406991891 / 2000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 0, 2, 3 => ⟨(4144793288664198085105361786561 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 2 => ⟨(4144793288664198085105361786561 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 3 => ⟨(23996286434538977853265770399 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 4, 1 => ⟨(7861396357689534306132328191817 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 0, 5, 0 => ⟨(33445776876645910225502339149 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 4, 0 => ⟨(663549549127581616184973285819 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(22175975409536958176216013675929 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 1, 3, 1 => ⟨(864190016534184083039605215301 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(22175975409536958176216013675929 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 1, 1, 3 => ⟨(864190016534184083039605215301 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 0, 4 => ⟨(663549549127581616184973285819 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 1, 0 => ⟨(50000000000000000000000000000001 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 2, 0, 1 => ⟨(50000000000000000000000000000001 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal5_2_1
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
def B5_2_1Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 1, 5 => ⟨(357314469969927548416673592027 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 2, 4 => ⟨(2950462341058093169205656218569 / 6250000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 0, 3, 4 => ⟨(1038986801565327097938076659421 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 4, 2 => ⟨(2950462341058093169205656218569 / 6250000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 0, 4, 3 => ⟨(1038986801565327097938076659421 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 5, 1 => ⟨(357314469969927548416673592027 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 2, 0 => ⟨(8251288847660790062385380988161 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(496830304206321792542832136267 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 1, 1 => ⟨(3151010108785313270505790947861 / 5000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
  | 1, 0, 2 => ⟨(8251288847660790062385380988161 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(496830304206321792542832136267 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 1, 0 => ⟨(1 / 2), (53 / 100000000000000000000000000000000)⟩
  | 2, 0, 1 => ⟨(1 / 2), (53 / 100000000000000000000000000000000)⟩
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
def B6_1_1Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 2, 5 => ⟨(2335026597000525930807493756423 / 10000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(149723592147492123923952773557 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(125762490542599097263427673501 / 250000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
  | 0, 5, 2 => ⟨(2335026597000525930807493756423 / 10000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(149723592147492123923952773557 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 1, 0 => ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩
  | 1, 0, 1 => ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩
  | 2, 1, 0 => ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩
  | 2, 0, 1 => ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SupportedContraction
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
def B3_2_3Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 4 => ⟨(660954401694675365284077503627 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 1, 2 => ⟨(22728942148145327387716240679751 / 50000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(805051725079998623499840908311 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 0, 2, 1 => ⟨(22728942148145327387716240679751 / 50000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(805051725079998623499840908311 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(660954401694675365284077503627 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 1, 1 => ⟨(7877790787272644406002286888011 / 12500000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 1, 2, 0 => ⟨(8810343598851601529271500513163 / 50000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(86814965320621931744785142163 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 0, 2 => ⟨(8810343598851601529271500513163 / 50000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(86814965320621931744785142163 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 4, 0 => ⟨(657827693429655515259251577397 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 2, 1 => ⟨(2331743502850952336234925741329 / 5000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 2, 3, 1 => ⟨(1024737278060821122391491009313 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 1, 2 => ⟨(2331743502850952336234925741329 / 5000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 2, 1, 3 => ⟨(1024737278060821122391491009313 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 0, 4 => ⟨(657827693429655515259251577397 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

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
def B5_1_2Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 1, 5 => ⟨(715243539925161855344559597823 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 2, 4 => ⟨(47206419312694013248239704463141 / 100000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 0, 3, 4 => ⟨(519584286845206224103933984759 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 4, 2 => ⟨(47206419312694013248239704463141 / 100000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 0, 4, 3 => ⟨(519584286845206224103933984759 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 5, 1 => ⟨(715243539925161855344559597823 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 1, 0 => ⟨(1 / 2), (53 / 100000000000000000000000000000000)⟩
  | 1, 0, 1 => ⟨(1 / 2), (53 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(16505214817994806105572714739171 / 100000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 2, 3, 0 => ⟨(49570105911377387117154514831 / 2500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(31511980945550098409741104667589 / 50000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(16505214817994806105572714739171 / 100000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 2, 0, 3 => ⟨(49570105911377387117154514831 / 2500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)

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
def halfTable (s : Shape) (w : Fin 3) (ij : PairSlot) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8Half w ij
  | 0, 1, 7 => Z0_1_7Half w ij
  | 0, 2, 6 => Z0_2_6Half w ij
  | 0, 3, 5 => Z0_3_5Half w ij
  | 0, 4, 4 => Z0_4_4Half w ij
  | 0, 5, 3 => Z0_5_3Half w ij
  | 0, 6, 2 => Z0_6_2Half w ij
  | 0, 7, 1 => Z0_7_1Half w ij
  | 0, 8, 0 => Z0_8_0Half w ij
  | 1, 0, 7 => Z1_0_7Half w ij
  | 1, 1, 6 => B1_1_6Half w ij
  | 1, 2, 5 => B1_2_5Half w ij
  | 1, 3, 4 => B1_3_4Half w ij
  | 1, 4, 3 => B1_4_3Half w ij
  | 1, 5, 2 => B1_5_2Half w ij
  | 1, 6, 1 => B1_6_1Half w ij
  | 1, 7, 0 => Z1_7_0Half w ij
  | 2, 0, 6 => Z2_0_6Half w ij
  | 2, 1, 5 => B2_1_5Half w ij
  | 2, 2, 4 => B2_2_4Half w ij
  | 2, 3, 3 => B2_3_3Half w ij
  | 2, 4, 2 => B2_4_2Half w ij
  | 2, 5, 1 => B2_5_1Half w ij
  | 2, 6, 0 => Z2_6_0Half w ij
  | 3, 0, 5 => Z3_0_5Half w ij
  | 3, 1, 4 => B3_1_4Half w ij
  | 3, 2, 3 => B3_2_3Half w ij
  | 3, 3, 2 => B3_3_2Half w ij
  | 3, 4, 1 => B3_4_1Half w ij
  | 3, 5, 0 => Z3_5_0Half w ij
  | 4, 0, 4 => Z4_0_4Half w ij
  | 4, 1, 3 => B4_1_3Half w ij
  | 4, 2, 2 => B4_2_2Half w ij
  | 4, 3, 1 => B4_3_1Half w ij
  | 4, 4, 0 => Z4_4_0Half w ij
  | 5, 0, 3 => Z5_0_3Half w ij
  | 5, 1, 2 => B5_1_2Half w ij
  | 5, 2, 1 => B5_2_1Half w ij
  | 5, 3, 0 => Z5_3_0Half w ij
  | 6, 0, 2 => Z6_0_2Half w ij
  | 6, 1, 1 => B6_1_1Half w ij
  | 6, 2, 0 => Z6_2_0Half w ij
  | 7, 0, 1 => Z7_0_1Half w ij
  | 7, 1, 0 => Z7_1_0Half w ij
  | 8, 0, 0 => Z8_0_0Half w ij
  | _, _, _ => (.exact 0)

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

def pairDegree (ij : PairSlot) : ℕ := statisticWeight ij.1 + statisticWeight ij.2

def stageAPairBall (s : Shape) (bs : Shape → Ball) (w : Fin 3)
    (ij : PairSlot × PairSlot) : Ball :=
  if pairDegree ij.1 + pairDegree ij.2 = s w then
    sparsePairLawBall (below s) s bs (fun u => halfTable u w) ij
  else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_1_14I1
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
def CA1_1_14I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 1 14)) (shape 1 1 14) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA1_1_14I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 1 14) A1_1_14Law 1 a
def CA1_1_14I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 0, 1 => 1
  | 0, 0, 1, 0 => 1
  | 1, 0, 0, 0 => 1
  | 0, 1, 0, 0 => 1
  | _, _, _, _ => 0
def CA1_1_14I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1PairCertificates (CA1_1_14I1PairCertificateIndex a)).input
def CA1_1_14I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1PairCertificates (CA1_1_14I1PairCertificateIndex a)).output

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
def CA1_1_14I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA1_1_14I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA1_1_14I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA1_1_14I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R0Certificates (CA1_1_14I1R0CertificateIndex a)).input
def CA1_1_14I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R0Certificates (CA1_1_14I1R0CertificateIndex a)).output
def CA1_1_14I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA1_1_14I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA1_1_14I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA1_1_14I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R1Certificates (CA1_1_14I1R1CertificateIndex a)).input
def CA1_1_14I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R1Certificates (CA1_1_14I1R1CertificateIndex a)).output
def CA1_1_14I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA1_1_14I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA1_1_14I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R2Certificates (CA1_1_14I1R2CertificateIndex a)).input
def CA1_1_14I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R2Certificates (CA1_1_14I1R2CertificateIndex a)).output
def CA1_1_14I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA1_1_14I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA1_1_14I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R3Certificates (CA1_1_14I1R3CertificateIndex a)).input
def CA1_1_14I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R3Certificates (CA1_1_14I1R3CertificateIndex a)).output
def CA1_1_14I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA1_1_14I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA1_1_14I1R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R4Certificates (CA1_1_14I1R4CertificateIndex a)).input
def CA1_1_14I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R4Certificates (CA1_1_14I1R4CertificateIndex a)).output
def CA1_1_14I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA1_1_14I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA1_1_14I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R5Certificates (CA1_1_14I1R5CertificateIndex a)).input
def CA1_1_14I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R5Certificates (CA1_1_14I1R5CertificateIndex a)).output
def CA1_1_14I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA1_1_14I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA1_1_14I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R6Certificates (CA1_1_14I1R6CertificateIndex a)).input
def CA1_1_14I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R6Certificates (CA1_1_14I1R6CertificateIndex a)).output
def CA1_1_14I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA1_1_14I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA1_1_14I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R7Certificates (CA1_1_14I1R7CertificateIndex a)).input
def CA1_1_14I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R7Certificates (CA1_1_14I1R7CertificateIndex a)).output
def CA1_1_14I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA1_1_14I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA1_1_14I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R8Certificates (CA1_1_14I1R8CertificateIndex a)).input
def CA1_1_14I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R8Certificates (CA1_1_14I1R8CertificateIndex a)).output
def CA1_1_14I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA1_1_14I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA1_1_14I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R9Certificates (CA1_1_14I1R9CertificateIndex a)).input
def CA1_1_14I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R9Certificates (CA1_1_14I1R9CertificateIndex a)).output
def CA1_1_14I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA1_1_14I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA1_1_14I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R10Certificates (CA1_1_14I1R10CertificateIndex a)).input
def CA1_1_14I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R10Certificates (CA1_1_14I1R10CertificateIndex a)).output
def CA1_1_14I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA1_1_14I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA1_1_14I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R11Certificates (CA1_1_14I1R11CertificateIndex a)).input
def CA1_1_14I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R11Certificates (CA1_1_14I1R11CertificateIndex a)).output
def CA1_1_14I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA1_1_14I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA1_1_14I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R12Certificates (CA1_1_14I1R12CertificateIndex a)).input
def CA1_1_14I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R12Certificates (CA1_1_14I1R12CertificateIndex a)).output
def CA1_1_14I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA1_1_14I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA1_1_14I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R13Certificates (CA1_1_14I1R13CertificateIndex a)).input
def CA1_1_14I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R13Certificates (CA1_1_14I1R13CertificateIndex a)).output
def CA1_1_14I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA1_1_14I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA1_1_14I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R14Certificates (CA1_1_14I1R14CertificateIndex a)).input
def CA1_1_14I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R14Certificates (CA1_1_14I1R14CertificateIndex a)).output
def CA1_1_14I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA1_1_14I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA1_1_14I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R15Certificates (CA1_1_14I1R15CertificateIndex a)).input
def CA1_1_14I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R15Certificates (CA1_1_14I1R15CertificateIndex a)).output
def CA1_1_14I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA1_1_14I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
def CA1_1_14I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R16Certificates (CA1_1_14I1R16CertificateIndex a)).input
def CA1_1_14I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I1R16Certificates (CA1_1_14I1R16CertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_1_14I2
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
def CA1_1_14I2PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 1 14)) (shape 1 1 14) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) a
def CA1_1_14I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 1 14) A1_1_14Law 2 a
def CA1_1_14I2PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 5, 5, 5, 2 => 1
  | 5, 5, 5, 3 => 2
  | 5, 5, 4, 4 => 3
  | 5, 5, 2, 5 => 1
  | 5, 5, 3, 5 => 2
  | 4, 5, 4, 5 => 4
  | 4, 5, 5, 4 => 4
  | 5, 4, 4, 5 => 4
  | 5, 4, 5, 4 => 4
  | 5, 2, 5, 5 => 1
  | 5, 3, 5, 5 => 2
  | 4, 4, 5, 5 => 3
  | 2, 5, 5, 5 => 1
  | 3, 5, 5, 5 => 2
  | _, _, _, _ => 0
def CA1_1_14I2PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2PairCertificates (CA1_1_14I2PairCertificateIndex a)).input
def CA1_1_14I2PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2PairCertificates (CA1_1_14I2PairCertificateIndex a)).output

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
def CA1_1_14I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA1_1_14I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA1_1_14I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R0Certificates (CA1_1_14I2R0CertificateIndex a)).input
def CA1_1_14I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R0Certificates (CA1_1_14I2R0CertificateIndex a)).output
def CA1_1_14I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA1_1_14I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA1_1_14I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R1Certificates (CA1_1_14I2R1CertificateIndex a)).input
def CA1_1_14I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R1Certificates (CA1_1_14I2R1CertificateIndex a)).output
def CA1_1_14I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA1_1_14I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA1_1_14I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R2Certificates (CA1_1_14I2R2CertificateIndex a)).input
def CA1_1_14I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R2Certificates (CA1_1_14I2R2CertificateIndex a)).output
def CA1_1_14I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA1_1_14I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA1_1_14I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R3Certificates (CA1_1_14I2R3CertificateIndex a)).input
def CA1_1_14I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R3Certificates (CA1_1_14I2R3CertificateIndex a)).output
def CA1_1_14I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA1_1_14I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA1_1_14I2R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R4Certificates (CA1_1_14I2R4CertificateIndex a)).input
def CA1_1_14I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R4Certificates (CA1_1_14I2R4CertificateIndex a)).output
def CA1_1_14I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA1_1_14I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA1_1_14I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R5Certificates (CA1_1_14I2R5CertificateIndex a)).input
def CA1_1_14I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R5Certificates (CA1_1_14I2R5CertificateIndex a)).output
def CA1_1_14I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA1_1_14I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA1_1_14I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA1_1_14I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R6Certificates (CA1_1_14I2R6CertificateIndex a)).input
def CA1_1_14I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R6Certificates (CA1_1_14I2R6CertificateIndex a)).output
def CA1_1_14I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA1_1_14I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA1_1_14I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R7Certificates (CA1_1_14I2R7CertificateIndex a)).input
def CA1_1_14I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R7Certificates (CA1_1_14I2R7CertificateIndex a)).output
def CA1_1_14I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA1_1_14I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA1_1_14I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R8Certificates (CA1_1_14I2R8CertificateIndex a)).input
def CA1_1_14I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R8Certificates (CA1_1_14I2R8CertificateIndex a)).output
def CA1_1_14I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA1_1_14I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA1_1_14I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R9Certificates (CA1_1_14I2R9CertificateIndex a)).input
def CA1_1_14I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R9Certificates (CA1_1_14I2R9CertificateIndex a)).output
def CA1_1_14I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA1_1_14I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA1_1_14I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R10Certificates (CA1_1_14I2R10CertificateIndex a)).input
def CA1_1_14I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R10Certificates (CA1_1_14I2R10CertificateIndex a)).output
def CA1_1_14I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA1_1_14I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA1_1_14I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R11Certificates (CA1_1_14I2R11CertificateIndex a)).input
def CA1_1_14I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R11Certificates (CA1_1_14I2R11CertificateIndex a)).output
def CA1_1_14I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA1_1_14I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA1_1_14I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R12Certificates (CA1_1_14I2R12CertificateIndex a)).input
def CA1_1_14I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R12Certificates (CA1_1_14I2R12CertificateIndex a)).output
def CA1_1_14I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA1_1_14I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA1_1_14I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R13Certificates (CA1_1_14I2R13CertificateIndex a)).input
def CA1_1_14I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R13Certificates (CA1_1_14I2R13CertificateIndex a)).output
def CA1_1_14I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA1_1_14I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA1_1_14I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R14Certificates (CA1_1_14I2R14CertificateIndex a)).input
def CA1_1_14I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R14Certificates (CA1_1_14I2R14CertificateIndex a)).output
def CA1_1_14I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA1_1_14I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA1_1_14I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R15Certificates (CA1_1_14I2R15CertificateIndex a)).input
def CA1_1_14I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R15Certificates (CA1_1_14I2R15CertificateIndex a)).output
def CA1_1_14I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA1_1_14I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 1 14)) A1_1_14Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
def CA1_1_14I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_1_14I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R16Certificates (CA1_1_14I2R16CertificateIndex a)).input
def CA1_1_14I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I2R16Certificates (CA1_1_14I2R16CertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_2_13I1
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
def CA1_2_13I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 2 13)) (shape 1 2 13) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA1_2_13I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 2 13) A1_2_13Law 1 a
def CA1_2_13I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 0, 2 => 1
  | 0, 0, 0, 3 => 2
  | 0, 0, 1, 1 => 3
  | 0, 0, 2, 0 => 1
  | 0, 0, 3, 0 => 2
  | 1, 0, 0, 1 => 4
  | 1, 0, 1, 0 => 4
  | 0, 1, 0, 1 => 4
  | 0, 1, 1, 0 => 4
  | 2, 0, 0, 0 => 1
  | 3, 0, 0, 0 => 2
  | 1, 1, 0, 0 => 3
  | 0, 2, 0, 0 => 1
  | 0, 3, 0, 0 => 2
  | _, _, _, _ => 0
def CA1_2_13I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1PairCertificates (CA1_2_13I1PairCertificateIndex a)).input
def CA1_2_13I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1PairCertificates (CA1_2_13I1PairCertificateIndex a)).output

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
def CA1_2_13I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA1_2_13I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA1_2_13I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA1_2_13I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R0Certificates (CA1_2_13I1R0CertificateIndex a)).input
def CA1_2_13I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R0Certificates (CA1_2_13I1R0CertificateIndex a)).output
def CA1_2_13I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA1_2_13I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA1_2_13I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA1_2_13I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R1Certificates (CA1_2_13I1R1CertificateIndex a)).input
def CA1_2_13I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R1Certificates (CA1_2_13I1R1CertificateIndex a)).output
def CA1_2_13I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA1_2_13I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA1_2_13I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_2_13I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R2Certificates (CA1_2_13I1R2CertificateIndex a)).input
def CA1_2_13I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R2Certificates (CA1_2_13I1R2CertificateIndex a)).output
def CA1_2_13I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA1_2_13I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA1_2_13I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R3Certificates (CA1_2_13I1R3CertificateIndex a)).input
def CA1_2_13I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R3Certificates (CA1_2_13I1R3CertificateIndex a)).output
def CA1_2_13I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA1_2_13I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA1_2_13I1R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R4Certificates (CA1_2_13I1R4CertificateIndex a)).input
def CA1_2_13I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R4Certificates (CA1_2_13I1R4CertificateIndex a)).output
def CA1_2_13I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA1_2_13I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA1_2_13I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R5Certificates (CA1_2_13I1R5CertificateIndex a)).input
def CA1_2_13I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R5Certificates (CA1_2_13I1R5CertificateIndex a)).output
def CA1_2_13I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA1_2_13I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA1_2_13I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R6Certificates (CA1_2_13I1R6CertificateIndex a)).input
def CA1_2_13I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R6Certificates (CA1_2_13I1R6CertificateIndex a)).output
def CA1_2_13I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA1_2_13I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA1_2_13I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R7Certificates (CA1_2_13I1R7CertificateIndex a)).input
def CA1_2_13I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R7Certificates (CA1_2_13I1R7CertificateIndex a)).output
def CA1_2_13I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA1_2_13I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA1_2_13I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R8Certificates (CA1_2_13I1R8CertificateIndex a)).input
def CA1_2_13I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R8Certificates (CA1_2_13I1R8CertificateIndex a)).output
def CA1_2_13I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA1_2_13I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA1_2_13I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R9Certificates (CA1_2_13I1R9CertificateIndex a)).input
def CA1_2_13I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R9Certificates (CA1_2_13I1R9CertificateIndex a)).output
def CA1_2_13I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA1_2_13I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA1_2_13I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R10Certificates (CA1_2_13I1R10CertificateIndex a)).input
def CA1_2_13I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R10Certificates (CA1_2_13I1R10CertificateIndex a)).output
def CA1_2_13I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA1_2_13I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA1_2_13I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R11Certificates (CA1_2_13I1R11CertificateIndex a)).input
def CA1_2_13I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R11Certificates (CA1_2_13I1R11CertificateIndex a)).output
def CA1_2_13I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA1_2_13I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA1_2_13I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R12Certificates (CA1_2_13I1R12CertificateIndex a)).input
def CA1_2_13I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R12Certificates (CA1_2_13I1R12CertificateIndex a)).output
def CA1_2_13I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA1_2_13I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA1_2_13I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R13Certificates (CA1_2_13I1R13CertificateIndex a)).input
def CA1_2_13I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R13Certificates (CA1_2_13I1R13CertificateIndex a)).output
def CA1_2_13I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA1_2_13I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA1_2_13I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R14Certificates (CA1_2_13I1R14CertificateIndex a)).input
def CA1_2_13I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R14Certificates (CA1_2_13I1R14CertificateIndex a)).output
def CA1_2_13I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA1_2_13I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA1_2_13I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R15Certificates (CA1_2_13I1R15CertificateIndex a)).input
def CA1_2_13I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R15Certificates (CA1_2_13I1R15CertificateIndex a)).output
def CA1_2_13I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA1_2_13I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
def CA1_2_13I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R16Certificates (CA1_2_13I1R16CertificateIndex a)).input
def CA1_2_13I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I1R16Certificates (CA1_2_13I1R16CertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_2_13I2
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
def CA1_2_13I2PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 2 13)) (shape 1 2 13) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) a
def CA1_2_13I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 2 13) A1_2_13Law 2 a
def CA1_2_13I2PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 5, 5, 5, 1 => 1
  | 5, 5, 4, 2 => 2
  | 5, 5, 4, 3 => 3
  | 5, 5, 2, 4 => 2
  | 5, 5, 3, 4 => 3
  | 5, 5, 1, 5 => 1
  | 4, 5, 5, 2 => 4
  | 4, 5, 5, 3 => 5
  | 4, 5, 4, 4 => 6
  | 4, 5, 2, 5 => 4
  | 4, 5, 3, 5 => 5
  | 5, 4, 5, 2 => 4
  | 5, 4, 5, 3 => 5
  | 5, 4, 4, 4 => 6
  | 5, 4, 2, 5 => 4
  | 5, 4, 3, 5 => 5
  | 2, 5, 4, 5 => 4
  | 2, 5, 5, 4 => 4
  | 3, 5, 4, 5 => 5
  | 3, 5, 5, 4 => 5
  | 4, 4, 4, 5 => 6
  | 4, 4, 5, 4 => 6
  | 5, 2, 4, 5 => 4
  | 5, 2, 5, 4 => 4
  | 5, 3, 4, 5 => 5
  | 5, 3, 5, 4 => 5
  | 5, 1, 5, 5 => 1
  | 4, 2, 5, 5 => 2
  | 4, 3, 5, 5 => 3
  | 2, 4, 5, 5 => 2
  | 3, 4, 5, 5 => 3
  | 1, 5, 5, 5 => 1
  | _, _, _, _ => 0
def CA1_2_13I2PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2PairCertificates (CA1_2_13I2PairCertificateIndex a)).input
def CA1_2_13I2PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2PairCertificates (CA1_2_13I2PairCertificateIndex a)).output

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
def CA1_2_13I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA1_2_13I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA1_2_13I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R0Certificates (CA1_2_13I2R0CertificateIndex a)).input
def CA1_2_13I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R0Certificates (CA1_2_13I2R0CertificateIndex a)).output
def CA1_2_13I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA1_2_13I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA1_2_13I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R1Certificates (CA1_2_13I2R1CertificateIndex a)).input
def CA1_2_13I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R1Certificates (CA1_2_13I2R1CertificateIndex a)).output
def CA1_2_13I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA1_2_13I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA1_2_13I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R2Certificates (CA1_2_13I2R2CertificateIndex a)).input
def CA1_2_13I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R2Certificates (CA1_2_13I2R2CertificateIndex a)).output
def CA1_2_13I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA1_2_13I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA1_2_13I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R3Certificates (CA1_2_13I2R3CertificateIndex a)).input
def CA1_2_13I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R3Certificates (CA1_2_13I2R3CertificateIndex a)).output
def CA1_2_13I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA1_2_13I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA1_2_13I2R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R4Certificates (CA1_2_13I2R4CertificateIndex a)).input
def CA1_2_13I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R4Certificates (CA1_2_13I2R4CertificateIndex a)).output
def CA1_2_13I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA1_2_13I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA1_2_13I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA1_2_13I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R5Certificates (CA1_2_13I2R5CertificateIndex a)).input
def CA1_2_13I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R5Certificates (CA1_2_13I2R5CertificateIndex a)).output
def CA1_2_13I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA1_2_13I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA1_2_13I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA1_2_13I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R6Certificates (CA1_2_13I2R6CertificateIndex a)).input
def CA1_2_13I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R6Certificates (CA1_2_13I2R6CertificateIndex a)).output
def CA1_2_13I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA1_2_13I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA1_2_13I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R7Certificates (CA1_2_13I2R7CertificateIndex a)).input
def CA1_2_13I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R7Certificates (CA1_2_13I2R7CertificateIndex a)).output
def CA1_2_13I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA1_2_13I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA1_2_13I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R8Certificates (CA1_2_13I2R8CertificateIndex a)).input
def CA1_2_13I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R8Certificates (CA1_2_13I2R8CertificateIndex a)).output
def CA1_2_13I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA1_2_13I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA1_2_13I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R9Certificates (CA1_2_13I2R9CertificateIndex a)).input
def CA1_2_13I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R9Certificates (CA1_2_13I2R9CertificateIndex a)).output
def CA1_2_13I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA1_2_13I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA1_2_13I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R10Certificates (CA1_2_13I2R10CertificateIndex a)).input
def CA1_2_13I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R10Certificates (CA1_2_13I2R10CertificateIndex a)).output
def CA1_2_13I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA1_2_13I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA1_2_13I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R11Certificates (CA1_2_13I2R11CertificateIndex a)).input
def CA1_2_13I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R11Certificates (CA1_2_13I2R11CertificateIndex a)).output
def CA1_2_13I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA1_2_13I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA1_2_13I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R12Certificates (CA1_2_13I2R12CertificateIndex a)).input
def CA1_2_13I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R12Certificates (CA1_2_13I2R12CertificateIndex a)).output
def CA1_2_13I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA1_2_13I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA1_2_13I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R13Certificates (CA1_2_13I2R13CertificateIndex a)).input
def CA1_2_13I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R13Certificates (CA1_2_13I2R13CertificateIndex a)).output
def CA1_2_13I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA1_2_13I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA1_2_13I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R14Certificates (CA1_2_13I2R14CertificateIndex a)).input
def CA1_2_13I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R14Certificates (CA1_2_13I2R14CertificateIndex a)).output
def CA1_2_13I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA1_2_13I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA1_2_13I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R15Certificates (CA1_2_13I2R15CertificateIndex a)).input
def CA1_2_13I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R15Certificates (CA1_2_13I2R15CertificateIndex a)).output
def CA1_2_13I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA1_2_13I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 2 13)) A1_2_13Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
def CA1_2_13I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_2_13I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R16Certificates (CA1_2_13I2R16CertificateIndex a)).input
def CA1_2_13I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I2R16Certificates (CA1_2_13I2R16CertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_3_12I1
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
def CA1_3_12I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 3 12)) (shape 1 3 12) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA1_3_12I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 3 12) A1_3_12Law 1 a
def CA1_3_12I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 0, 4 => 1
  | 0, 0, 1, 2 => 2
  | 0, 0, 1, 3 => 3
  | 0, 0, 2, 1 => 2
  | 0, 0, 3, 1 => 3
  | 0, 0, 4, 0 => 1
  | 1, 0, 0, 2 => 4
  | 1, 0, 0, 3 => 5
  | 1, 0, 1, 1 => 6
  | 1, 0, 2, 0 => 4
  | 1, 0, 3, 0 => 5
  | 0, 1, 0, 2 => 4
  | 0, 1, 0, 3 => 5
  | 0, 1, 1, 1 => 6
  | 0, 1, 2, 0 => 4
  | 0, 1, 3, 0 => 5
  | 2, 0, 0, 1 => 4
  | 2, 0, 1, 0 => 4
  | 3, 0, 0, 1 => 5
  | 3, 0, 1, 0 => 5
  | 1, 1, 0, 1 => 6
  | 1, 1, 1, 0 => 6
  | 0, 2, 0, 1 => 4
  | 0, 2, 1, 0 => 4
  | 0, 3, 0, 1 => 5
  | 0, 3, 1, 0 => 5
  | 4, 0, 0, 0 => 1
  | 2, 1, 0, 0 => 2
  | 3, 1, 0, 0 => 3
  | 1, 2, 0, 0 => 2
  | 1, 3, 0, 0 => 3
  | 0, 4, 0, 0 => 1
  | _, _, _, _ => 0
def CA1_3_12I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1PairCertificates (CA1_3_12I1PairCertificateIndex a)).input
def CA1_3_12I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1PairCertificates (CA1_3_12I1PairCertificateIndex a)).output

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
def CA1_3_12I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA1_3_12I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA1_3_12I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA1_3_12I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R0Certificates (CA1_3_12I1R0CertificateIndex a)).input
def CA1_3_12I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R0Certificates (CA1_3_12I1R0CertificateIndex a)).output
def CA1_3_12I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA1_3_12I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA1_3_12I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA1_3_12I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R1Certificates (CA1_3_12I1R1CertificateIndex a)).input
def CA1_3_12I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R1Certificates (CA1_3_12I1R1CertificateIndex a)).output
def CA1_3_12I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA1_3_12I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA1_3_12I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_3_12I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R2Certificates (CA1_3_12I1R2CertificateIndex a)).input
def CA1_3_12I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R2Certificates (CA1_3_12I1R2CertificateIndex a)).output
def CA1_3_12I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA1_3_12I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA1_3_12I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_3_12I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R3Certificates (CA1_3_12I1R3CertificateIndex a)).input
def CA1_3_12I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R3Certificates (CA1_3_12I1R3CertificateIndex a)).output
def CA1_3_12I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA1_3_12I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA1_3_12I1R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R4Certificates (CA1_3_12I1R4CertificateIndex a)).input
def CA1_3_12I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R4Certificates (CA1_3_12I1R4CertificateIndex a)).output
def CA1_3_12I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA1_3_12I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA1_3_12I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R5Certificates (CA1_3_12I1R5CertificateIndex a)).input
def CA1_3_12I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R5Certificates (CA1_3_12I1R5CertificateIndex a)).output
def CA1_3_12I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA1_3_12I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA1_3_12I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R6Certificates (CA1_3_12I1R6CertificateIndex a)).input
def CA1_3_12I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R6Certificates (CA1_3_12I1R6CertificateIndex a)).output
def CA1_3_12I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA1_3_12I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA1_3_12I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R7Certificates (CA1_3_12I1R7CertificateIndex a)).input
def CA1_3_12I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R7Certificates (CA1_3_12I1R7CertificateIndex a)).output
def CA1_3_12I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA1_3_12I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA1_3_12I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R8Certificates (CA1_3_12I1R8CertificateIndex a)).input
def CA1_3_12I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R8Certificates (CA1_3_12I1R8CertificateIndex a)).output
def CA1_3_12I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA1_3_12I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA1_3_12I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R9Certificates (CA1_3_12I1R9CertificateIndex a)).input
def CA1_3_12I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R9Certificates (CA1_3_12I1R9CertificateIndex a)).output
def CA1_3_12I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA1_3_12I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA1_3_12I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R10Certificates (CA1_3_12I1R10CertificateIndex a)).input
def CA1_3_12I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R10Certificates (CA1_3_12I1R10CertificateIndex a)).output
def CA1_3_12I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA1_3_12I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA1_3_12I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R11Certificates (CA1_3_12I1R11CertificateIndex a)).input
def CA1_3_12I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R11Certificates (CA1_3_12I1R11CertificateIndex a)).output
def CA1_3_12I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA1_3_12I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA1_3_12I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R12Certificates (CA1_3_12I1R12CertificateIndex a)).input
def CA1_3_12I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R12Certificates (CA1_3_12I1R12CertificateIndex a)).output
def CA1_3_12I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA1_3_12I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA1_3_12I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R13Certificates (CA1_3_12I1R13CertificateIndex a)).input
def CA1_3_12I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R13Certificates (CA1_3_12I1R13CertificateIndex a)).output
def CA1_3_12I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA1_3_12I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA1_3_12I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R14Certificates (CA1_3_12I1R14CertificateIndex a)).input
def CA1_3_12I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R14Certificates (CA1_3_12I1R14CertificateIndex a)).output
def CA1_3_12I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA1_3_12I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA1_3_12I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R15Certificates (CA1_3_12I1R15CertificateIndex a)).input
def CA1_3_12I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R15Certificates (CA1_3_12I1R15CertificateIndex a)).output
def CA1_3_12I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA1_3_12I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
def CA1_3_12I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R16Certificates (CA1_3_12I1R16CertificateIndex a)).input
def CA1_3_12I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I1R16Certificates (CA1_3_12I1R16CertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_3_12I2
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
def CA1_3_12I2PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 3 12)) (shape 1 3 12) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) a
def CA1_3_12I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 3 12) A1_3_12Law 2 a
def CA1_3_12I2PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 5, 5, 5, 0 => 1
  | 5, 5, 4, 1 => 2
  | 5, 5, 2, 2 => 3
  | 5, 5, 2, 3 => 4
  | 5, 5, 3, 2 => 4
  | 5, 5, 3, 3 => 5
  | 5, 5, 1, 4 => 2
  | 5, 5, 0, 5 => 1
  | 4, 5, 5, 1 => 6
  | 4, 5, 4, 2 => 7
  | 4, 5, 4, 3 => 8
  | 4, 5, 2, 4 => 7
  | 4, 5, 3, 4 => 8
  | 4, 5, 1, 5 => 6
  | 5, 4, 5, 1 => 6
  | 5, 4, 4, 2 => 7
  | 5, 4, 4, 3 => 8
  | 5, 4, 2, 4 => 7
  | 5, 4, 3, 4 => 8
  | 5, 4, 1, 5 => 6
  | 2, 5, 5, 2 => 9
  | 2, 5, 5, 3 => 10
  | 2, 5, 4, 4 => 11
  | 2, 5, 2, 5 => 9
  | 2, 5, 3, 5 => 10
  | 3, 5, 5, 2 => 10
  | 3, 5, 5, 3 => 12
  | 3, 5, 4, 4 => 13
  | 3, 5, 2, 5 => 10
  | 3, 5, 3, 5 => 12
  | 4, 4, 5, 2 => 11
  | 4, 4, 5, 3 => 13
  | 4, 4, 4, 4 => 14
  | 4, 4, 2, 5 => 11
  | 4, 4, 3, 5 => 13
  | 5, 2, 5, 2 => 9
  | 5, 2, 5, 3 => 10
  | 5, 2, 4, 4 => 11
  | 5, 2, 2, 5 => 9
  | 5, 2, 3, 5 => 10
  | 5, 3, 5, 2 => 10
  | 5, 3, 5, 3 => 12
  | 5, 3, 4, 4 => 13
  | 5, 3, 2, 5 => 10
  | 5, 3, 3, 5 => 12
  | 1, 5, 4, 5 => 6
  | 1, 5, 5, 4 => 6
  | 2, 4, 4, 5 => 7
  | 2, 4, 5, 4 => 7
  | 3, 4, 4, 5 => 8
  | 3, 4, 5, 4 => 8
  | 4, 2, 4, 5 => 7
  | 4, 2, 5, 4 => 7
  | 4, 3, 4, 5 => 8
  | 4, 3, 5, 4 => 8
  | 5, 1, 4, 5 => 6
  | 5, 1, 5, 4 => 6
  | 5, 0, 5, 5 => 1
  | 4, 1, 5, 5 => 2
  | 2, 2, 5, 5 => 3
  | 2, 3, 5, 5 => 4
  | 3, 2, 5, 5 => 4
  | 3, 3, 5, 5 => 5
  | 1, 4, 5, 5 => 2
  | 0, 5, 5, 5 => 1
  | _, _, _, _ => 0
def CA1_3_12I2PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2PairCertificates (CA1_3_12I2PairCertificateIndex a)).input
def CA1_3_12I2PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2PairCertificates (CA1_3_12I2PairCertificateIndex a)).output

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
def CA1_3_12I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA1_3_12I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA1_3_12I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R0Certificates (CA1_3_12I2R0CertificateIndex a)).input
def CA1_3_12I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R0Certificates (CA1_3_12I2R0CertificateIndex a)).output
def CA1_3_12I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA1_3_12I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA1_3_12I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R1Certificates (CA1_3_12I2R1CertificateIndex a)).input
def CA1_3_12I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R1Certificates (CA1_3_12I2R1CertificateIndex a)).output
def CA1_3_12I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA1_3_12I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA1_3_12I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R2Certificates (CA1_3_12I2R2CertificateIndex a)).input
def CA1_3_12I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R2Certificates (CA1_3_12I2R2CertificateIndex a)).output
def CA1_3_12I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA1_3_12I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA1_3_12I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R3Certificates (CA1_3_12I2R3CertificateIndex a)).input
def CA1_3_12I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R3Certificates (CA1_3_12I2R3CertificateIndex a)).output
def CA1_3_12I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA1_3_12I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA1_3_12I2R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 0 => 1
  | 4, 1 => 2
  | 2, 2 => 3
  | 2, 3 => 4
  | 3, 2 => 4
  | 3, 3 => 5
  | 1, 4 => 2
  | 0, 5 => 1
  | _, _ => 0
def CA1_3_12I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R4Certificates (CA1_3_12I2R4CertificateIndex a)).input
def CA1_3_12I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R4Certificates (CA1_3_12I2R4CertificateIndex a)).output
def CA1_3_12I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA1_3_12I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA1_3_12I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA1_3_12I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R5Certificates (CA1_3_12I2R5CertificateIndex a)).input
def CA1_3_12I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R5Certificates (CA1_3_12I2R5CertificateIndex a)).output
def CA1_3_12I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA1_3_12I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA1_3_12I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA1_3_12I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R6Certificates (CA1_3_12I2R6CertificateIndex a)).input
def CA1_3_12I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R6Certificates (CA1_3_12I2R6CertificateIndex a)).output
def CA1_3_12I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA1_3_12I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA1_3_12I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R7Certificates (CA1_3_12I2R7CertificateIndex a)).input
def CA1_3_12I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R7Certificates (CA1_3_12I2R7CertificateIndex a)).output
def CA1_3_12I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA1_3_12I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA1_3_12I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R8Certificates (CA1_3_12I2R8CertificateIndex a)).input
def CA1_3_12I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R8Certificates (CA1_3_12I2R8CertificateIndex a)).output
def CA1_3_12I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA1_3_12I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA1_3_12I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R9Certificates (CA1_3_12I2R9CertificateIndex a)).input
def CA1_3_12I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R9Certificates (CA1_3_12I2R9CertificateIndex a)).output
def CA1_3_12I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA1_3_12I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA1_3_12I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R10Certificates (CA1_3_12I2R10CertificateIndex a)).input
def CA1_3_12I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R10Certificates (CA1_3_12I2R10CertificateIndex a)).output
def CA1_3_12I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA1_3_12I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA1_3_12I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R11Certificates (CA1_3_12I2R11CertificateIndex a)).input
def CA1_3_12I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R11Certificates (CA1_3_12I2R11CertificateIndex a)).output
def CA1_3_12I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA1_3_12I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA1_3_12I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R12Certificates (CA1_3_12I2R12CertificateIndex a)).input
def CA1_3_12I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R12Certificates (CA1_3_12I2R12CertificateIndex a)).output
def CA1_3_12I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA1_3_12I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA1_3_12I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R13Certificates (CA1_3_12I2R13CertificateIndex a)).input
def CA1_3_12I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R13Certificates (CA1_3_12I2R13CertificateIndex a)).output
def CA1_3_12I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA1_3_12I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA1_3_12I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R14Certificates (CA1_3_12I2R14CertificateIndex a)).input
def CA1_3_12I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R14Certificates (CA1_3_12I2R14CertificateIndex a)).output
def CA1_3_12I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA1_3_12I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA1_3_12I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R15Certificates (CA1_3_12I2R15CertificateIndex a)).input
def CA1_3_12I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R15Certificates (CA1_3_12I2R15CertificateIndex a)).output
def CA1_3_12I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA1_3_12I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 3 12)) A1_3_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
def CA1_3_12I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_3_12I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R16Certificates (CA1_3_12I2R16CertificateIndex a)).input
def CA1_3_12I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I2R16Certificates (CA1_3_12I2R16CertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_4_11I1
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
def CA1_4_11I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 4 11)) (shape 1 4 11) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA1_4_11I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 4 11) A1_4_11Law 1 a
def CA1_4_11I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 1, 4 => 1
  | 0, 0, 2, 2 => 2
  | 0, 0, 2, 3 => 3
  | 0, 0, 3, 2 => 3
  | 0, 0, 3, 3 => 4
  | 0, 0, 4, 1 => 1
  | 0, 0, 5, 0 => 5
  | 0, 0, 0, 5 => 5
  | 1, 0, 0, 4 => 6
  | 1, 0, 1, 2 => 7
  | 1, 0, 1, 3 => 8
  | 1, 0, 2, 1 => 7
  | 1, 0, 3, 1 => 8
  | 1, 0, 4, 0 => 6
  | 0, 1, 0, 4 => 6
  | 0, 1, 1, 2 => 7
  | 0, 1, 1, 3 => 8
  | 0, 1, 2, 1 => 7
  | 0, 1, 3, 1 => 8
  | 0, 1, 4, 0 => 6
  | 2, 0, 0, 2 => 9
  | 2, 0, 0, 3 => 10
  | 2, 0, 1, 1 => 11
  | 2, 0, 2, 0 => 9
  | 2, 0, 3, 0 => 10
  | 3, 0, 0, 2 => 10
  | 3, 0, 0, 3 => 12
  | 3, 0, 1, 1 => 13
  | 3, 0, 2, 0 => 10
  | 3, 0, 3, 0 => 12
  | 1, 1, 0, 2 => 11
  | 1, 1, 0, 3 => 13
  | 1, 1, 1, 1 => 14
  | 1, 1, 2, 0 => 11
  | 1, 1, 3, 0 => 13
  | 0, 2, 0, 2 => 9
  | 0, 2, 0, 3 => 10
  | 0, 2, 1, 1 => 11
  | 0, 2, 2, 0 => 9
  | 0, 2, 3, 0 => 10
  | 0, 3, 0, 2 => 10
  | 0, 3, 0, 3 => 12
  | 0, 3, 1, 1 => 13
  | 0, 3, 2, 0 => 10
  | 0, 3, 3, 0 => 12
  | 4, 0, 0, 1 => 6
  | 4, 0, 1, 0 => 6
  | 2, 1, 0, 1 => 7
  | 2, 1, 1, 0 => 7
  | 3, 1, 0, 1 => 8
  | 3, 1, 1, 0 => 8
  | 1, 2, 0, 1 => 7
  | 1, 2, 1, 0 => 7
  | 1, 3, 0, 1 => 8
  | 1, 3, 1, 0 => 8
  | 0, 4, 0, 1 => 6
  | 0, 4, 1, 0 => 6
  | 0, 5, 0, 0 => 5
  | 1, 4, 0, 0 => 1
  | 2, 2, 0, 0 => 2
  | 2, 3, 0, 0 => 3
  | 3, 2, 0, 0 => 3
  | 3, 3, 0, 0 => 4
  | 4, 1, 0, 0 => 1
  | 5, 0, 0, 0 => 5
  | _, _, _, _ => 0
def CA1_4_11I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1PairCertificates (CA1_4_11I1PairCertificateIndex a)).input
def CA1_4_11I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1PairCertificates (CA1_4_11I1PairCertificateIndex a)).output

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
def CA1_4_11I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA1_4_11I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA1_4_11I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA1_4_11I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R0Certificates (CA1_4_11I1R0CertificateIndex a)).input
def CA1_4_11I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R0Certificates (CA1_4_11I1R0CertificateIndex a)).output
def CA1_4_11I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA1_4_11I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA1_4_11I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA1_4_11I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R1Certificates (CA1_4_11I1R1CertificateIndex a)).input
def CA1_4_11I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R1Certificates (CA1_4_11I1R1CertificateIndex a)).output
def CA1_4_11I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA1_4_11I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA1_4_11I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_4_11I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R2Certificates (CA1_4_11I1R2CertificateIndex a)).input
def CA1_4_11I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R2Certificates (CA1_4_11I1R2CertificateIndex a)).output
def CA1_4_11I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA1_4_11I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA1_4_11I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_4_11I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R3Certificates (CA1_4_11I1R3CertificateIndex a)).input
def CA1_4_11I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R3Certificates (CA1_4_11I1R3CertificateIndex a)).output
def CA1_4_11I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA1_4_11I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA1_4_11I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA1_4_11I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R4Certificates (CA1_4_11I1R4CertificateIndex a)).input
def CA1_4_11I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R4Certificates (CA1_4_11I1R4CertificateIndex a)).output
def CA1_4_11I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA1_4_11I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA1_4_11I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R5Certificates (CA1_4_11I1R5CertificateIndex a)).input
def CA1_4_11I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R5Certificates (CA1_4_11I1R5CertificateIndex a)).output
def CA1_4_11I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA1_4_11I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA1_4_11I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R6Certificates (CA1_4_11I1R6CertificateIndex a)).input
def CA1_4_11I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R6Certificates (CA1_4_11I1R6CertificateIndex a)).output
def CA1_4_11I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA1_4_11I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA1_4_11I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R7Certificates (CA1_4_11I1R7CertificateIndex a)).input
def CA1_4_11I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R7Certificates (CA1_4_11I1R7CertificateIndex a)).output
def CA1_4_11I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA1_4_11I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA1_4_11I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R8Certificates (CA1_4_11I1R8CertificateIndex a)).input
def CA1_4_11I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R8Certificates (CA1_4_11I1R8CertificateIndex a)).output
def CA1_4_11I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA1_4_11I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA1_4_11I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R9Certificates (CA1_4_11I1R9CertificateIndex a)).input
def CA1_4_11I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R9Certificates (CA1_4_11I1R9CertificateIndex a)).output
def CA1_4_11I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA1_4_11I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA1_4_11I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R10Certificates (CA1_4_11I1R10CertificateIndex a)).input
def CA1_4_11I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R10Certificates (CA1_4_11I1R10CertificateIndex a)).output
def CA1_4_11I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA1_4_11I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA1_4_11I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R11Certificates (CA1_4_11I1R11CertificateIndex a)).input
def CA1_4_11I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R11Certificates (CA1_4_11I1R11CertificateIndex a)).output
def CA1_4_11I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA1_4_11I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA1_4_11I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R12Certificates (CA1_4_11I1R12CertificateIndex a)).input
def CA1_4_11I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R12Certificates (CA1_4_11I1R12CertificateIndex a)).output
def CA1_4_11I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA1_4_11I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA1_4_11I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R13Certificates (CA1_4_11I1R13CertificateIndex a)).input
def CA1_4_11I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R13Certificates (CA1_4_11I1R13CertificateIndex a)).output
def CA1_4_11I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA1_4_11I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA1_4_11I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R14Certificates (CA1_4_11I1R14CertificateIndex a)).input
def CA1_4_11I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R14Certificates (CA1_4_11I1R14CertificateIndex a)).output
def CA1_4_11I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA1_4_11I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA1_4_11I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R15Certificates (CA1_4_11I1R15CertificateIndex a)).input
def CA1_4_11I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R15Certificates (CA1_4_11I1R15CertificateIndex a)).output
def CA1_4_11I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA1_4_11I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
def CA1_4_11I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R16Certificates (CA1_4_11I1R16CertificateIndex a)).input
def CA1_4_11I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I1R16Certificates (CA1_4_11I1R16CertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_4_11I2
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
def CA1_4_11I2PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 4 11)) (shape 1 4 11) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) a
def CA1_4_11I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 4 11) A1_4_11Law 2 a
def CA1_4_11I2PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 5, 5, 4, 0 => 1
  | 5, 5, 2, 1 => 2
  | 5, 5, 3, 1 => 3
  | 5, 5, 1, 2 => 2
  | 5, 5, 1, 3 => 3
  | 5, 5, 0, 4 => 1
  | 4, 5, 5, 0 => 4
  | 4, 5, 4, 1 => 5
  | 4, 5, 2, 2 => 6
  | 4, 5, 2, 3 => 7
  | 4, 5, 3, 2 => 7
  | 4, 5, 3, 3 => 8
  | 4, 5, 1, 4 => 5
  | 4, 5, 0, 5 => 4
  | 5, 4, 5, 0 => 4
  | 5, 4, 4, 1 => 5
  | 5, 4, 2, 2 => 6
  | 5, 4, 2, 3 => 7
  | 5, 4, 3, 2 => 7
  | 5, 4, 3, 3 => 8
  | 5, 4, 1, 4 => 5
  | 5, 4, 0, 5 => 4
  | 2, 5, 5, 1 => 9
  | 2, 5, 4, 2 => 10
  | 2, 5, 4, 3 => 11
  | 2, 5, 2, 4 => 10
  | 2, 5, 3, 4 => 11
  | 2, 5, 1, 5 => 9
  | 3, 5, 5, 1 => 12
  | 3, 5, 4, 2 => 13
  | 3, 5, 4, 3 => 14
  | 3, 5, 2, 4 => 13
  | 3, 5, 3, 4 => 14
  | 3, 5, 1, 5 => 12
  | 4, 4, 5, 1 => 15
  | 4, 4, 4, 2 => 16
  | 4, 4, 4, 3 => 17
  | 4, 4, 2, 4 => 16
  | 4, 4, 3, 4 => 17
  | 4, 4, 1, 5 => 15
  | 5, 2, 5, 1 => 9
  | 5, 2, 4, 2 => 10
  | 5, 2, 4, 3 => 11
  | 5, 2, 2, 4 => 10
  | 5, 2, 3, 4 => 11
  | 5, 2, 1, 5 => 9
  | 5, 3, 5, 1 => 12
  | 5, 3, 4, 2 => 13
  | 5, 3, 4, 3 => 14
  | 5, 3, 2, 4 => 13
  | 5, 3, 3, 4 => 14
  | 5, 3, 1, 5 => 12
  | 1, 5, 5, 2 => 9
  | 1, 5, 5, 3 => 12
  | 1, 5, 4, 4 => 15
  | 1, 5, 2, 5 => 9
  | 1, 5, 3, 5 => 12
  | 2, 4, 5, 2 => 10
  | 2, 4, 5, 3 => 13
  | 2, 4, 4, 4 => 16
  | 2, 4, 2, 5 => 10
  | 2, 4, 3, 5 => 13
  | 3, 4, 5, 2 => 11
  | 3, 4, 5, 3 => 14
  | 3, 4, 4, 4 => 17
  | 3, 4, 2, 5 => 11
  | 3, 4, 3, 5 => 14
  | 4, 2, 5, 2 => 10
  | 4, 2, 5, 3 => 13
  | 4, 2, 4, 4 => 16
  | 4, 2, 2, 5 => 10
  | 4, 2, 3, 5 => 13
  | 4, 3, 5, 2 => 11
  | 4, 3, 5, 3 => 14
  | 4, 3, 4, 4 => 17
  | 4, 3, 2, 5 => 11
  | 4, 3, 3, 5 => 14
  | 5, 1, 5, 2 => 9
  | 5, 1, 5, 3 => 12
  | 5, 1, 4, 4 => 15
  | 5, 1, 2, 5 => 9
  | 5, 1, 3, 5 => 12
  | 5, 0, 4, 5 => 4
  | 5, 0, 5, 4 => 4
  | 4, 1, 4, 5 => 5
  | 4, 1, 5, 4 => 5
  | 2, 2, 4, 5 => 6
  | 2, 2, 5, 4 => 6
  | 2, 3, 4, 5 => 7
  | 2, 3, 5, 4 => 7
  | 3, 2, 4, 5 => 7
  | 3, 2, 5, 4 => 7
  | 3, 3, 4, 5 => 8
  | 3, 3, 5, 4 => 8
  | 1, 4, 4, 5 => 5
  | 1, 4, 5, 4 => 5
  | 0, 5, 4, 5 => 4
  | 0, 5, 5, 4 => 4
  | 4, 0, 5, 5 => 1
  | 2, 1, 5, 5 => 2
  | 3, 1, 5, 5 => 3
  | 1, 2, 5, 5 => 2
  | 1, 3, 5, 5 => 3
  | 0, 4, 5, 5 => 1
  | _, _, _, _ => 0
def CA1_4_11I2PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2PairCertificates (CA1_4_11I2PairCertificateIndex a)).input
def CA1_4_11I2PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2PairCertificates (CA1_4_11I2PairCertificateIndex a)).output

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
def CA1_4_11I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA1_4_11I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA1_4_11I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R0Certificates (CA1_4_11I2R0CertificateIndex a)).input
def CA1_4_11I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R0Certificates (CA1_4_11I2R0CertificateIndex a)).output
def CA1_4_11I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA1_4_11I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA1_4_11I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R1Certificates (CA1_4_11I2R1CertificateIndex a)).input
def CA1_4_11I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R1Certificates (CA1_4_11I2R1CertificateIndex a)).output
def CA1_4_11I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA1_4_11I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA1_4_11I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R2Certificates (CA1_4_11I2R2CertificateIndex a)).input
def CA1_4_11I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R2Certificates (CA1_4_11I2R2CertificateIndex a)).output
def CA1_4_11I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA1_4_11I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA1_4_11I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_4_11I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R3Certificates (CA1_4_11I2R3CertificateIndex a)).input
def CA1_4_11I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R3Certificates (CA1_4_11I2R3CertificateIndex a)).output
def CA1_4_11I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA1_4_11I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA1_4_11I2R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 0 => 1
  | 4, 1 => 2
  | 2, 2 => 3
  | 2, 3 => 4
  | 3, 2 => 4
  | 3, 3 => 5
  | 1, 4 => 2
  | 0, 5 => 1
  | _, _ => 0
def CA1_4_11I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R4Certificates (CA1_4_11I2R4CertificateIndex a)).input
def CA1_4_11I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R4Certificates (CA1_4_11I2R4CertificateIndex a)).output
def CA1_4_11I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA1_4_11I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA1_4_11I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA1_4_11I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R5Certificates (CA1_4_11I2R5CertificateIndex a)).input
def CA1_4_11I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R5Certificates (CA1_4_11I2R5CertificateIndex a)).output
def CA1_4_11I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA1_4_11I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA1_4_11I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA1_4_11I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R6Certificates (CA1_4_11I2R6CertificateIndex a)).input
def CA1_4_11I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R6Certificates (CA1_4_11I2R6CertificateIndex a)).output
def CA1_4_11I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA1_4_11I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA1_4_11I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R7Certificates (CA1_4_11I2R7CertificateIndex a)).input
def CA1_4_11I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R7Certificates (CA1_4_11I2R7CertificateIndex a)).output
def CA1_4_11I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA1_4_11I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA1_4_11I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R8Certificates (CA1_4_11I2R8CertificateIndex a)).input
def CA1_4_11I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R8Certificates (CA1_4_11I2R8CertificateIndex a)).output
def CA1_4_11I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA1_4_11I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA1_4_11I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R9Certificates (CA1_4_11I2R9CertificateIndex a)).input
def CA1_4_11I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R9Certificates (CA1_4_11I2R9CertificateIndex a)).output
def CA1_4_11I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA1_4_11I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA1_4_11I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R10Certificates (CA1_4_11I2R10CertificateIndex a)).input
def CA1_4_11I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R10Certificates (CA1_4_11I2R10CertificateIndex a)).output
def CA1_4_11I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA1_4_11I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA1_4_11I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R11Certificates (CA1_4_11I2R11CertificateIndex a)).input
def CA1_4_11I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R11Certificates (CA1_4_11I2R11CertificateIndex a)).output
def CA1_4_11I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA1_4_11I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA1_4_11I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R12Certificates (CA1_4_11I2R12CertificateIndex a)).input
def CA1_4_11I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R12Certificates (CA1_4_11I2R12CertificateIndex a)).output
def CA1_4_11I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA1_4_11I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA1_4_11I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R13Certificates (CA1_4_11I2R13CertificateIndex a)).input
def CA1_4_11I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R13Certificates (CA1_4_11I2R13CertificateIndex a)).output
def CA1_4_11I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA1_4_11I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA1_4_11I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R14Certificates (CA1_4_11I2R14CertificateIndex a)).input
def CA1_4_11I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R14Certificates (CA1_4_11I2R14CertificateIndex a)).output
def CA1_4_11I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA1_4_11I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA1_4_11I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R15Certificates (CA1_4_11I2R15CertificateIndex a)).input
def CA1_4_11I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R15Certificates (CA1_4_11I2R15CertificateIndex a)).output
def CA1_4_11I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA1_4_11I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 4 11)) A1_4_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
def CA1_4_11I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_4_11I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R16Certificates (CA1_4_11I2R16CertificateIndex a)).input
def CA1_4_11I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I2R16Certificates (CA1_4_11I2R16CertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_5_10I1
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
def CA1_5_10I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 5 10)) (shape 1 5 10) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA1_5_10I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 5 10) A1_5_10Law 1 a
def CA1_5_10I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 2, 4 => 1
  | 0, 0, 3, 4 => 2
  | 0, 0, 4, 2 => 1
  | 0, 0, 4, 3 => 2
  | 0, 0, 5, 1 => 3
  | 0, 0, 1, 5 => 3
  | 1, 0, 1, 4 => 4
  | 1, 0, 2, 2 => 5
  | 1, 0, 2, 3 => 6
  | 1, 0, 3, 2 => 6
  | 1, 0, 3, 3 => 7
  | 1, 0, 4, 1 => 4
  | 1, 0, 5, 0 => 8
  | 1, 0, 0, 5 => 8
  | 0, 1, 1, 4 => 4
  | 0, 1, 2, 2 => 5
  | 0, 1, 2, 3 => 6
  | 0, 1, 3, 2 => 6
  | 0, 1, 3, 3 => 7
  | 0, 1, 4, 1 => 4
  | 0, 1, 5, 0 => 8
  | 0, 1, 0, 5 => 8
  | 2, 0, 0, 4 => 9
  | 2, 0, 1, 2 => 10
  | 2, 0, 1, 3 => 11
  | 2, 0, 2, 1 => 10
  | 2, 0, 3, 1 => 11
  | 2, 0, 4, 0 => 9
  | 3, 0, 0, 4 => 12
  | 3, 0, 1, 2 => 13
  | 3, 0, 1, 3 => 14
  | 3, 0, 2, 1 => 13
  | 3, 0, 3, 1 => 14
  | 3, 0, 4, 0 => 12
  | 1, 1, 0, 4 => 15
  | 1, 1, 1, 2 => 16
  | 1, 1, 1, 3 => 17
  | 1, 1, 2, 1 => 16
  | 1, 1, 3, 1 => 17
  | 1, 1, 4, 0 => 15
  | 0, 2, 0, 4 => 9
  | 0, 2, 1, 2 => 10
  | 0, 2, 1, 3 => 11
  | 0, 2, 2, 1 => 10
  | 0, 2, 3, 1 => 11
  | 0, 2, 4, 0 => 9
  | 0, 3, 0, 4 => 12
  | 0, 3, 1, 2 => 13
  | 0, 3, 1, 3 => 14
  | 0, 3, 2, 1 => 13
  | 0, 3, 3, 1 => 14
  | 0, 3, 4, 0 => 12
  | 4, 0, 0, 2 => 9
  | 4, 0, 0, 3 => 12
  | 4, 0, 1, 1 => 15
  | 4, 0, 2, 0 => 9
  | 4, 0, 3, 0 => 12
  | 2, 1, 0, 2 => 10
  | 2, 1, 0, 3 => 13
  | 2, 1, 1, 1 => 16
  | 2, 1, 2, 0 => 10
  | 2, 1, 3, 0 => 13
  | 3, 1, 0, 2 => 11
  | 3, 1, 0, 3 => 14
  | 3, 1, 1, 1 => 17
  | 3, 1, 2, 0 => 11
  | 3, 1, 3, 0 => 14
  | 1, 2, 0, 2 => 10
  | 1, 2, 0, 3 => 13
  | 1, 2, 1, 1 => 16
  | 1, 2, 2, 0 => 10
  | 1, 2, 3, 0 => 13
  | 1, 3, 0, 2 => 11
  | 1, 3, 0, 3 => 14
  | 1, 3, 1, 1 => 17
  | 1, 3, 2, 0 => 11
  | 1, 3, 3, 0 => 14
  | 0, 4, 0, 2 => 9
  | 0, 4, 0, 3 => 12
  | 0, 4, 1, 1 => 15
  | 0, 4, 2, 0 => 9
  | 0, 4, 3, 0 => 12
  | 0, 5, 0, 1 => 8
  | 0, 5, 1, 0 => 8
  | 1, 4, 0, 1 => 4
  | 1, 4, 1, 0 => 4
  | 2, 2, 0, 1 => 5
  | 2, 2, 1, 0 => 5
  | 2, 3, 0, 1 => 6
  | 2, 3, 1, 0 => 6
  | 3, 2, 0, 1 => 6
  | 3, 2, 1, 0 => 6
  | 3, 3, 0, 1 => 7
  | 3, 3, 1, 0 => 7
  | 4, 1, 0, 1 => 4
  | 4, 1, 1, 0 => 4
  | 5, 0, 0, 1 => 8
  | 5, 0, 1, 0 => 8
  | 1, 5, 0, 0 => 3
  | 2, 4, 0, 0 => 1
  | 3, 4, 0, 0 => 2
  | 4, 2, 0, 0 => 1
  | 4, 3, 0, 0 => 2
  | 5, 1, 0, 0 => 3
  | _, _, _, _ => 0
def CA1_5_10I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1PairCertificates (CA1_5_10I1PairCertificateIndex a)).input
def CA1_5_10I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1PairCertificates (CA1_5_10I1PairCertificateIndex a)).output

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
def CA1_5_10I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA1_5_10I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA1_5_10I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA1_5_10I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R0Certificates (CA1_5_10I1R0CertificateIndex a)).input
def CA1_5_10I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R0Certificates (CA1_5_10I1R0CertificateIndex a)).output
def CA1_5_10I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA1_5_10I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA1_5_10I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA1_5_10I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R1Certificates (CA1_5_10I1R1CertificateIndex a)).input
def CA1_5_10I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R1Certificates (CA1_5_10I1R1CertificateIndex a)).output
def CA1_5_10I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA1_5_10I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA1_5_10I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_5_10I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R2Certificates (CA1_5_10I1R2CertificateIndex a)).input
def CA1_5_10I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R2Certificates (CA1_5_10I1R2CertificateIndex a)).output
def CA1_5_10I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA1_5_10I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA1_5_10I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_5_10I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R3Certificates (CA1_5_10I1R3CertificateIndex a)).input
def CA1_5_10I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R3Certificates (CA1_5_10I1R3CertificateIndex a)).output
def CA1_5_10I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA1_5_10I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA1_5_10I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA1_5_10I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R4Certificates (CA1_5_10I1R4CertificateIndex a)).input
def CA1_5_10I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R4Certificates (CA1_5_10I1R4CertificateIndex a)).output
def CA1_5_10I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA1_5_10I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA1_5_10I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CA1_5_10I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R5Certificates (CA1_5_10I1R5CertificateIndex a)).input
def CA1_5_10I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R5Certificates (CA1_5_10I1R5CertificateIndex a)).output
def CA1_5_10I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA1_5_10I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA1_5_10I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R6Certificates (CA1_5_10I1R6CertificateIndex a)).input
def CA1_5_10I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R6Certificates (CA1_5_10I1R6CertificateIndex a)).output
def CA1_5_10I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA1_5_10I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA1_5_10I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R7Certificates (CA1_5_10I1R7CertificateIndex a)).input
def CA1_5_10I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R7Certificates (CA1_5_10I1R7CertificateIndex a)).output
def CA1_5_10I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA1_5_10I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA1_5_10I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R8Certificates (CA1_5_10I1R8CertificateIndex a)).input
def CA1_5_10I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R8Certificates (CA1_5_10I1R8CertificateIndex a)).output
def CA1_5_10I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA1_5_10I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA1_5_10I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R9Certificates (CA1_5_10I1R9CertificateIndex a)).input
def CA1_5_10I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R9Certificates (CA1_5_10I1R9CertificateIndex a)).output
def CA1_5_10I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA1_5_10I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA1_5_10I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R10Certificates (CA1_5_10I1R10CertificateIndex a)).input
def CA1_5_10I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R10Certificates (CA1_5_10I1R10CertificateIndex a)).output
def CA1_5_10I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA1_5_10I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA1_5_10I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R11Certificates (CA1_5_10I1R11CertificateIndex a)).input
def CA1_5_10I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R11Certificates (CA1_5_10I1R11CertificateIndex a)).output
def CA1_5_10I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA1_5_10I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA1_5_10I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R12Certificates (CA1_5_10I1R12CertificateIndex a)).input
def CA1_5_10I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R12Certificates (CA1_5_10I1R12CertificateIndex a)).output
def CA1_5_10I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA1_5_10I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA1_5_10I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R13Certificates (CA1_5_10I1R13CertificateIndex a)).input
def CA1_5_10I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R13Certificates (CA1_5_10I1R13CertificateIndex a)).output
def CA1_5_10I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA1_5_10I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA1_5_10I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R14Certificates (CA1_5_10I1R14CertificateIndex a)).input
def CA1_5_10I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R14Certificates (CA1_5_10I1R14CertificateIndex a)).output
def CA1_5_10I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA1_5_10I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA1_5_10I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R15Certificates (CA1_5_10I1R15CertificateIndex a)).input
def CA1_5_10I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R15Certificates (CA1_5_10I1R15CertificateIndex a)).output
def CA1_5_10I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA1_5_10I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
def CA1_5_10I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R16Certificates (CA1_5_10I1R16CertificateIndex a)).input
def CA1_5_10I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R16Certificates (CA1_5_10I1R16CertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_5_10I2Pair
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
def CA1_5_10I2PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 5 10)) (shape 1 5 10) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) a
def CA1_5_10I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 5 10) A1_5_10Law 2 a
def CA1_5_10I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(447236789237316840707946291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(688610068444994029318992737 / 12500000000000000000000000000000), (179943 / 10000000000000000000000000000000)⟩ ⟨(-615879627987935948080324132652163 / 50000000000000000000000000000000), (402340873571 / 100000000000000000000000000000000)⟩ ⟨-18, 447236789237316840707946291, 381469726562500000000000000⟩,
   .log ⟨(53769237716673631681010297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(194052899722326233188264489 / 25000000000000000000000000000000), (25051 / 10000000000000000000000000000000)⟩ ⟨(-180449740374644722766312628984091 / 12500000000000000000000000000000), (18634799233 / 4000000000000000000000000000000)⟩ ⟨-21, 53769237716673631681010297, 47683715820312500000000000⟩,
   .log ⟨(1706374619138283140882338411 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(18733526669721479089924408983 / 100000000000000000000000000000000), (3071387 / 50000000000000000000000000000000)⟩ ⟨(-137231930635356939885690339142263 / 12500000000000000000000000000000), (179994530607 / 50000000000000000000000000000000)⟩ ⟨-16, 1706374619138283140882338411, 1525878906250000000000000000⟩,
   .log ⟨(3241139016201081741900431197 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(62514139484452513978237592137 / 100000000000000000000000000000000), (5147537 / 25000000000000000000000000000000)⟩ ⟨(-9643853468174428385920786865427 / 1000000000000000000000000000000), (317637370671 / 100000000000000000000000000000000)⟩ ⟨-14, 3241139016201081741900431197, 3051757812500000000000000000⟩,
   .log ⟨(183316638080722186838854373789 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1155208391188910650998770499159 / 100000000000000000000000000000000), (53375863 / 12500000000000000000000000000000)⟩ ⟨(-315085527228636714092310458820519 / 50000000000000000000000000000000), (58233515401 / 25000000000000000000000000000000)⟩ ⟨-10, 183316638080722186838854373789, 97656250000000000000000000000⟩,
   .log ⟨(17471312315954566585414775389 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(377920437811155753835039869 / 250000000000000000000000000000), (51795731 / 100000000000000000000000000000000)⟩ ⟨(-86523652253882248114946805809359 / 10000000000000000000000000000000), (59292307457 / 20000000000000000000000000000000)⟩ ⟨-13, 17471312315954566585414775389, 12207031250000000000000000000⟩,
   .log ⟨(622687359809091706509760327 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(3731963418358488179025749239 / 50000000000000000000000000000000), (1252669 / 50000000000000000000000000000000)⟩ ⟨(-1198663618128578138491381959184577 / 100000000000000000000000000000000), (402340810571 / 100000000000000000000000000000000)⟩ ⟨-18, 622687359809091706509760327, 381469726562500000000000000⟩,
   .log ⟨(20272164809224285723253563167 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(314273878220142774199993200043 / 25000000000000000000000000000000), (429279803 / 100000000000000000000000000000000)⟩ ⟨(-31005458092678999135442646726649 / 5000000000000000000000000000000), (26469779727 / 12500000000000000000000000000000)⟩ ⟨-9, 20272164809224285723253563167, 19531250000000000000000000000⟩,
   .log ⟨(2102272074250790204621278602629 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(507455825973427320434676662231 / 6250000000000000000000000000000), (779053511 / 25000000000000000000000000000000)⟩ ⟨(-96553787150366810293970918202207 / 25000000000000000000000000000000), (9264422891 / 6250000000000000000000000000000)⟩ ⟨-6, 2102272074250790204621278602629, 1562500000000000000000000000000⟩,
   .log ⟨(111221115180691714779777314009 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(756459872970579363643185617631 / 100000000000000000000000000000000), (64767967 / 25000000000000000000000000000000)⟩ ⟨(-170035130411527926187555275089797 / 25000000000000000000000000000000), (58233515353 / 25000000000000000000000000000000)⟩ ⟨-10, 111221115180691714779777314009, 97656250000000000000000000000⟩,
   .log ⟨(92101918036391963270099979 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(4353968393005264559923740189 / 50000000000000000000000000000000), (2964521 / 100000000000000000000000000000000)⟩ ⟨(-295458585841074292239596126826253 / 25000000000000000000000000000000), (12573149553 / 3125000000000000000000000000000)⟩ ⟨-18, 92101918036391963270099979, 47683715820312500000000000⟩,
   .log ⟨(1980714011568923376047003 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(11679471172473652795728637 / 2000000000000000000000000000000), (38591 / 20000000000000000000000000000000)⟩ ⟨(-1474149107879327921652579442921641 / 100000000000000000000000000000000), (487046469051 / 100000000000000000000000000000000)⟩ ⟨-22, 1980714011568923376047003, 1192092895507812500000000⟩,
   .log ⟨(3922986013242751549869149831 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(27491589264612354155404833677 / 20000000000000000000000000000000), (11630147 / 25000000000000000000000000000000)⟩ ⟨(-175195560039020679566071876309813 / 20000000000000000000000000000000), (148230768967 / 50000000000000000000000000000000)⟩ ⟨-13, 3922986013242751549869149831, 3051757812500000000000000000⟩,
   .log ⟨(83375800235145745215086008987 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1066613302661959727727064752781 / 100000000000000000000000000000000), (194210641 / 50000000000000000000000000000000)⟩ ⟨(-127928403643956369452961201085279 / 20000000000000000000000000000000), (29116757639 / 12500000000000000000000000000000)⟩ ⟨-10, 83375800235145745215086008987, 48828125000000000000000000000⟩,
   .log ⟨(8646206533355745804790161179 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(5055763781945299190277427299 / 6250000000000000000000000000000), (27463593 / 100000000000000000000000000000000)⟩ ⟨(-29236889972735058948765842287483 / 3125000000000000000000000000000), (31763736681 / 10000000000000000000000000000000)⟩ ⟨-14, 8646206533355745804790161179, 6103515625000000000000000000⟩,
   .log ⟨(2063257465845684282331253 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(31761392632433117809477861 / 10000000000000000000000000000000), (26219 / 25000000000000000000000000000000)⟩ ⟨(-384845240574651391920675325717799 / 25000000000000000000000000000000), (63528076887 / 12500000000000000000000000000000)⟩ ⟨-23, 2063257465845684282331253, 1192092895507812500000000⟩,
   .log ⟨(3874243817958301501429918271 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(135943815595302065538285069041 / 100000000000000000000000000000000), (45942581 / 100000000000000000000000000000000)⟩ ⟨(-877228060384074343634582168844643 / 100000000000000000000000000000000), (148230769007 / 50000000000000000000000000000000)⟩ ⟨-13, 3874243817958301501429918271, 3051757812500000000000000000⟩,
   .log ⟨(191008923016041377412620830947 / 12500000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩ ⟨(1597279180750824162549435636669 / 25000000000000000000000000000000), (80895427 / 3125000000000000000000000000000)⟩ ⟨(-418116377897351138445099644060711 / 100000000000000000000000000000000), (169406590053 / 100000000000000000000000000000000)⟩ ⟨-7, 191008923016041377412620830947, 97656250000000000000000000000⟩,
   .log ⟨(10785136579497245115988190180163 / 100000000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩ ⟨(6004628140468174260369868483247 / 25000000000000000000000000000000), (11419207673 / 100000000000000000000000000000000)⟩ ⟨(-222700124238874801461167822386801 / 100000000000000000000000000000000), (105879118823 / 100000000000000000000000000000000)⟩ ⟨-4, 10785136579497245115988190180163, 6250000000000000000000000000000⟩,
   .log ⟨(791822085718177342495688877343 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(957825356541796192309550353611 / 25000000000000000000000000000000), (670699407 / 50000000000000000000000000000000)⟩ ⟨(-30241179610223140974066025271459 / 6250000000000000000000000000000), (10587911873 / 6250000000000000000000000000000)⟩ ⟨-7, 791822085718177342495688877343, 781250000000000000000000000000⟩,
   .log ⟨(51357827334459029339937650851 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(97247434120707804012571941123 / 25000000000000000000000000000000), (5220213 / 4000000000000000000000000000000)⟩ ⟨(-189352702729032115077831268942829 / 25000000000000000000000000000000), (127054943071 / 50000000000000000000000000000000)⟩ ⟨-11, 51357827334459029339937650851, 48828125000000000000000000000⟩,
   .log ⟨(266674382470302839354079003 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(6105967605224781648922340161 / 50000000000000000000000000000000), (4065889 / 100000000000000000000000000000000)⟩ ⟨(-1144835800998760933257542476011351 / 100000000000000000000000000000000), (381164920041 / 100000000000000000000000000000000)⟩ ⟨-17, 266674382470302839354079003, 190734863281250000000000000⟩,
   .log ⟨(181450604106123642236082066657 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(2039067429394094057333460199957 / 100000000000000000000000000000000), (384236607 / 50000000000000000000000000000000)⟩ ⟨(-561879482143118166329838591190561 / 100000000000000000000000000000000), (211758237381 / 100000000000000000000000000000000)⟩ ⟨-9, 181450604106123642236082066657, 97656250000000000000000000000⟩,
   .log ⟨(13932558651992671363474219161 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(123702966911870126753310137091 / 100000000000000000000000000000000), (41304687 / 100000000000000000000000000000000)⟩ ⟨(-22196742536981497197388235948923 / 2500000000000000000000000000000), (296461538739 / 100000000000000000000000000000000)⟩ ⟨-13, 13932558651992671363474219161, 12207031250000000000000000000⟩,
   .log ⟨(11518310933089731091894286224663 / 100000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩ ⟨(12446872019458289123324161673441 / 50000000000000000000000000000000), (2439097243 / 20000000000000000000000000000000)⟩ ⟨(-216123216186168296459960009943243 / 100000000000000000000000000000000), (21175823761 / 20000000000000000000000000000000)⟩ ⟨-4, 11518310933089731091894286224663, 6250000000000000000000000000000⟩,
   .log ⟨(783795781330155054539950519379 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(380045092707268734121915779943 / 10000000000000000000000000000000), (663900863 / 50000000000000000000000000000000)⟩ ⟨(-19395107846194640943222960864133 / 4000000000000000000000000000000), (169406589973 / 100000000000000000000000000000000)⟩ ⟨-7, 783795781330155054539950519379, 781250000000000000000000000000⟩,
   .log ⟨(21081710312044096845027453533 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(32766764457907768728959956557 / 10000000000000000000000000000000), (116069881 / 100000000000000000000000000000000)⟩ ⟨(-777137242968089175776914164213739 / 100000000000000000000000000000000), (1101142841 / 400000000000000000000000000000)⟩ ⟨-12, 21081710312044096845027453533, 12207031250000000000000000000⟩]
def CA1_5_10I2PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 5, 5, 2, 0 => 1
  | 5, 5, 3, 0 => 2
  | 5, 5, 1, 1 => 3
  | 5, 5, 0, 2 => 1
  | 5, 5, 0, 3 => 2
  | 4, 5, 4, 0 => 4
  | 4, 5, 2, 1 => 5
  | 4, 5, 3, 1 => 6
  | 4, 5, 1, 2 => 5
  | 4, 5, 1, 3 => 6
  | 4, 5, 0, 4 => 4
  | 5, 4, 4, 0 => 4
  | 5, 4, 2, 1 => 5
  | 5, 4, 3, 1 => 6
  | 5, 4, 1, 2 => 5
  | 5, 4, 1, 3 => 6
  | 5, 4, 0, 4 => 4
  | 2, 5, 5, 0 => 7
  | 2, 5, 4, 1 => 8
  | 2, 5, 2, 2 => 9
  | 2, 5, 2, 3 => 10
  | 2, 5, 3, 2 => 10
  | 2, 5, 3, 3 => 11
  | 2, 5, 1, 4 => 8
  | 2, 5, 0, 5 => 7
  | 3, 5, 5, 0 => 12
  | 3, 5, 4, 1 => 13
  | 3, 5, 2, 2 => 14
  | 3, 5, 2, 3 => 15
  | 3, 5, 3, 2 => 15
  | 3, 5, 3, 3 => 16
  | 3, 5, 1, 4 => 13
  | 3, 5, 0, 5 => 12
  | 4, 4, 5, 0 => 17
  | 4, 4, 4, 1 => 18
  | 4, 4, 2, 2 => 19
  | 4, 4, 2, 3 => 20
  | 4, 4, 3, 2 => 20
  | 4, 4, 3, 3 => 21
  | 4, 4, 1, 4 => 18
  | 4, 4, 0, 5 => 17
  | 5, 2, 5, 0 => 7
  | 5, 2, 4, 1 => 8
  | 5, 2, 2, 2 => 9
  | 5, 2, 2, 3 => 10
  | 5, 2, 3, 2 => 10
  | 5, 2, 3, 3 => 11
  | 5, 2, 1, 4 => 8
  | 5, 2, 0, 5 => 7
  | 5, 3, 5, 0 => 12
  | 5, 3, 4, 1 => 13
  | 5, 3, 2, 2 => 14
  | 5, 3, 2, 3 => 15
  | 5, 3, 3, 2 => 15
  | 5, 3, 3, 3 => 16
  | 5, 3, 1, 4 => 13
  | 5, 3, 0, 5 => 12
  | 1, 5, 5, 1 => 22
  | 1, 5, 4, 2 => 23
  | 1, 5, 4, 3 => 24
  | 1, 5, 2, 4 => 23
  | 1, 5, 3, 4 => 24
  | 1, 5, 1, 5 => 22
  | 2, 4, 5, 1 => 23
  | 2, 4, 4, 2 => 25
  | 2, 4, 4, 3 => 26
  | 2, 4, 2, 4 => 25
  | 2, 4, 3, 4 => 26
  | 2, 4, 1, 5 => 23
  | 3, 4, 5, 1 => 24
  | 3, 4, 4, 2 => 26
  | 3, 4, 4, 3 => 27
  | 3, 4, 2, 4 => 26
  | 3, 4, 3, 4 => 27
  | 3, 4, 1, 5 => 24
  | 4, 2, 5, 1 => 23
  | 4, 2, 4, 2 => 25
  | 4, 2, 4, 3 => 26
  | 4, 2, 2, 4 => 25
  | 4, 2, 3, 4 => 26
  | 4, 2, 1, 5 => 23
  | 4, 3, 5, 1 => 24
  | 4, 3, 4, 2 => 26
  | 4, 3, 4, 3 => 27
  | 4, 3, 2, 4 => 26
  | 4, 3, 3, 4 => 27
  | 4, 3, 1, 5 => 24
  | 5, 1, 5, 1 => 22
  | 5, 1, 4, 2 => 23
  | 5, 1, 4, 3 => 24
  | 5, 1, 2, 4 => 23
  | 5, 1, 3, 4 => 24
  | 5, 1, 1, 5 => 22
  | 5, 0, 5, 2 => 7
  | 5, 0, 5, 3 => 12
  | 5, 0, 4, 4 => 17
  | 5, 0, 2, 5 => 7
  | 5, 0, 3, 5 => 12
  | 4, 1, 5, 2 => 8
  | 4, 1, 5, 3 => 13
  | 4, 1, 4, 4 => 18
  | 4, 1, 2, 5 => 8
  | 4, 1, 3, 5 => 13
  | 2, 2, 5, 2 => 9
  | 2, 2, 5, 3 => 14
  | 2, 2, 4, 4 => 19
  | 2, 2, 2, 5 => 9
  | 2, 2, 3, 5 => 14
  | 2, 3, 5, 2 => 10
  | 2, 3, 5, 3 => 15
  | 2, 3, 4, 4 => 20
  | 2, 3, 2, 5 => 10
  | 2, 3, 3, 5 => 15
  | 3, 2, 5, 2 => 10
  | 3, 2, 5, 3 => 15
  | 3, 2, 4, 4 => 20
  | 3, 2, 2, 5 => 10
  | 3, 2, 3, 5 => 15
  | 3, 3, 5, 2 => 11
  | 3, 3, 5, 3 => 16
  | 3, 3, 4, 4 => 21
  | 3, 3, 2, 5 => 11
  | 3, 3, 3, 5 => 16
  | 1, 4, 5, 2 => 8
  | 1, 4, 5, 3 => 13
  | 1, 4, 4, 4 => 18
  | 1, 4, 2, 5 => 8
  | 1, 4, 3, 5 => 13
  | 0, 5, 5, 2 => 7
  | 0, 5, 5, 3 => 12
  | 0, 5, 4, 4 => 17
  | 0, 5, 2, 5 => 7
  | 0, 5, 3, 5 => 12
  | 4, 0, 4, 5 => 4
  | 4, 0, 5, 4 => 4
  | 2, 1, 4, 5 => 5
  | 2, 1, 5, 4 => 5
  | 3, 1, 4, 5 => 6
  | 3, 1, 5, 4 => 6
  | 1, 2, 4, 5 => 5
  | 1, 2, 5, 4 => 5
  | 1, 3, 4, 5 => 6
  | 1, 3, 5, 4 => 6
  | 0, 4, 4, 5 => 4
  | 0, 4, 5, 4 => 4
  | 2, 0, 5, 5 => 1
  | 3, 0, 5, 5 => 2
  | 1, 1, 5, 5 => 3
  | 0, 2, 5, 5 => 1
  | 0, 3, 5, 5 => 2
  | _, _, _, _ => 0
def CA1_5_10I2PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2PairCertificates (CA1_5_10I2PairCertificateIndex a)).input
def CA1_5_10I2PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2PairCertificates (CA1_5_10I2PairCertificateIndex a)).output

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
def CA1_5_10I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA1_5_10I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA1_5_10I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R0Certificates (CA1_5_10I2R0CertificateIndex a)).input
def CA1_5_10I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R0Certificates (CA1_5_10I2R0CertificateIndex a)).output
def CA1_5_10I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA1_5_10I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA1_5_10I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R1Certificates (CA1_5_10I2R1CertificateIndex a)).input
def CA1_5_10I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R1Certificates (CA1_5_10I2R1CertificateIndex a)).output
def CA1_5_10I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA1_5_10I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA1_5_10I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_5_10I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R2Certificates (CA1_5_10I2R2CertificateIndex a)).input
def CA1_5_10I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R2Certificates (CA1_5_10I2R2CertificateIndex a)).output
def CA1_5_10I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA1_5_10I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA1_5_10I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_5_10I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R3Certificates (CA1_5_10I2R3CertificateIndex a)).input
def CA1_5_10I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R3Certificates (CA1_5_10I2R3CertificateIndex a)).output
def CA1_5_10I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA1_5_10I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA1_5_10I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(632871159398230728670782241 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(13396767985006072636062921341 / 50000000000000000000000000000000), (9113079 / 100000000000000000000000000000000)⟩ ⟨(-105841195210605492117564918365433 / 10000000000000000000000000000000), (359989042113 / 100000000000000000000000000000000)⟩ ⟨-16, 632871159398230728670782241, 381469726562500000000000000⟩,
   .log ⟨(20058892686705406523311807527 / 2000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(1153945440678932638698219878697 / 25000000000000000000000000000000), (212381791 / 12500000000000000000000000000000)⟩ ⟨(-115055746964910214632716111832649 / 25000000000000000000000000000000), (84703294981 / 50000000000000000000000000000000)⟩ ⟨-7, 20058892686705406523311807527, 15625000000000000000000000000⟩,
   .log ⟨(1065807453028293525913333569141 / 10000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩ ⟨(5965463960001714492232909133471 / 25000000000000000000000000000000), (5642337719 / 50000000000000000000000000000000)⟩ ⟨(-223885240924219805416967771004573 / 100000000000000000000000000000000), (105879118659 / 100000000000000000000000000000000)⟩ ⟨-4, 1065807453028293525913333569141, 625000000000000000000000000000⟩,
   .log ⟨(3453880792944542478296706953 / 625000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(359082936537564572837174392869 / 12500000000000000000000000000000), (1053198311 / 100000000000000000000000000000000)⟩ ⟨(-6497816479203003750205809534597 / 1250000000000000000000000000000), (190582413509 / 100000000000000000000000000000000)⟩ ⟨-8, 3453880792944542478296706953, 2441406250000000000000000000⟩,
   .log ⟨(1316827912981976963120678709 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(3699529166154410349622448903 / 25000000000000000000000000000000), (2509649 / 50000000000000000000000000000000)⟩ ⟨(-224753994333353395052494386894243 / 20000000000000000000000000000000), (190582451117 / 50000000000000000000000000000000)⟩ ⟨-17, 1316827912981976963120678709, 762939453125000000000000000⟩]
def CA1_5_10I2R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 0 => 1
  | 4, 1 => 2
  | 2, 2 => 3
  | 2, 3 => 4
  | 3, 2 => 4
  | 3, 3 => 5
  | 1, 4 => 2
  | 0, 5 => 1
  | _, _ => 0
def CA1_5_10I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R4Certificates (CA1_5_10I2R4CertificateIndex a)).input
def CA1_5_10I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R4Certificates (CA1_5_10I2R4CertificateIndex a)).output
def CA1_5_10I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA1_5_10I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA1_5_10I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1258098169685637449695465587 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(171317453113904513126502808813 / 100000000000000000000000000000000), (14919111 / 25000000000000000000000000000000)⟩ ⟨(-851073555118078631593835392303337 / 100000000000000000000000000000000), (29646153653 / 10000000000000000000000000000000)⟩ ⟨-13, 1258098169685637449695465587, 762939453125000000000000000⟩,
   .log ⟨(6684646318168966297530337967463 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩ ⟨(13450910182909538526533189477777 / 50000000000000000000000000000000), (11324231421 / 100000000000000000000000000000000)⟩ ⟨(-50305242576371498699063217216007 / 25000000000000000000000000000000), (42351647459 / 50000000000000000000000000000000)⟩ ⟨-3, 6684646318168966297530337967463, 6250000000000000000000000000000⟩,
   .log ⟨(493377940579587723437131807133 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(524130184741895029846388666731 / 20000000000000000000000000000000), (470145799 / 50000000000000000000000000000000)⟩ ⟨(-531164997087406874113207080480883 / 100000000000000000000000000000000), (11911400847 / 6250000000000000000000000000000)⟩ ⟨-8, 493377940579587723437131807133, 390625000000000000000000000000⟩]
def CA1_5_10I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA1_5_10I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R5Certificates (CA1_5_10I2R5CertificateIndex a)).input
def CA1_5_10I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R5Certificates (CA1_5_10I2R5CertificateIndex a)).output
def CA1_5_10I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA1_5_10I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA1_5_10I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(35687513078880597433602857623 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(103422090723016740293707659229 / 20000000000000000000000000000000), (36274201 / 20000000000000000000000000000000)⟩ ⟨(-362248871525530095950681596372239 / 50000000000000000000000000000000), (63527471399 / 25000000000000000000000000000000)⟩ ⟨-11, 35687513078880597433602857623, 24414062500000000000000000000⟩,
   .log ⟨(2248454976633005517664593 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(7607553095292825842435907 / 10000000000000000000000000000000), (12389 / 50000000000000000000000000000000)⟩ ⟨(-845864513004937999114364798625629 / 50000000000000000000000000000000), (2202374613 / 400000000000000000000000000000)⟩ ⟨-25, 2248454976633005517664593, 1490116119384765625000000⟩,
   .log ⟨(3742132954163165391913878812327 / 50000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩ ⟨(19401965815814233651433897567907 / 100000000000000000000000000000000), (3962137431 / 50000000000000000000000000000000)⟩ ⟨(-64809181199151831416449059873581 / 25000000000000000000000000000000), (4235164751 / 4000000000000000000000000000000)⟩ ⟨-4, 3742132954163165391913878812327, 3125000000000000000000000000000⟩]
def CA1_5_10I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA1_5_10I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R6Certificates (CA1_5_10I2R6CertificateIndex a)).input
def CA1_5_10I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R6Certificates (CA1_5_10I2R6CertificateIndex a)).output
def CA1_5_10I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA1_5_10I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA1_5_10I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R7Certificates (CA1_5_10I2R7CertificateIndex a)).input
def CA1_5_10I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R7Certificates (CA1_5_10I2R7CertificateIndex a)).output
def CA1_5_10I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA1_5_10I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA1_5_10I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R8Certificates (CA1_5_10I2R8CertificateIndex a)).input
def CA1_5_10I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R8Certificates (CA1_5_10I2R8CertificateIndex a)).output
def CA1_5_10I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA1_5_10I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA1_5_10I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R9Certificates (CA1_5_10I2R9CertificateIndex a)).input
def CA1_5_10I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R9Certificates (CA1_5_10I2R9CertificateIndex a)).output
def CA1_5_10I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA1_5_10I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA1_5_10I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R10Certificates (CA1_5_10I2R10CertificateIndex a)).input
def CA1_5_10I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R10Certificates (CA1_5_10I2R10CertificateIndex a)).output
def CA1_5_10I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA1_5_10I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA1_5_10I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R11Certificates (CA1_5_10I2R11CertificateIndex a)).input
def CA1_5_10I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R11Certificates (CA1_5_10I2R11CertificateIndex a)).output
def CA1_5_10I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA1_5_10I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA1_5_10I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R12Certificates (CA1_5_10I2R12CertificateIndex a)).input
def CA1_5_10I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R12Certificates (CA1_5_10I2R12CertificateIndex a)).output
def CA1_5_10I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA1_5_10I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA1_5_10I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R13Certificates (CA1_5_10I2R13CertificateIndex a)).input
def CA1_5_10I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R13Certificates (CA1_5_10I2R13CertificateIndex a)).output
def CA1_5_10I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA1_5_10I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA1_5_10I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R14Certificates (CA1_5_10I2R14CertificateIndex a)).input
def CA1_5_10I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R14Certificates (CA1_5_10I2R14CertificateIndex a)).output
def CA1_5_10I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA1_5_10I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA1_5_10I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R15Certificates (CA1_5_10I2R15CertificateIndex a)).input
def CA1_5_10I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R15Certificates (CA1_5_10I2R15CertificateIndex a)).output
def CA1_5_10I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA1_5_10I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
def CA1_5_10I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R16Certificates (CA1_5_10I2R16CertificateIndex a)).input
def CA1_5_10I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I2R16Certificates (CA1_5_10I2R16CertificateIndex a)).output
def CA1_5_10I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_5_10I2R0H
  | 1 => CA1_5_10I2R1H
  | 2 => CA1_5_10I2R2H
  | 3 => CA1_5_10I2R3H
  | 4 => CA1_5_10I2R4H
  | 5 => CA1_5_10I2R5H
  | 6 => CA1_5_10I2R6H
  | 7 => CA1_5_10I2R7H
  | 8 => CA1_5_10I2R8H
  | 9 => CA1_5_10I2R9H
  | 10 => CA1_5_10I2R10H
  | 11 => CA1_5_10I2R11H
  | 12 => CA1_5_10I2R12H
  | 13 => CA1_5_10I2R13H
  | 14 => CA1_5_10I2R14H
  | 15 => CA1_5_10I2R15H
  | 16 => CA1_5_10I2R16H
  | _ => (.exact 0)
def CA1_5_10I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 0, 5, 3 => Z0_5_3H2H
  | 1, 0, 7 => Z1_0_7H2H
  | _, _, _ => (.exact 0)

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
def CA1_6_9I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 1 6 9)) A1_6_9Law ((Equiv.refl (Fin 3)) 0) a
def CA1_6_9I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (37 / 50000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (330872247 / 1562500000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647513 / 100000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
def CA1_6_9I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I0Certificates (CA1_6_9I0CertificateIndex a)).input
def CA1_6_9I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I0Certificates (CA1_6_9I0CertificateIndex a)).output

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
def CA1_6_9I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 6 9)) (shape 1 6 9) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA1_6_9I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 6 9) A1_6_9Law 1 a
def CA1_6_9I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(441876206744648671114472127 / 4000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(100645869110909624952901605809 / 100000000000000000000000000000000), (17544559 / 50000000000000000000000000000000)⟩ ⟨(-911077515147321236108554608474889 / 100000000000000000000000000000000), (317637373349 / 100000000000000000000000000000000)⟩ ⟨-14, 441876206744648671114472127, 244140625000000000000000000⟩,
   .log ⟨(657080921971796282931564339 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(27719823945490765311282689673 / 100000000000000000000000000000000), (9461689 / 100000000000000000000000000000000)⟩ ⟨(-131832240037821096251951760685329 / 12500000000000000000000000000000), (179994520329 / 50000000000000000000000000000000)⟩ ⟨-16, 657080921971796282931564339, 381469726562500000000000000⟩,
   .log ⟨(94111745008810675585318067 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1240679906901828064584075781 / 50000000000000000000000000000000), (83703 / 10000000000000000000000000000000)⟩ ⟨(-1318305071046845939950790763193751 / 100000000000000000000000000000000), (222346414313 / 50000000000000000000000000000000)⟩ ⟨-20, 94111745008810675585318067, 47683715820312500000000000⟩,
   .log ⟨(31036799123995126073588775049 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1792426919717737345491904986727 / 100000000000000000000000000000000), (657229807 / 100000000000000000000000000000000)⟩ ⟨(-577516680298381281900907376060233 / 100000000000000000000000000000000), (52939559449 / 25000000000000000000000000000000)⟩ ⟨-9, 31036799123995126073588775049, 19531250000000000000000000000⟩,
   .log ⟨(2778136476605944221571551103 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(227489372302179854034600281019 / 100000000000000000000000000000000), (76478137 / 100000000000000000000000000000000)⟩ ⟨(-40942800006014130005143854813759 / 5000000000000000000000000000000), (137642855739 / 50000000000000000000000000000000)⟩ ⟨-12, 2778136476605944221571551103, 2441406250000000000000000000⟩,
   .log ⟨(18501565179107019817172619 / 125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(65260302091448506302700432411 / 50000000000000000000000000000000), (4388003 / 10000000000000000000000000000000)⟩ ⟨(-881821368350284382934873207105127 / 100000000000000000000000000000000), (296461538317 / 100000000000000000000000000000000)⟩ ⟨-13, 18501565179107019817172619, 15258789062500000000000000⟩,
   .log ⟨(87909239679064740202376269349 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2385497496339457151402690193659 / 100000000000000000000000000000000), (209424443 / 25000000000000000000000000000000)⟩ ⟨(-542718263756649130440773595054797 / 100000000000000000000000000000000), (190582413829 / 100000000000000000000000000000000)⟩ ⟨-8, 87909239679064740202376269349, 78125000000000000000000000000⟩,
   .log ⟨(2397841103861224198183981936807 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩ ⟨(894538936350652942746544141601 / 10000000000000000000000000000000), (1777169149 / 50000000000000000000000000000000)⟩ ⟨(-373060139352096394253289417342207 / 100000000000000000000000000000000), (37057691591 / 25000000000000000000000000000000)⟩ ⟨-6, 2397841103861224198183981936807, 1562500000000000000000000000000⟩,
   .log ⟨(55084917588553862649425208577 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1347984153750061927306891099159 / 100000000000000000000000000000000), (58323427 / 12500000000000000000000000000000)⟩ ⟨(-19117984853553869366385232630869 / 3125000000000000000000000000000), (211758237737 / 100000000000000000000000000000000)⟩ ⟨-9, 55084917588553862649425208577, 48828125000000000000000000000⟩,
   .log ⟨(20759577999412165650052381717 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(176039513637130230288747536003 / 100000000000000000000000000000000), (61544173 / 100000000000000000000000000000000)⟩ ⟨(-423995886723022542215919261641731 / 50000000000000000000000000000000), (296461536379 / 100000000000000000000000000000000)⟩ ⟨-13, 20759577999412165650052381717, 12207031250000000000000000000⟩,
   .log ⟨(5941887119991255639030945031 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(57819901562831230535228103283 / 100000000000000000000000000000000), (5032977 / 25000000000000000000000000000000)⟩ ⟨(-243272467127061145794215990352467 / 25000000000000000000000000000000), (338813195757 / 100000000000000000000000000000000)⟩ ⟨-15, 5941887119991255639030945031, 3051757812500000000000000000⟩,
   .log ⟨(22978040129733690400522318527 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(353183474154743719903286073019 / 100000000000000000000000000000000), (12651053 / 10000000000000000000000000000000)⟩ ⟨(-768523930153909575193722362133089 / 100000000000000000000000000000000), (55057142011 / 20000000000000000000000000000000)⟩ ⟨-12, 22978040129733690400522318527, 12207031250000000000000000000⟩,
   .log ⟨(7638517967839454208914260439 / 3125000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(735007037152254525790532510527 / 50000000000000000000000000000000), (258803063 / 50000000000000000000000000000000)⟩ ⟨(-601398596107634736869781960612483 / 100000000000000000000000000000000), (211758237647 / 100000000000000000000000000000000)⟩ ⟨-9, 7638517967839454208914260439, 6103515625000000000000000000⟩,
   .log ⟨(11500982753340549434368253601 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(96347709517186786552843229153 / 50000000000000000000000000000000), (68191989 / 100000000000000000000000000000000)⟩ ⟨(-837734579588008240364578866892303 / 100000000000000000000000000000000), (296461535909 / 100000000000000000000000000000000)⟩ ⟨-13, 11500982753340549434368253601, 6103515625000000000000000000⟩,
   .log ⟨(2236384514690918206764343199 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(23947350656693576188507800821 / 100000000000000000000000000000000), (8050751 / 100000000000000000000000000000000)⟩ ⟨(-214161299180729161041706543576697 / 20000000000000000000000000000000), (14399561893 / 4000000000000000000000000000000)⟩ ⟨-16, 2236384514690918206764343199, 1525878906250000000000000000⟩,
   .log ⟨(635086863187962003560534443 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(190000825639915592944604079 / 2500000000000000000000000000000), (1277613 / 50000000000000000000000000000000)⟩ ⟨(-29917297404982291584739580036251 / 2500000000000000000000000000000), (80468161487 / 20000000000000000000000000000000)⟩ ⟨-18, 635086863187962003560534443, 381469726562500000000000000⟩,
   .log ⟨(1645550759964372303342956763939 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩ ⟨(6758433379650538845905004137789 / 100000000000000000000000000000000), (1219606267 / 50000000000000000000000000000000)⟩ ⟨(-410709504931763100547790863935819 / 100000000000000000000000000000000), (148230766267 / 100000000000000000000000000000000)⟩ ⟨-6, 1645550759964372303342956763939, 1562500000000000000000000000000⟩,
   .log ⟨(4391498038472609372528693892929 / 50000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩ ⟨(10681671661751321671614349256369 / 50000000000000000000000000000000), (1859871789 / 20000000000000000000000000000000)⟩ ⟨(-12161762988588825866894782910377 / 5000000000000000000000000000000), (26469779709 / 25000000000000000000000000000000)⟩ ⟨-4, 4391498038472609372528693892929, 3125000000000000000000000000000⟩,
   .log ⟨(823804361764859503861595460401 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(988357715388072645073744957439 / 25000000000000000000000000000000), (1395578897 / 100000000000000000000000000000000)⟩ ⟨(-119974809707329761366408847648449 / 25000000000000000000000000000000), (169406589949 / 100000000000000000000000000000000)⟩ ⟨-7, 823804361764859503861595460401, 781250000000000000000000000000⟩,
   .log ⟨(39878384659993184498745180899 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(568980313599541517712456220437 / 100000000000000000000000000000000), (202669843 / 100000000000000000000000000000000)⟩ ⟨(-713394384515221184637262973130497 / 100000000000000000000000000000000), (254109885449 / 100000000000000000000000000000000)⟩ ⟨-11, 39878384659993184498745180899, 24414062500000000000000000000⟩,
   .log ⟨(5668259952116994413712018063 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(9513322866248222045037957383 / 5000000000000000000000000000000), (67216851 / 100000000000000000000000000000000)⟩ ⟨(-104896861499523819122737507663813 / 12500000000000000000000000000000), (74115383993 / 25000000000000000000000000000000)⟩ ⟨-13, 5668259952116994413712018063, 3051757812500000000000000000⟩,
   .log ⟨(2325734267941421170719201531 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(159814190682024003393280260257 / 100000000000000000000000000000000), (5515927 / 10000000000000000000000000000000)⟩ ⟨(-429472405997075849922385931581039 / 50000000000000000000000000000000), (37057692117 / 12500000000000000000000000000000)⟩ ⟨-13, 2325734267941421170719201531, 1525878906250000000000000000⟩,
   .log ⟨(462798965777906867780188403881 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2487837255979488470899503004741 / 100000000000000000000000000000000), (882013457 / 100000000000000000000000000000000)⟩ ⟨(-107512654087190833346588335835551 / 20000000000000000000000000000000), (95291206897 / 50000000000000000000000000000000)⟩ ⟨-8, 462798965777906867780188403881, 390625000000000000000000000000⟩,
   .log ⟨(44589878690847598995753768469 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(68805915589264588615596475629 / 20000000000000000000000000000000), (122749573 / 100000000000000000000000000000000)⟩ ⟨(-385770928344034212093159577348853 / 50000000000000000000000000000000), (137642855061 / 50000000000000000000000000000000)⟩ ⟨-12, 44589878690847598995753768469, 24414062500000000000000000000⟩,
   .log ⟨(10130496501763004045361752623573 / 100000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩ ⟨(2899373242597345393296920604419 / 12500000000000000000000000000000), (670380031 / 6250000000000000000000000000000)⟩ ⟨(-228961985592139082996034395848633 / 100000000000000000000000000000000), (5293955937 / 5000000000000000000000000000000)⟩ ⟨-4, 10130496501763004045361752623573, 6250000000000000000000000000000⟩,
   .log ⟨(122933322718074998557527270291 / 12500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(2272713481463272385856994160607 / 50000000000000000000000000000000), (833028609 / 50000000000000000000000000000000)⟩ ⟨(-18487367226503129813357539367781 / 4000000000000000000000000000000), (16940658987 / 10000000000000000000000000000000)⟩ ⟨-7, 122933322718074998557527270291, 97656250000000000000000000000⟩,
   .log ⟨(1908591051834485317217172211 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(132733673911115935362865028459 / 20000000000000000000000000000000), (121247967 / 50000000000000000000000000000000)⟩ ⟨(-347726857944597330849319412249363 / 50000000000000000000000000000000), (254109885243 / 100000000000000000000000000000000)⟩ ⟨-11, 1908591051834485317217172211, 976562500000000000000000000⟩]
def CA1_6_9I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 4, 4 => 1
  | 0, 0, 5, 2 => 2
  | 0, 0, 5, 3 => 3
  | 0, 0, 2, 5 => 2
  | 0, 0, 3, 5 => 3
  | 1, 0, 2, 4 => 4
  | 1, 0, 3, 4 => 5
  | 1, 0, 4, 2 => 4
  | 1, 0, 4, 3 => 5
  | 1, 0, 5, 1 => 6
  | 1, 0, 1, 5 => 6
  | 0, 1, 2, 4 => 4
  | 0, 1, 3, 4 => 5
  | 0, 1, 4, 2 => 4
  | 0, 1, 4, 3 => 5
  | 0, 1, 5, 1 => 6
  | 0, 1, 1, 5 => 6
  | 2, 0, 1, 4 => 7
  | 2, 0, 2, 2 => 8
  | 2, 0, 2, 3 => 9
  | 2, 0, 3, 2 => 9
  | 2, 0, 3, 3 => 10
  | 2, 0, 4, 1 => 7
  | 2, 0, 5, 0 => 11
  | 2, 0, 0, 5 => 11
  | 3, 0, 1, 4 => 12
  | 3, 0, 2, 2 => 13
  | 3, 0, 2, 3 => 14
  | 3, 0, 3, 2 => 14
  | 3, 0, 3, 3 => 15
  | 3, 0, 4, 1 => 12
  | 3, 0, 5, 0 => 16
  | 3, 0, 0, 5 => 16
  | 1, 1, 1, 4 => 17
  | 1, 1, 2, 2 => 18
  | 1, 1, 2, 3 => 19
  | 1, 1, 3, 2 => 19
  | 1, 1, 3, 3 => 20
  | 1, 1, 4, 1 => 17
  | 1, 1, 5, 0 => 21
  | 1, 1, 0, 5 => 21
  | 0, 2, 1, 4 => 7
  | 0, 2, 2, 2 => 8
  | 0, 2, 2, 3 => 9
  | 0, 2, 3, 2 => 9
  | 0, 2, 3, 3 => 10
  | 0, 2, 4, 1 => 7
  | 0, 2, 5, 0 => 11
  | 0, 2, 0, 5 => 11
  | 0, 3, 1, 4 => 12
  | 0, 3, 2, 2 => 13
  | 0, 3, 2, 3 => 14
  | 0, 3, 3, 2 => 14
  | 0, 3, 3, 3 => 15
  | 0, 3, 4, 1 => 12
  | 0, 3, 5, 0 => 16
  | 0, 3, 0, 5 => 16
  | 4, 0, 0, 4 => 22
  | 4, 0, 1, 2 => 23
  | 4, 0, 1, 3 => 24
  | 4, 0, 2, 1 => 23
  | 4, 0, 3, 1 => 24
  | 4, 0, 4, 0 => 22
  | 2, 1, 0, 4 => 23
  | 2, 1, 1, 2 => 25
  | 2, 1, 1, 3 => 26
  | 2, 1, 2, 1 => 25
  | 2, 1, 3, 1 => 26
  | 2, 1, 4, 0 => 23
  | 3, 1, 0, 4 => 24
  | 3, 1, 1, 2 => 26
  | 3, 1, 1, 3 => 27
  | 3, 1, 2, 1 => 26
  | 3, 1, 3, 1 => 27
  | 3, 1, 4, 0 => 24
  | 1, 2, 0, 4 => 23
  | 1, 2, 1, 2 => 25
  | 1, 2, 1, 3 => 26
  | 1, 2, 2, 1 => 25
  | 1, 2, 3, 1 => 26
  | 1, 2, 4, 0 => 23
  | 1, 3, 0, 4 => 24
  | 1, 3, 1, 2 => 26
  | 1, 3, 1, 3 => 27
  | 1, 3, 2, 1 => 26
  | 1, 3, 3, 1 => 27
  | 1, 3, 4, 0 => 24
  | 0, 4, 0, 4 => 22
  | 0, 4, 1, 2 => 23
  | 0, 4, 1, 3 => 24
  | 0, 4, 2, 1 => 23
  | 0, 4, 3, 1 => 24
  | 0, 4, 4, 0 => 22
  | 0, 5, 0, 2 => 11
  | 0, 5, 0, 3 => 16
  | 0, 5, 1, 1 => 21
  | 0, 5, 2, 0 => 11
  | 0, 5, 3, 0 => 16
  | 1, 4, 0, 2 => 7
  | 1, 4, 0, 3 => 12
  | 1, 4, 1, 1 => 17
  | 1, 4, 2, 0 => 7
  | 1, 4, 3, 0 => 12
  | 2, 2, 0, 2 => 8
  | 2, 2, 0, 3 => 13
  | 2, 2, 1, 1 => 18
  | 2, 2, 2, 0 => 8
  | 2, 2, 3, 0 => 13
  | 2, 3, 0, 2 => 9
  | 2, 3, 0, 3 => 14
  | 2, 3, 1, 1 => 19
  | 2, 3, 2, 0 => 9
  | 2, 3, 3, 0 => 14
  | 3, 2, 0, 2 => 9
  | 3, 2, 0, 3 => 14
  | 3, 2, 1, 1 => 19
  | 3, 2, 2, 0 => 9
  | 3, 2, 3, 0 => 14
  | 3, 3, 0, 2 => 10
  | 3, 3, 0, 3 => 15
  | 3, 3, 1, 1 => 20
  | 3, 3, 2, 0 => 10
  | 3, 3, 3, 0 => 15
  | 4, 1, 0, 2 => 7
  | 4, 1, 0, 3 => 12
  | 4, 1, 1, 1 => 17
  | 4, 1, 2, 0 => 7
  | 4, 1, 3, 0 => 12
  | 5, 0, 0, 2 => 11
  | 5, 0, 0, 3 => 16
  | 5, 0, 1, 1 => 21
  | 5, 0, 2, 0 => 11
  | 5, 0, 3, 0 => 16
  | 1, 5, 0, 1 => 6
  | 1, 5, 1, 0 => 6
  | 2, 4, 0, 1 => 4
  | 2, 4, 1, 0 => 4
  | 3, 4, 0, 1 => 5
  | 3, 4, 1, 0 => 5
  | 4, 2, 0, 1 => 4
  | 4, 2, 1, 0 => 4
  | 4, 3, 0, 1 => 5
  | 4, 3, 1, 0 => 5
  | 5, 1, 0, 1 => 6
  | 5, 1, 1, 0 => 6
  | 2, 5, 0, 0 => 2
  | 3, 5, 0, 0 => 3
  | 4, 4, 0, 0 => 1
  | 5, 2, 0, 0 => 2
  | 5, 3, 0, 0 => 3
  | _, _, _, _ => 0
def CA1_6_9I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1PairCertificates (CA1_6_9I1PairCertificateIndex a)).input
def CA1_6_9I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1PairCertificates (CA1_6_9I1PairCertificateIndex a)).output

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
def CA1_6_9I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA1_6_9I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA1_6_9I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(8339999762212914871827795077 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1450945636735909530787380563 / 1000000000000000000000000000000), (24724901 / 50000000000000000000000000000000)⟩ ⟨(-54366969353445431436392639182027 / 6250000000000000000000000000000), (2316105809 / 781250000000000000000000000000)⟩ ⟨-13, 8339999762212914871827795077, 6103515625000000000000000000⟩]
def CA1_6_9I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA1_6_9I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R0Certificates (CA1_6_9I1R0CertificateIndex a)).input
def CA1_6_9I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R0Certificates (CA1_6_9I1R0CertificateIndex a)).output
def CA1_6_9I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA1_6_9I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA1_6_9I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(352950608149296318805341356721 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(3496646491070427809635638237251 / 100000000000000000000000000000000), (1345323603 / 100000000000000000000000000000000)⟩ ⟨(-247672507876184481726943786438277 / 50000000000000000000000000000000), (38116482771 / 20000000000000000000000000000000)⟩ ⟨-8, 352950608149296318805341356721, 195312500000000000000000000000⟩]
def CA1_6_9I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA1_6_9I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R1Certificates (CA1_6_9I1R1CertificateIndex a)).input
def CA1_6_9I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R1Certificates (CA1_6_9I1R1CertificateIndex a)).output
def CA1_6_9I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA1_6_9I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA1_6_9I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3750256193599697178331260570691 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩ ⟨(12313388784911392649224959762473 / 100000000000000000000000000000000), (952977181 / 20000000000000000000000000000000)⟩ ⟨(-328334603004610765255022211056333 / 100000000000000000000000000000000), (31763735631 / 25000000000000000000000000000000)⟩ ⟨-5, 3750256193599697178331260570691, 3125000000000000000000000000000⟩,
   .log ⟨(96463806186056584059676008661 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(428875244823396362642940222883 / 20000000000000000000000000000000), (817080241 / 100000000000000000000000000000000)⟩ ⟨(-69468290391118668442947267645409 / 12500000000000000000000000000000), (211758237607 / 100000000000000000000000000000000)⟩ ⟨-9, 96463806186056584059676008661, 48828125000000000000000000000⟩,
   .log ⟨(13846809169340604683773678740841 / 100000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩ ⟨(3422092395239441090087522368893 / 12500000000000000000000000000000), (1172870369 / 10000000000000000000000000000000)⟩ ⟨(-98855768239128658880322037043519 / 50000000000000000000000000000000), (84703294991 / 100000000000000000000000000000000)⟩ ⟨-3, 13846809169340604683773678740841, 12500000000000000000000000000000⟩]
def CA1_6_9I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_6_9I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R2Certificates (CA1_6_9I1R2CertificateIndex a)).input
def CA1_6_9I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R2Certificates (CA1_6_9I1R2CertificateIndex a)).output
def CA1_6_9I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA1_6_9I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA1_6_9I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(262997359306142918070847892299 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(2395636167101722520226825879023 / 50000000000000000000000000000000), (27845929 / 1562500000000000000000000000000)⟩ ⟨(-1821794844953613827296409995907 / 400000000000000000000000000000), (169406589939 / 100000000000000000000000000000000)⟩ ⟨-7, 262997359306142918070847892299, 195312500000000000000000000000⟩,
   .log ⟨(5788381024642755450801079594891 / 25000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩ ⟨(3387414264386620807997353345651 / 10000000000000000000000000000000), (1225737367 / 6250000000000000000000000000000)⟩ ⟨(-3657557970403826810673592756509 / 2500000000000000000000000000000), (8470329493 / 10000000000000000000000000000000)⟩ ⟨-3, 5788381024642755450801079594891, 3125000000000000000000000000000⟩,
   .log ⟨(561743006513585926658415270673 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(341143080310919619072648549763 / 4000000000000000000000000000000), (3330703861 / 100000000000000000000000000000000)⟩ ⟨(-379558664232641596305435459734451 / 100000000000000000000000000000000), (74115382979 / 50000000000000000000000000000000)⟩ ⟨-6, 561743006513585926658415270673, 390625000000000000000000000000⟩]
def CA1_6_9I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_6_9I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R3Certificates (CA1_6_9I1R3CertificateIndex a)).input
def CA1_6_9I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R3Certificates (CA1_6_9I1R3CertificateIndex a)).output
def CA1_6_9I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA1_6_9I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA1_6_9I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(35826987774826412940031031201 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(142129673252656233185977844649 / 50000000000000000000000000000000), (98626587 / 100000000000000000000000000000000)⟩ ⟨(-396711200355288234932394326306789 / 50000000000000000000000000000000), (275285710669 / 100000000000000000000000000000000)⟩ ⟨-12, 35826987774826412940031031201, 24414062500000000000000000000⟩,
   .log ⟨(163534707329622154185550545721 / 6250000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩ ⟨(9532926071727824250208934309911 / 100000000000000000000000000000000), (969635009 / 25000000000000000000000000000000)⟩ ⟨(-72866229953507402120495250057111 / 20000000000000000000000000000000), (148230766201 / 100000000000000000000000000000000)⟩ ⟨-6, 163534707329622154185550545721, 97656250000000000000000000000⟩,
   .log ⟨(879221464663087013174741520473 / 6250000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩ ⟨(3448833987306901485794990391481 / 12500000000000000000000000000000), (2978918233 / 25000000000000000000000000000000)⟩ ⟨(-39225998521640691723875329727651 / 20000000000000000000000000000000), (84703295101 / 100000000000000000000000000000000)⟩ ⟨-3, 879221464663087013174741520473, 781250000000000000000000000000⟩,
   .log ⟨(1310487633486652602794470143421 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(2840331815290867417715528693877 / 50000000000000000000000000000000), (1110026219 / 50000000000000000000000000000000)⟩ ⟨(-27092317992100651631905078306153 / 6250000000000000000000000000000), (169406589921 / 100000000000000000000000000000000)⟩ ⟨-7, 1310487633486652602794470143421, 781250000000000000000000000000⟩,
   .log ⟨(31437173587048134177780952907 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(419915132460468872428984587311 / 50000000000000000000000000000000), (73227887 / 25000000000000000000000000000000)⟩ ⟨(-166966000974031016161403637963159 / 25000000000000000000000000000000), (58233515327 / 25000000000000000000000000000000)⟩ ⟨-10, 31437173587048134177780952907, 24414062500000000000000000000⟩]
def CA1_6_9I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA1_6_9I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R4Certificates (CA1_6_9I1R4CertificateIndex a)).input
def CA1_6_9I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R4Certificates (CA1_6_9I1R4CertificateIndex a)).output
def CA1_6_9I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA1_6_9I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
def CA1_6_9I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(18501565179107019817172619 / 62500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(4810446319640869613227379209 / 2000000000000000000000000000000), (81491473 / 100000000000000000000000000000000)⟩ ⟨(-812506650294289851993150014054797 / 100000000000000000000000000000000), (34410713907 / 12500000000000000000000000000000)⟩ ⟨-12, 18501565179107019817172619, 15258789062500000000000000⟩,
   .log ⟨(620735982479902521471775500981 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(1577296221653711324887320429691 / 50000000000000000000000000000000), (591506823 / 50000000000000000000000000000000)⟩ ⟨(-254100981121193375479592091504871 / 50000000000000000000000000000000), (1488925109 / 781250000000000000000000000000)⟩ ⟨-8, 620735982479902521471775500981, 390625000000000000000000000000⟩,
   .log ⟨(55562729532118884431431022061 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(83293119056991338824175993333 / 20000000000000000000000000000000), (141190397 / 100000000000000000000000000000000)⟩ ⟨(-14990825641285761383223078064461 / 2000000000000000000000000000000), (50821977199 / 20000000000000000000000000000000)⟩ ⟨-11, 55562729532118884431431022061, 48828125000000000000000000000⟩]
def CA1_6_9I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CA1_6_9I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R5Certificates (CA1_6_9I1R5CertificateIndex a)).input
def CA1_6_9I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R5Certificates (CA1_6_9I1R5CertificateIndex a)).output
def CA1_6_9I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA1_6_9I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
def CA1_6_9I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(657080921971796282931564339 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(27719823945490765311282689673 / 100000000000000000000000000000000), (9461689 / 100000000000000000000000000000000)⟩ ⟨(-131832240037821096251951760685329 / 12500000000000000000000000000000), (179994520329 / 50000000000000000000000000000000)⟩ ⟨-16, 657080921971796282931564339, 381469726562500000000000000⟩,
   .log ⟨(94111745008810675585318067 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1240679906901828064584075781 / 50000000000000000000000000000000), (83703 / 10000000000000000000000000000000)⟩ ⟨(-1318305071046845939950790763193751 / 100000000000000000000000000000000), (222346414313 / 50000000000000000000000000000000)⟩ ⟨-20, 94111745008810675585318067, 47683715820312500000000000⟩,
   .log ⟨(441876206744648671114472127 / 4000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(100645869110909624952901605809 / 100000000000000000000000000000000), (17544559 / 50000000000000000000000000000000)⟩ ⟨(-911077515147321236108554608474889 / 100000000000000000000000000000000), (317637373349 / 100000000000000000000000000000000)⟩ ⟨-14, 441876206744648671114472127, 244140625000000000000000000⟩]
def CA1_6_9I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 5 => 1
  | 3, 5 => 2
  | 4, 4 => 3
  | 5, 2 => 1
  | 5, 3 => 2
  | _, _ => 0
def CA1_6_9I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R6Certificates (CA1_6_9I1R6CertificateIndex a)).input
def CA1_6_9I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R6Certificates (CA1_6_9I1R6CertificateIndex a)).output
def CA1_6_9I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA1_6_9I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
def CA1_6_9I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R7Certificates (CA1_6_9I1R7CertificateIndex a)).input
def CA1_6_9I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R7Certificates (CA1_6_9I1R7CertificateIndex a)).output
def CA1_6_9I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA1_6_9I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
def CA1_6_9I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R8Certificates (CA1_6_9I1R8CertificateIndex a)).input
def CA1_6_9I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R8Certificates (CA1_6_9I1R8CertificateIndex a)).output
def CA1_6_9I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA1_6_9I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
def CA1_6_9I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R9Certificates (CA1_6_9I1R9CertificateIndex a)).input
def CA1_6_9I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R9Certificates (CA1_6_9I1R9CertificateIndex a)).output
def CA1_6_9I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA1_6_9I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA1_6_9I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R10Certificates (CA1_6_9I1R10CertificateIndex a)).input
def CA1_6_9I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R10Certificates (CA1_6_9I1R10CertificateIndex a)).output
def CA1_6_9I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA1_6_9I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA1_6_9I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R11Certificates (CA1_6_9I1R11CertificateIndex a)).input
def CA1_6_9I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R11Certificates (CA1_6_9I1R11CertificateIndex a)).output
def CA1_6_9I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA1_6_9I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA1_6_9I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R12Certificates (CA1_6_9I1R12CertificateIndex a)).input
def CA1_6_9I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R12Certificates (CA1_6_9I1R12CertificateIndex a)).output
def CA1_6_9I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA1_6_9I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA1_6_9I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R13Certificates (CA1_6_9I1R13CertificateIndex a)).input
def CA1_6_9I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R13Certificates (CA1_6_9I1R13CertificateIndex a)).output
def CA1_6_9I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA1_6_9I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA1_6_9I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R14Certificates (CA1_6_9I1R14CertificateIndex a)).input
def CA1_6_9I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R14Certificates (CA1_6_9I1R14CertificateIndex a)).output
def CA1_6_9I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA1_6_9I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA1_6_9I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R15Certificates (CA1_6_9I1R15CertificateIndex a)).input
def CA1_6_9I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R15Certificates (CA1_6_9I1R15CertificateIndex a)).output
def CA1_6_9I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA1_6_9I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
def CA1_6_9I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R16Certificates (CA1_6_9I1R16CertificateIndex a)).input
def CA1_6_9I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R16Certificates (CA1_6_9I1R16CertificateIndex a)).output

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
def CA1_6_9I2PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 6 9)) (shape 1 6 9) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) a
def CA1_6_9I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 6 9) A1_6_9Law 2 a
def CA1_6_9I2PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 5, 5, 1, 0 => 1
  | 5, 5, 0, 1 => 1
  | 4, 5, 2, 0 => 2
  | 4, 5, 3, 0 => 3
  | 4, 5, 1, 1 => 4
  | 4, 5, 0, 2 => 2
  | 4, 5, 0, 3 => 3
  | 5, 4, 2, 0 => 2
  | 5, 4, 3, 0 => 3
  | 5, 4, 1, 1 => 4
  | 5, 4, 0, 2 => 2
  | 5, 4, 0, 3 => 3
  | 2, 5, 4, 0 => 5
  | 2, 5, 2, 1 => 6
  | 2, 5, 3, 1 => 7
  | 2, 5, 1, 2 => 6
  | 2, 5, 1, 3 => 7
  | 2, 5, 0, 4 => 5
  | 3, 5, 4, 0 => 8
  | 3, 5, 2, 1 => 9
  | 3, 5, 3, 1 => 10
  | 3, 5, 1, 2 => 9
  | 3, 5, 1, 3 => 10
  | 3, 5, 0, 4 => 8
  | 4, 4, 4, 0 => 11
  | 4, 4, 2, 1 => 12
  | 4, 4, 3, 1 => 13
  | 4, 4, 1, 2 => 12
  | 4, 4, 1, 3 => 13
  | 4, 4, 0, 4 => 11
  | 5, 2, 4, 0 => 5
  | 5, 2, 2, 1 => 6
  | 5, 2, 3, 1 => 7
  | 5, 2, 1, 2 => 6
  | 5, 2, 1, 3 => 7
  | 5, 2, 0, 4 => 5
  | 5, 3, 4, 0 => 8
  | 5, 3, 2, 1 => 9
  | 5, 3, 3, 1 => 10
  | 5, 3, 1, 2 => 9
  | 5, 3, 1, 3 => 10
  | 5, 3, 0, 4 => 8
  | 1, 5, 5, 0 => 14
  | 1, 5, 4, 1 => 15
  | 1, 5, 2, 2 => 16
  | 1, 5, 2, 3 => 17
  | 1, 5, 3, 2 => 17
  | 1, 5, 3, 3 => 18
  | 1, 5, 1, 4 => 15
  | 1, 5, 0, 5 => 14
  | 2, 4, 5, 0 => 19
  | 2, 4, 4, 1 => 20
  | 2, 4, 2, 2 => 21
  | 2, 4, 2, 3 => 22
  | 2, 4, 3, 2 => 22
  | 2, 4, 3, 3 => 23
  | 2, 4, 1, 4 => 20
  | 2, 4, 0, 5 => 19
  | 3, 4, 5, 0 => 24
  | 3, 4, 4, 1 => 25
  | 3, 4, 2, 2 => 26
  | 3, 4, 2, 3 => 27
  | 3, 4, 3, 2 => 27
  | 3, 4, 3, 3 => 28
  | 3, 4, 1, 4 => 25
  | 3, 4, 0, 5 => 24
  | 4, 2, 5, 0 => 19
  | 4, 2, 4, 1 => 20
  | 4, 2, 2, 2 => 21
  | 4, 2, 2, 3 => 22
  | 4, 2, 3, 2 => 22
  | 4, 2, 3, 3 => 23
  | 4, 2, 1, 4 => 20
  | 4, 2, 0, 5 => 19
  | 4, 3, 5, 0 => 24
  | 4, 3, 4, 1 => 25
  | 4, 3, 2, 2 => 26
  | 4, 3, 2, 3 => 27
  | 4, 3, 3, 2 => 27
  | 4, 3, 3, 3 => 28
  | 4, 3, 1, 4 => 25
  | 4, 3, 0, 5 => 24
  | 5, 1, 5, 0 => 14
  | 5, 1, 4, 1 => 15
  | 5, 1, 2, 2 => 16
  | 5, 1, 2, 3 => 17
  | 5, 1, 3, 2 => 17
  | 5, 1, 3, 3 => 18
  | 5, 1, 1, 4 => 15
  | 5, 1, 0, 5 => 14
  | 5, 0, 5, 1 => 14
  | 5, 0, 4, 2 => 19
  | 5, 0, 4, 3 => 24
  | 5, 0, 2, 4 => 19
  | 5, 0, 3, 4 => 24
  | 5, 0, 1, 5 => 14
  | 4, 1, 5, 1 => 15
  | 4, 1, 4, 2 => 20
  | 4, 1, 4, 3 => 25
  | 4, 1, 2, 4 => 20
  | 4, 1, 3, 4 => 25
  | 4, 1, 1, 5 => 15
  | 2, 2, 5, 1 => 16
  | 2, 2, 4, 2 => 21
  | 2, 2, 4, 3 => 26
  | 2, 2, 2, 4 => 21
  | 2, 2, 3, 4 => 26
  | 2, 2, 1, 5 => 16
  | 2, 3, 5, 1 => 17
  | 2, 3, 4, 2 => 22
  | 2, 3, 4, 3 => 27
  | 2, 3, 2, 4 => 22
  | 2, 3, 3, 4 => 27
  | 2, 3, 1, 5 => 17
  | 3, 2, 5, 1 => 17
  | 3, 2, 4, 2 => 22
  | 3, 2, 4, 3 => 27
  | 3, 2, 2, 4 => 22
  | 3, 2, 3, 4 => 27
  | 3, 2, 1, 5 => 17
  | 3, 3, 5, 1 => 18
  | 3, 3, 4, 2 => 23
  | 3, 3, 4, 3 => 28
  | 3, 3, 2, 4 => 23
  | 3, 3, 3, 4 => 28
  | 3, 3, 1, 5 => 18
  | 1, 4, 5, 1 => 15
  | 1, 4, 4, 2 => 20
  | 1, 4, 4, 3 => 25
  | 1, 4, 2, 4 => 20
  | 1, 4, 3, 4 => 25
  | 1, 4, 1, 5 => 15
  | 0, 5, 5, 1 => 14
  | 0, 5, 4, 2 => 19
  | 0, 5, 4, 3 => 24
  | 0, 5, 2, 4 => 19
  | 0, 5, 3, 4 => 24
  | 0, 5, 1, 5 => 14
  | 4, 0, 5, 2 => 5
  | 4, 0, 5, 3 => 8
  | 4, 0, 4, 4 => 11
  | 4, 0, 2, 5 => 5
  | 4, 0, 3, 5 => 8
  | 2, 1, 5, 2 => 6
  | 2, 1, 5, 3 => 9
  | 2, 1, 4, 4 => 12
  | 2, 1, 2, 5 => 6
  | 2, 1, 3, 5 => 9
  | 3, 1, 5, 2 => 7
  | 3, 1, 5, 3 => 10
  | 3, 1, 4, 4 => 13
  | 3, 1, 2, 5 => 7
  | 3, 1, 3, 5 => 10
  | 1, 2, 5, 2 => 6
  | 1, 2, 5, 3 => 9
  | 1, 2, 4, 4 => 12
  | 1, 2, 2, 5 => 6
  | 1, 2, 3, 5 => 9
  | 1, 3, 5, 2 => 7
  | 1, 3, 5, 3 => 10
  | 1, 3, 4, 4 => 13
  | 1, 3, 2, 5 => 7
  | 1, 3, 3, 5 => 10
  | 0, 4, 5, 2 => 5
  | 0, 4, 5, 3 => 8
  | 0, 4, 4, 4 => 11
  | 0, 4, 2, 5 => 5
  | 0, 4, 3, 5 => 8
  | 2, 0, 4, 5 => 2
  | 2, 0, 5, 4 => 2
  | 3, 0, 4, 5 => 3
  | 3, 0, 5, 4 => 3
  | 1, 1, 4, 5 => 4
  | 1, 1, 5, 4 => 4
  | 0, 2, 4, 5 => 2
  | 0, 2, 5, 4 => 2
  | 0, 3, 4, 5 => 3
  | 0, 3, 5, 4 => 3
  | 1, 0, 5, 5 => 1
  | 0, 1, 5, 5 => 1
  | _, _, _, _ => 0

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
def CA1_6_9I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA1_6_9I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
def CA1_6_9I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R0Certificates (CA1_6_9I2R0CertificateIndex a)).input
def CA1_6_9I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R0Certificates (CA1_6_9I2R0CertificateIndex a)).output
def CA1_6_9I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA1_6_9I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
def CA1_6_9I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(15382325296305947711052937 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(175988165289010751885124581 / 20000000000000000000000000000000), (286661 / 100000000000000000000000000000000)⟩ ⟨(-715058362028310178292855577849303 / 50000000000000000000000000000000), (465869746267 / 100000000000000000000000000000000)⟩ ⟨-21, 15382325296305947711052937, 11920928955078125000000000⟩]
def CA1_6_9I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA1_6_9I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R1Certificates (CA1_6_9I2R1CertificateIndex a)).input
def CA1_6_9I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R1Certificates (CA1_6_9I2R1CertificateIndex a)).output
def CA1_6_9I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA1_6_9I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
def CA1_6_9I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1967664415920849334251689419 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(9077465887398263442569774983 / 10000000000000000000000000000000), (31250197 / 100000000000000000000000000000000)⟩ ⟨(-230666007220293473135349718557659 / 25000000000000000000000000000000), (317637365409 / 100000000000000000000000000000000)⟩ ⟨-14, 1967664415920849334251689419, 1220703125000000000000000000⟩,
   .log ⟨(236563311141533721982429851 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1677385714010515046244526493 / 12500000000000000000000000000000), (2254247 / 50000000000000000000000000000000)⟩ ⟨(-28362567397561494462781291018621 / 2500000000000000000000000000000), (381164910837 / 100000000000000000000000000000000)⟩ ⟨-17, 236563311141533721982429851, 152587890625000000000000000⟩,
   .log ⟨(37536856304181027501326567191 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(148037894805379859615916769287 / 50000000000000000000000000000000), (10333361 / 10000000000000000000000000000000)⟩ ⟨(-394380108994078757733136660996807 / 50000000000000000000000000000000), (275285710543 / 100000000000000000000000000000000)⟩ ⟨-12, 37536856304181027501326567191, 24414062500000000000000000000⟩]
def CA1_6_9I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_6_9I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R2Certificates (CA1_6_9I2R2CertificateIndex a)).input
def CA1_6_9I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R2Certificates (CA1_6_9I2R2CertificateIndex a)).output
def CA1_6_9I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA1_6_9I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
def CA1_6_9I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(47639572620445901729347554581 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(45550944730904560016893522953 / 12500000000000000000000000000000), (8196559 / 6250000000000000000000000000000)⟩ ⟨(-382463084577337735485603822228969 / 50000000000000000000000000000000), (137642854989 / 50000000000000000000000000000000)⟩ ⟨-12, 47639572620445901729347554581, 24414062500000000000000000000⟩,
   .log ⟨(404985042186294983709925891827 / 25000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(3339329250362934946673635828707 / 50000000000000000000000000000000), (1200624877 / 50000000000000000000000000000000)⟩ ⟨(-103069524257479493504067476311811 / 25000000000000000000000000000000), (37057691553 / 25000000000000000000000000000000)⟩ ⟨-6, 404985042186294983709925891827, 390625000000000000000000000000⟩,
   .log ⟨(78457363860611206788924191831 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(15831771560782973034392613207 / 1562500000000000000000000000000), (365507863 / 100000000000000000000000000000000)⟩ ⟨(-645722294270706890661498213531627 / 100000000000000000000000000000000), (232934061787 / 100000000000000000000000000000000)⟩ ⟨-10, 78457363860611206788924191831, 48828125000000000000000000000⟩]
def CA1_6_9I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_6_9I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R3Certificates (CA1_6_9I2R3CertificateIndex a)).input
def CA1_6_9I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R3Certificates (CA1_6_9I2R3CertificateIndex a)).output
def CA1_6_9I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA1_6_9I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
def CA1_6_9I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2430534116665658559357617653 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(48278512173544068138928239363 / 100000000000000000000000000000000), (257343 / 1562500000000000000000000000000)⟩ ⟨(-993166725011356917556399735208013 / 100000000000000000000000000000000), (338813199499 / 100000000000000000000000000000000)⟩ ⟨-15, 2430534116665658559357617653, 1525878906250000000000000000⟩,
   .log ⟨(962949217498128365494858418103 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(3803435256577646695635444709003 / 50000000000000000000000000000000), (2854774029 / 100000000000000000000000000000000)⟩ ⟨(-197488880382471427455807499445087 / 50000000000000000000000000000000), (37057691523 / 25000000000000000000000000000000)⟩ ⟨-6, 962949217498128365494858418103, 781250000000000000000000000000⟩,
   .log ⟨(4093220773158589283453798912321 / 20000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩ ⟨(32467430003058226294756699721411 / 100000000000000000000000000000000), (4333866083 / 25000000000000000000000000000000)⟩ ⟨(-39660003457380450449429580641009 / 25000000000000000000000000000000), (42351647417 / 50000000000000000000000000000000)⟩ ⟨-3, 4093220773158589283453798912321, 2500000000000000000000000000000⟩,
   .log ⟨(1061167029337240682905698619983 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(2411927025093196302256514455281 / 50000000000000000000000000000000), (359537377 / 20000000000000000000000000000000)⟩ ⟨(-227290045620771148198607657163703 / 50000000000000000000000000000000), (42351647413 / 25000000000000000000000000000000)⟩ ⟨-7, 1061167029337240682905698619983, 781250000000000000000000000000⟩,
   .log ⟨(1264315461666651412057543429 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(13383092011192096452737170241 / 50000000000000000000000000000000), (4551403 / 50000000000000000000000000000000)⟩ ⟨(-211704948914413794328644497200899 / 20000000000000000000000000000000), (179994521079 / 50000000000000000000000000000000)⟩ ⟨-16, 1264315461666651412057543429, 762939453125000000000000000⟩]
def CA1_6_9I2R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 0 => 1
  | 4, 1 => 2
  | 2, 2 => 3
  | 2, 3 => 4
  | 3, 2 => 4
  | 3, 3 => 5
  | 1, 4 => 2
  | 0, 5 => 1
  | _, _ => 0
def CA1_6_9I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R4Certificates (CA1_6_9I2R4CertificateIndex a)).input
def CA1_6_9I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R4Certificates (CA1_6_9I2R4CertificateIndex a)).output
def CA1_6_9I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA1_6_9I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
def CA1_6_9I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5230646719901306559878843 / 39062500000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(119421215364038691133498363387 / 100000000000000000000000000000000), (992439 / 2500000000000000000000000000000)⟩ ⟨(-178367665604676125594917184952803 / 20000000000000000000000000000000), (296461539029 / 100000000000000000000000000000000)⟩ ⟨-13, 5230646719901306559878843, 4768371582031250000000000⟩,
   .log ⟨(4446714786534358028185757328621 / 50000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩ ⟨(10760415824659170996692001674603 / 50000000000000000000000000000000), (4708142459 / 50000000000000000000000000000000)⟩ ⟨(-241985743210787991177003382232591 / 100000000000000000000000000000000), (105879118707 / 100000000000000000000000000000000)⟩ ⟨-4, 4446714786534358028185757328621, 3125000000000000000000000000000⟩,
   .log ⟨(82050376313928551286274993721 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(938541057060807284277361877919 / 50000000000000000000000000000000), (138998747 / 20000000000000000000000000000000)⟩ ⟨(-71491221249088608811744699231191 / 12500000000000000000000000000000), (211758237439 / 100000000000000000000000000000000)⟩ ⟨-9, 82050376313928551286274993721, 48828125000000000000000000000⟩]
def CA1_6_9I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA1_6_9I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R5Certificates (CA1_6_9I2R5CertificateIndex a)).input
def CA1_6_9I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R5Certificates (CA1_6_9I2R5CertificateIndex a)).output
def CA1_6_9I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA1_6_9I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
def CA1_6_9I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(6327170418027537211250852597 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(28392940486801011288001427499 / 25000000000000000000000000000000), (37515263 / 100000000000000000000000000000000)⟩ ⟨(-179498503191272437656422737403447 / 20000000000000000000000000000000), (37057692433 / 12500000000000000000000000000000)⟩ ⟨-13, 6327170418027537211250852597, 6103515625000000000000000000⟩,
   .log ⟨(398636850457313655069073 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(7433476221723436291366273 / 50000000000000000000000000000000), (1187 / 25000000000000000000000000000000)⟩ ⟨(-932361899457588997304740056174253 / 50000000000000000000000000000000), (148262122641 / 25000000000000000000000000000000)⟩ ⟨-27, 398636850457313655069073, 372529029846191406250000⟩,
   .log ⟨(1326913022802868439058073980313 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(89614625494726809618503117817 / 1562500000000000000000000000000), (449575627 / 20000000000000000000000000000000)⟩ ⟨(-432231497701909322046546714671963 / 100000000000000000000000000000000), (169406589991 / 100000000000000000000000000000000)⟩ ⟨-7, 1326913022802868439058073980313, 781250000000000000000000000000⟩]
def CA1_6_9I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA1_6_9I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R6Certificates (CA1_6_9I2R6CertificateIndex a)).input
def CA1_6_9I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R6Certificates (CA1_6_9I2R6CertificateIndex a)).output
def CA1_6_9I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA1_6_9I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
def CA1_6_9I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R7Certificates (CA1_6_9I2R7CertificateIndex a)).input
def CA1_6_9I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R7Certificates (CA1_6_9I2R7CertificateIndex a)).output
def CA1_6_9I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA1_6_9I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
def CA1_6_9I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R8Certificates (CA1_6_9I2R8CertificateIndex a)).input
def CA1_6_9I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R8Certificates (CA1_6_9I2R8CertificateIndex a)).output
def CA1_6_9I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA1_6_9I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
def CA1_6_9I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R9Certificates (CA1_6_9I2R9CertificateIndex a)).input
def CA1_6_9I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R9Certificates (CA1_6_9I2R9CertificateIndex a)).output
def CA1_6_9I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA1_6_9I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
def CA1_6_9I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R10Certificates (CA1_6_9I2R10CertificateIndex a)).input
def CA1_6_9I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R10Certificates (CA1_6_9I2R10CertificateIndex a)).output
def CA1_6_9I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA1_6_9I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
def CA1_6_9I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R11Certificates (CA1_6_9I2R11CertificateIndex a)).input
def CA1_6_9I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R11Certificates (CA1_6_9I2R11CertificateIndex a)).output
def CA1_6_9I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA1_6_9I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
def CA1_6_9I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R12Certificates (CA1_6_9I2R12CertificateIndex a)).input
def CA1_6_9I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R12Certificates (CA1_6_9I2R12CertificateIndex a)).output
def CA1_6_9I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA1_6_9I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
def CA1_6_9I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R13Certificates (CA1_6_9I2R13CertificateIndex a)).input
def CA1_6_9I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R13Certificates (CA1_6_9I2R13CertificateIndex a)).output
def CA1_6_9I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA1_6_9I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
def CA1_6_9I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R14Certificates (CA1_6_9I2R14CertificateIndex a)).input
def CA1_6_9I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R14Certificates (CA1_6_9I2R14CertificateIndex a)).output
def CA1_6_9I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA1_6_9I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
def CA1_6_9I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R15Certificates (CA1_6_9I2R15CertificateIndex a)).input
def CA1_6_9I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R15Certificates (CA1_6_9I2R15CertificateIndex a)).output
def CA1_6_9I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA1_6_9I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
def CA1_6_9I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_6_9I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R16Certificates (CA1_6_9I2R16CertificateIndex a)).input
def CA1_6_9I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R16Certificates (CA1_6_9I2R16CertificateIndex a)).output
def CA1_6_9I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 0, 5, 3 => Z0_5_3H2H
  | 0, 6, 2 => Z0_6_2H2H
  | 1, 0, 7 => Z1_0_7H2H
  | _, _, _ => (.exact 0)

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
def CA1_7_8I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 1 7 8)) A1_7_8Law ((Equiv.refl (Fin 3)) 0) a
def CA1_7_8I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(50000000000000000000000000000001 / 100000000000000000000000000000000), (69 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (105879119 / 500000000000000000000000000000)⟩ ⟨(-8664339756999316367715399131291 / 12500000000000000000000000000000), (42351647503 / 100000000000000000000000000000000)⟩ ⟨-1, 50000000000000000000000000000001, 50000000000000000000000000000000⟩]
def CA1_7_8I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I0Certificates (CA1_7_8I0CertificateIndex a)).input
def CA1_7_8I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I0Certificates (CA1_7_8I0CertificateIndex a)).output

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
def CA1_7_8I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 7 8)) (shape 1 7 8) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA1_7_8I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 7 8) A1_7_8Law 1 a

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
def CA1_7_8I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA1_7_8I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
def CA1_7_8I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(584532371534609447407610401 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(7043538258496618443777008947 / 100000000000000000000000000000000), (1175919 / 50000000000000000000000000000000)⟩ ⟨(-1204986858128109531200624689824771 / 100000000000000000000000000000000), (40234099213 / 10000000000000000000000000000000)⟩ ⟨-18, 584532371534609447407610401, 381469726562500000000000000⟩]
def CA1_7_8I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA1_7_8I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R0Certificates (CA1_7_8I1R0CertificateIndex a)).input
def CA1_7_8I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R0Certificates (CA1_7_8I1R0CertificateIndex a)).output
def CA1_7_8I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA1_7_8I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
def CA1_7_8I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(37035762938464593102856286141 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(533899727137404610567259234731 / 100000000000000000000000000000000), (94111543 / 50000000000000000000000000000000)⟩ ⟨(-28831577090742589774638387234999 / 4000000000000000000000000000000), (15881867931 / 6250000000000000000000000000000)⟩ ⟨-11, 37035762938464593102856286141, 24414062500000000000000000000⟩]
def CA1_7_8I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA1_7_8I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R1Certificates (CA1_7_8I1R1CertificateIndex a)).input
def CA1_7_8I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R1Certificates (CA1_7_8I1R1CertificateIndex a)).output
def CA1_7_8I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA1_7_8I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
def CA1_7_8I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(191222039936786006968920366603 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(889192484118741395146123232667 / 20000000000000000000000000000000), (404928429 / 25000000000000000000000000000000)⟩ ⟨(-116251307173154539090529363913951 / 25000000000000000000000000000000), (169406590091 / 100000000000000000000000000000000)⟩ ⟨-7, 191222039936786006968920366603, 156250000000000000000000000000⟩,
   .log ⟨(99733771788650035743636910389 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(344601181037491046007893380543 / 50000000000000000000000000000000), (232313933 / 100000000000000000000000000000000)⟩ ⟨(-691042111127110831503848470013037 / 100000000000000000000000000000000), (46586812303 / 20000000000000000000000000000000)⟩ ⟨-10, 99733771788650035743636910389, 97656250000000000000000000000⟩,
   .log ⟨(893074147967023893622413206403 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩ ⟨(11902754689191070752310359424387 / 100000000000000000000000000000000), (567347429 / 12500000000000000000000000000000)⟩ ⟨(-333196149398296411637838059992123 / 100000000000000000000000000000000), (127054942517 / 100000000000000000000000000000000)⟩ ⟨-5, 893074147967023893622413206403, 781250000000000000000000000000⟩]
def CA1_7_8I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_7_8I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R2Certificates (CA1_7_8I1R2CertificateIndex a)).input
def CA1_7_8I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R2Certificates (CA1_7_8I1R2CertificateIndex a)).output
def CA1_7_8I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA1_7_8I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
def CA1_7_8I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(23755725364738632673182145927 / 3125000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(92730302782309864385551828973 / 2500000000000000000000000000000), (72438777 / 5000000000000000000000000000000)⟩ ⟨(-487936599275307531018982220159061 / 100000000000000000000000000000000), (38116482761 / 20000000000000000000000000000000)⟩ ⟨-8, 23755725364738632673182145927, 12207031250000000000000000000⟩,
   .log ⟨(19452192305358146935978508749949 / 100000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩ ⟨(31847331688048502861394488834571 / 100000000000000000000000000000000), (16476647881 / 100000000000000000000000000000000)⟩ ⟨(-40930260183676172240128151715623 / 25000000000000000000000000000000), (84703294927 / 100000000000000000000000000000000)⟩ ⟨-3, 19452192305358146935978508749949, 12500000000000000000000000000000⟩,
   .log ⟨(935634211750446234858590523347 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(7444941879560739999523215666747 / 100000000000000000000000000000000), (554759107 / 20000000000000000000000000000000)⟩ ⟨(-79571073674531966587660539103193 / 20000000000000000000000000000000), (74115382997 / 50000000000000000000000000000000)⟩ ⟨-6, 935634211750446234858590523347, 781250000000000000000000000000⟩]
def CA1_7_8I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_7_8I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R3Certificates (CA1_7_8I1R3CertificateIndex a)).input
def CA1_7_8I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R3Certificates (CA1_7_8I1R3CertificateIndex a)).output
def CA1_7_8I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA1_7_8I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
def CA1_7_8I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(15627028006695398584059032451 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(230580833894447540330567428909 / 50000000000000000000000000000000), (1588393 / 1000000000000000000000000000000)⟩ ⟨(-737762912422167558497093805111299 / 100000000000000000000000000000000), (50821977159 / 20000000000000000000000000000000)⟩ ⟨-11, 15627028006695398584059032451, 12207031250000000000000000000⟩,
   .log ⟨(2473098266048731246033486140617 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩ ⟨(7435496762584514584666307602159 / 50000000000000000000000000000000), (6284387201 / 100000000000000000000000000000000)⟩ ⟨(-300655128211472434651138191805343 / 100000000000000000000000000000000), (127054942401 / 100000000000000000000000000000000)⟩ ⟨-5, 2473098266048731246033486140617, 1562500000000000000000000000000⟩,
   .log ⟨(28955837401340539615145743394389 / 100000000000000000000000000000000), (69 / 100000000000000000000000000000000)⟩ ⟨(17943908765390744531566152093057 / 50000000000000000000000000000000), (18394911377 / 100000000000000000000000000000000)⟩ ⟨(-123939836494316087214867202179321 / 100000000000000000000000000000000), (31763735643 / 50000000000000000000000000000000)⟩ ⟨-2, 28955837401340539615145743394389, 25000000000000000000000000000000⟩,
   .log ⟨(311323194051302437148547523701 / 12500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩ ⟨(459843328596575980405811384097 / 5000000000000000000000000000000), (147672563 / 4000000000000000000000000000000)⟩ ⟨(-369265234154702230875504734955431 / 100000000000000000000000000000000), (74115383051 / 50000000000000000000000000000000)⟩ ⟨-6, 311323194051302437148547523701, 195312500000000000000000000000⟩,
   .log ⟨(42574017330296904029223267387 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1309628587183769853925035297047 / 100000000000000000000000000000000), (9015399 / 2000000000000000000000000000000)⟩ ⟨(-76903042589535015149302725245349 / 12500000000000000000000000000000), (211758237299 / 100000000000000000000000000000000)⟩ ⟨-9, 42574017330296904029223267387, 39062500000000000000000000000⟩]
def CA1_7_8I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA1_7_8I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R4Certificates (CA1_7_8I1R4CertificateIndex a)).input
def CA1_7_8I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R4Certificates (CA1_7_8I1R4CertificateIndex a)).output
def CA1_7_8I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(56490034731352553689181797071 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(383325221697784832231938850641 / 50000000000000000000000000000000), (16448067 / 6250000000000000000000000000000)⟩ ⟨(-67857140382502786554008324328631 / 10000000000000000000000000000000), (232934061397 / 100000000000000000000000000000000)⟩ ⟨-10, 56490034731352553689181797071, 48828125000000000000000000000⟩,
   .log ⟨(1256825878128021407454329983707 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩ ⟨(92588693557674396110477875221 / 1000000000000000000000000000000), (1863002657 / 50000000000000000000000000000000)⟩ ⟨(-92085840179767555893425843607037 / 25000000000000000000000000000000), (74115383169 / 50000000000000000000000000000000)⟩ ⟨-6, 1256825878128021407454329983707, 781250000000000000000000000000⟩,
   .log ⟨(107680220843939967773020797327 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(66122249585888860257413042173 / 5000000000000000000000000000000), (456043489 / 100000000000000000000000000000000)⟩ ⟨(-122812247351756970586692448402091 / 20000000000000000000000000000000), (105879118879 / 50000000000000000000000000000000)⟩ ⟨-9, 107680220843939967773020797327, 97656250000000000000000000000⟩]
def CA1_7_8I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CA1_7_8I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_7_8I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA1_7_8I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
def CA1_7_8I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_7_8I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R10Certificates (CA1_7_8I1R10CertificateIndex a)).input
def CA1_7_8I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R10Certificates (CA1_7_8I1R10CertificateIndex a)).output
def CA1_7_8I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA1_7_8I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
def CA1_7_8I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_7_8I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R11Certificates (CA1_7_8I1R11CertificateIndex a)).input
def CA1_7_8I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R11Certificates (CA1_7_8I1R11CertificateIndex a)).output
def CA1_7_8I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA1_7_8I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
def CA1_7_8I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_7_8I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R12Certificates (CA1_7_8I1R12CertificateIndex a)).input
def CA1_7_8I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R12Certificates (CA1_7_8I1R12CertificateIndex a)).output
def CA1_7_8I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA1_7_8I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
def CA1_7_8I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_7_8I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R13Certificates (CA1_7_8I1R13CertificateIndex a)).input
def CA1_7_8I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R13Certificates (CA1_7_8I1R13CertificateIndex a)).output
def CA1_7_8I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA1_7_8I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
def CA1_7_8I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_7_8I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R14Certificates (CA1_7_8I1R14CertificateIndex a)).input
def CA1_7_8I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R14Certificates (CA1_7_8I1R14CertificateIndex a)).output
def CA1_7_8I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA1_7_8I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
def CA1_7_8I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_7_8I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R15Certificates (CA1_7_8I1R15CertificateIndex a)).input
def CA1_7_8I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R15Certificates (CA1_7_8I1R15CertificateIndex a)).output
def CA1_7_8I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA1_7_8I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
def CA1_7_8I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_7_8I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R16Certificates (CA1_7_8I1R16CertificateIndex a)).input
def CA1_7_8I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R16Certificates (CA1_7_8I1R16CertificateIndex a)).output

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_JointScalarOrbitAdmissibility
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointScalarOrbitAdmissibility

open JointPopulation JointCanonicalization PermutationMatching
attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ) (L R : H → Type*)

section Windows

variable {SL SR : H → Type*}
    [∀ h, Fintype (SL h)] [∀ h, Fintype (SR h)]
    [∀ h, DecidableEq (SL h)] [∀ h, DecidableEq (SR h)]
    (sl : ∀ c : ClassKey (H := H), L c.1 → SL c.1)
    (sr : ∀ c : ClassKey (H := H), R c.1 → SR c.1)
    (νl : ∀ c : ClassKey (H := H), SL c.1 → ℝ)
    (νr : ∀ c : ClassKey (H := H), SR c.1 → ℝ)
    (ηl ηr : ClassKey (H := H) → ℝ)

omit [Fintype H] [DecidableEq H] in
theorem rawWindows_smul (e : Target counts) :
    letI : MulAction (HalfClassPermutations (ClassPositions counts)) (RawPairs counts L R) :=
      EquivOrbitTransport.action (pairEquiv counts L R e)
    ∀ (g : HalfClassPermutations (ClassPositions counts)) (w : RawPairs counts L R),
      rawWindows counts L R sl sr νl νr ηl ηr e ((EquivOrbitTransport.action (pairEquiv counts L R e)).smul g w) ↔
      rawWindows counts L R sl sr νl νr ηl ηr e w := by
  let : MulAction (HalfClassPermutations (ClassPositions counts)) (RawPairs counts L R) :=
    EquivOrbitTransport.action (pairEquiv counts L R e)
  intro g w
  rw [rawWindows_iff_childWindows, rawWindows_iff_childWindows]
  change HistorySymmetry.childWindows _ _ _ _ _ _
      ((pairEquiv counts L R e) ((pairEquiv counts L R e).symm
        (g • (pairEquiv counts L R e) w))) ↔ _
  rw [Equiv.apply_symm_apply]
  exact HistorySymmetry.childWindows_smul _ _ _ _ _ _ g _

end Windows

end MatrixMultiplication.JointScalarOrbitAdmissibility

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_GroupAssignmentRetention
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
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

theorem admissible_smul (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma) :
    letI : MulAction (Symmetries (K := K) (tick := tick) allocation m sigma) (Raw (K := K) (tick := tick) allocation m sigma) :=
      rawAction (K := K) (tick := tick) allocation m sigma e
    ∀ (g : Symmetries (K := K) (tick := tick) allocation m sigma) (w : Raw (K := K) (tick := tick) allocation m sigma),
      Admissible (K := K) (tick := tick) allocation m ε sigma side e w →
      Admissible (K := K) (tick := tick) allocation m ε sigma side e ((rawAction (K := K) (tick := tick) allocation m sigma e).smul g w) := by
  let : MulAction (Symmetries (K := K) (tick := tick) allocation m sigma) (Raw (K := K) (tick := tick) allocation m sigma) :=
    rawAction (K := K) (tick := tick) allocation m sigma e
  intro g w hw
  have hweights : ∀ h j,
      CWStrands.weight (((rawAction (K := K) (tick := tick) allocation m sigma e).smul g w) h j).1 = (shapeSide (sigma side) ((e h).val j)).val ∧
      CWStrands.weight (((rawAction (K := K) (tick := tick) allocation m sigma e).smul g w) h j).2 = activeParentShape h.val (sigma side) -
        (shapeSide (sigma side) ((e h).val j)).val := by
    exact JointScalarOrbitAdmissibility.classWeights_smul
      (Counts (K := K) (tick := tick) allocation m sigma)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun _ => CWStrands.weight) (fun _ => CWStrands.weight)
      (fun _ u => (shapeSide (sigma side) u).val)
      (fun h u => activeParentShape h.val (sigma side) - (shapeSide (sigma side) u).val)
      e g w hw.2
  refine ⟨⟨?_, ?_⟩, hweights⟩
  · intro h j
    apply Fin.ext
    exact (hweights h j).1
  · exact (JointScalarOrbitAdmissibility.rawWindows_smul
      (SL := fun h : ActiveOrder K tick sigma => Statistic h.val)
      (SR := fun h : ActiveOrder K tick sigma => Statistic h.val)
      (Counts (K := K) (tick := tick) allocation m sigma)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun c => statistic c.1.val) (fun c => statistic c.1.val)
      (fun c => leftLaw c.1.val c.2 (sigma side))
      (fun c => rightLaw c.1.val c.2 (sigma side))
      (fun c => AllFieldHistoryMasks.childWidth ε c.1.val)
      (fun c => AllFieldHistoryMasks.childWidth ε c.1.val) e g w).mpr hw.1.2

theorem admissible_of_orbitOf_eq (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w v : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible (K := K) (tick := tick) allocation m ε sigma side e w)
    (hv : orbitOf (K := K) (tick := tick) allocation m sigma e v = orbitOf (K := K) (tick := tick) allocation m sigma e w) :
    Admissible (K := K) (tick := tick) allocation m ε sigma side e v := by
  let : MulAction (Symmetries (K := K) (tick := tick) allocation m sigma) (Raw (K := K) (tick := tick) allocation m sigma) :=
    rawAction (K := K) (tick := tick) allocation m sigma e
  have hrel : MulAction.orbitRel
      (Symmetries (K := K) (tick := tick) allocation m sigma)
      (CanonicalPairs (Counts (K := K) (tick := tick) allocation m sigma)
        (fun h => Fin (activeHalfLength h.val) → Fin 7)
        (fun h => Fin (activeHalfLength h.val) → Fin 7))
      (groupCoordinates (K := K) (tick := tick) allocation m sigma e v)
      (groupCoordinates (K := K) (tick := tick) allocation m sigma e w) := Quotient.exact hv
  obtain ⟨g, hg⟩ := hrel
  have hgv : ((rawAction (K := K) (tick := tick) allocation m sigma e).smul g w) = v := by
    apply (groupCoordinates (K := K) (tick := tick) allocation m sigma e).injective
    exact (EquivOrbitTransport.equiv_smul
      (groupCoordinates (K := K) (tick := tick) allocation m sigma e) g w).trans hg
  rw [← hgv]
  exact admissible_smul allocation m ε sigma side e g w hw

theorem full_admissible (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (ho : o ∈ (data (K := K) (tick := tick) allocation m ε sigma).orbits e)
    (v : Variable (K := K) (tick := tick) allocation m sigma) (hv : v ∈ (data (K := K) (tick := tick) allocation m ε sigma).full e o) :
    Admissible (K := K) (tick := tick) allocation m ε sigma v.1 e v.2 := by
  obtain ⟨w, hw, hwo⟩ := (Finset.mem_filter.mp ho).2
  obtain ⟨hside, hvo⟩ := (Finset.mem_filter.mp hv).2
  rw [hside]
  exact admissible_of_orbitOf_eq allocation m ε sigma o.1 e w v.2 hw (hvo.trans hwo.symm)

end MatrixMultiplication.AllFieldGroupAdmissible

end
end

end MatrixAllFields

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

theorem used_project_admissible (F : Type*) [CommRing F]
    (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m)
    (side : Fin 3) (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryRecovery.Used F allocation m ε e (sigma side) w) :
    Admissible (K := K) (tick := tick) allocation m ε sigma side
      (projectTarget (K := K) (tick := tick) allocation m sigma e) (projectRaw (K := K) (tick := tick) allocation m sigma w) := by
  obtain ⟨x, y, z, hq, rfl⟩ := hw
  have hi :
      AllFieldHistoryRecovery.idealSide allocation m ε 0 e x ∧
      AllFieldHistoryRecovery.idealSide allocation m ε 1 e y ∧
      AllFieldHistoryRecovery.idealSide allocation m ε 2 e z := by
    by_contra hn
    apply hq
    rw [AllFieldHistoryRecovery.ideal_eq_delete_source F allocation m ε e]
    exact ite_eq_right hn
  have ht := AllFieldHistoryRecovery.ideal_support_weights F allocation m ε e x y z hq
  have hs (s : Fin 3) :
      AllFieldHistoryRecovery.idealSide allocation m ε s e
          (AllFieldHistoryRecovery.sideVariable s x y z) ∧
        AllFieldHistoryRecovery.sideWeights allocation m s e
          (AllFieldHistoryRecovery.sideVariable s x y z) := by
    fin_cases s
    · exact ⟨hi.1, ht.1⟩
    · exact ⟨hi.2.1, ht.2.1⟩
    · exact ⟨hi.2.2, ht.2.2⟩
  refine ⟨?_, ?_⟩
  · exact (idealSide_iff_all_groups allocation m ε
      (sigma side) e _).mp (hs (sigma side)).1 sigma
  · intro h j
    exact (hs (sigma side)).2 h.val j

end MatrixMultiplication.AllFieldGroupAdmissible

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupAssignmentRetention
open AllFieldHistory AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData JointCoarseHashing
attribute [local instance] Classical.propDecidable Classical.decEq
variable {K tick : ℕ}

def assigned (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (v : Variable (K := K) (tick := tick) allocation m sigma) : Option (Triple (Pos (K := K) (tick := tick) allocation m sigma)) :=
  (data allocation m ε sigma).actualAssignment k U
    (actualCompatible allocation m ε sigma) (actualUseful allocation m ε sigma)
    (actualKeep allocation m ε sigma) s v

def physicalAssignment (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k) :
    JointExtraction.Assignment (Raw (K := K) (tick := tick) allocation m sigma) (Raw (K := K) (tick := tick) allocation m sigma)
      (Raw (K := K) (tick := tick) allocation m sigma) (Triple (Pos (K := K) (tick := tick) allocation m sigma)) where
  x w := assigned allocation m ε sigma k U s (sigma.symm 0, w)
  y w := assigned allocation m ε sigma k U s (sigma.symm 1, w)
  z w := assigned allocation m ε sigma k U s (sigma.symm 2, w)

theorem assigned_spec (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (v : Variable (K := K) (tick := tick) allocation m sigma) (t : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (h : assigned allocation m ε sigma k U s v = some t) :
    t ∈ (data allocation m ε sigma).actualEligible k U s ∧
      actualCompatible allocation m ε sigma t v ∧ actualUseful allocation m ε sigma t v ∧
      ∀ f, f ∈ (data allocation m ε sigma).actualEligible k U s →
        actualCompatible allocation m ε sigma f v → f = t := by
  have hh := JointExtraction.retainAssignment_some _ _ v t h
  exact JointCoarseAssignment.assignUseful_spec _ _ _ v t hh

theorem assigned_some_idealSide (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma)
    (h : assigned allocation m ε sigma k U s v = some (coarse allocation m sigma e)) :
    groupIdealSide allocation m ε (sigma v.1) sigma e v.2 := by
  exact (actualUseful_coarse allocation m ε sigma e v).mp
    (assigned_spec allocation m ε sigma k U s v _ h).2.2.1

end MatrixMultiplication.AllFieldGroupAssignmentRetention

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupCompatibility

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistoryGroupMasks
open AllFieldHistoryGroupedRecovery AllFieldGroupOrbitData
open JointPopulation JointCanonicalization

attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

theorem groupIdealSide_ownWord (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : groupIdealSide allocation m ε (sigma side) sigma e w) :
    tripleSide side (AllFieldGroupOrbitData.coarse allocation m sigma e) =
      ownWord allocation m sigma w := by
  change tripleSide side
    (reorder sigma (triple (Counts (K := K) (tick := tick) allocation m sigma) e)) = _
  rw [tripleSide_reorder]
  funext p
  have hs : tripleSide (sigma side)
      (triple (Counts (K := K) (tick := tick) allocation m sigma) e) p =
      shapeSide (sigma side) ((e p.1).val p.2) := by
    generalize sigma side = s
    fin_cases s <;> rfl
  rw [hs]
  exact (hw.1 p.1 p.2).symm

theorem groupIdealSide_fineCompatible (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : groupIdealSide allocation m ε (sigma side) sigma e w) :
    fineCompatible allocation m ε sigma side e w := by
  intro right h u hd
  apply JointPopulationCompatibility.shape_count_window_of_typeWindow
    (Counts (K := K) (tick := tick) allocation m sigma) e h u
    (fun i => statistic h.val (if right then (w h i).2 else (w h i).1))
    (compatibilityLaw right side sigma h u) (AllFieldHistoryMasks.childWidth ε h.val)
  intro hu
  rw [AllFieldGroupNativeLaws.compatibilityLaw_eq allocation m sigma right side h u hu hd]
  cases right
  · exact (hw.2 h u hu).1
  · exact (hw.2 h u hu).2

theorem groupIdealSide_compatible (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : groupIdealSide allocation m ε (sigma side) sigma e w) :
    Compatible allocation m ε sigma side e w :=
  ⟨groupIdealSide_ownWord allocation m ε sigma side e w hw,
    groupIdealSide_fineCompatible allocation m ε sigma side e w hw⟩

theorem admissible_compatible (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : Admissible allocation m ε sigma side e w) :
    Compatible allocation m ε sigma side e w :=
  groupIdealSide_compatible allocation m ε sigma side e w hw.1

end MatrixMultiplication.AllFieldGroupCompatibility

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupAssignmentRetention
open AllFieldHistory AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData JointCoarseHashing
attribute [local instance] Classical.propDecidable Classical.decEq
variable {K tick : ℕ}

theorem good_failure_fraction_le (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (hg : (data (K := K) (tick := tick) allocation m ε sigma).Good k U N e s)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (ho : o ∈ (data (K := K) (tick := tick) allocation m ε sigma).orbits e) :
    ((((data (K := K) (tick := tick) allocation m ε sigma).passing e o).filter
      (fun v => assigned (K := K) (tick := tick) allocation m ε sigma k U s v ≠ some (coarse (K := K) (tick := tick) allocation m sigma e))).card : ℝ) /
        (((data (K := K) (tick := tick) allocation m ε sigma).full e o).card : ℝ) ≤ 1 / N := by
  have ha (v : Variable (K := K) (tick := tick) allocation m sigma)
      (hv : v ∈ (data (K := K) (tick := tick) allocation m ε sigma).passing e o) :
      Admissible (K := K) (tick := tick) allocation m ε sigma v.1 e v.2 :=
    AllFieldGroupAdmissible.full_admissible (K := K) (tick := tick) allocation m ε sigma e o ho v
      ((mem_passing (K := K) (tick := tick) allocation m ε sigma e o v).mp hv).1
  have hc (v : Variable (K := K) (tick := tick) allocation m sigma)
      (hv : v ∈ (data (K := K) (tick := tick) allocation m ε sigma).passing e o) :
      Compatible (K := K) (tick := tick) allocation m ε sigma v.1 e v.2 :=
    AllFieldGroupCompatibility.admissible_compatible (K := K) (tick := tick) allocation m ε sigma v.1 e v.2 (ha v hv)
  have hh := (data (K := K) (tick := tick) allocation m ε sigma).good_passing_actual_failure_fraction_le k U hAP N e o ho s hg
    (actualCompatible (K := K) (tick := tick) allocation m ε sigma) (actualUseful (K := K) (tick := tick) allocation m ε sigma)
    (actualKeep (K := K) (tick := tick) allocation m ε sigma)
    (fun v hv => (actualCompatible_coarse (K := K) (tick := tick) allocation m ε sigma e v).mpr (hc v hv))
    (fun v hv => (actualUseful_coarse (K := K) (tick := tick) allocation m ε sigma e v).mpr (ha v hv).1)
    (fun v hv => ((mem_passing (K := K) (tick := tick) allocation m ε sigma e o v).mp hv).2)
    (fun v hv f hf hn hcomp => competitor_coverage (K := K) (tick := tick) allocation m ε sigma e o v (hc v hv) f hn hcomp)

  rw [Finset.filter_congr_decidable] at hh
  exact hh

end MatrixMultiplication.AllFieldGroupAssignmentRetention

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupAssignmentRetention

open AllFieldHistory AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData JointCoarseHashing
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem good_local_failure_le (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (hg : (data allocation m ε sigma).Good k U N e s)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : Admissible allocation m ε sigma side e w) :
    (((localOrbit allocation m sigma e w).filter (fun v =>
      completeKeep allocation m ε (sigma side) sigma v ∧
        assigned allocation m ε sigma k U s (side, v) ≠ some (coarse allocation m sigma e))).card : ℝ) /
      ((localOrbit allocation m sigma e w).card : ℝ) ≤ 1 / N := by
  have ho : (side, orbitOf allocation m sigma e w) ∈ (data allocation m ε sigma).orbits e :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, rfl⟩
  have hh := good_failure_fraction_le allocation m ε sigma k U hAP N s e hg _ ho
  change (((passing allocation m sigma ε e (side, orbitOf allocation m sigma e w)).filter
      (fun v => assigned allocation m ε sigma k U s v ≠ some (coarse allocation m sigma e))).card : ℝ) /
    ((full allocation m sigma e (side, orbitOf allocation m sigma e w)).card : ℝ) ≤ 1 / N at hh
  rw [passing, Finset.filter_filter] at hh
  simp only [full_eq_tagged_localOrbit, Finset.filter_map, Finset.card_map] at hh
  rw [Finset.filter_congr_decidable] at hh
  exact hh

theorem localAssigned_iff (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (t : Triple (Pos (K := K) (tick := tick) allocation m sigma)) (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) :
    localAssigned allocation m sigma (physicalAssignment allocation m ε sigma k U s) t side w ↔
      assigned allocation m ε sigma k U s (sigma.symm side, w) = some t := by
  fin_cases side <;> rfl

theorem good_physical_local_failure_le (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (hg : (data allocation m ε sigma).Good k U N e s)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : Admissible allocation m ε sigma (sigma.symm side) e w) :
    (((localOrbit allocation m sigma e w).filter (fun v =>
      completeKeep allocation m ε side sigma v ∧
        ¬localAssigned allocation m sigma (physicalAssignment allocation m ε sigma k U s)
          (coarse allocation m sigma e) side v)).card : ℝ) /
      ((localOrbit allocation m sigma e w).card : ℝ) ≤ 1 / N := by
  simpa only [sigma.apply_symm_apply, localAssigned_iff] using
    good_local_failure_le allocation m ε sigma k U hAP N s e hg (sigma.symm side) w hw

theorem good_projected_failure_le (F : Type*) [CommRing F]
    (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m)
    (hg : (data allocation m ε sigma).Good k U N (projectTarget allocation m sigma e) s)
    (side : Fin 3) (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryRecovery.Used F allocation m ε e side w) :
    (((localOrbit allocation m sigma (projectTarget allocation m sigma e)
      (projectRaw allocation m sigma w)).filter (fun v =>
        completeKeep allocation m ε side sigma v ∧
          ¬localAssigned allocation m sigma (physicalAssignment allocation m ε sigma k U s)
            (coarse allocation m sigma (projectTarget allocation m sigma e)) side v)).card : ℝ) /
      ((localOrbit allocation m sigma (projectTarget allocation m sigma e)
        (projectRaw allocation m sigma w)).card : ℝ) ≤ 1 / N := by
  apply good_physical_local_failure_le allocation m ε sigma k U hAP N s _ hg
  exact AllFieldGroupAdmissible.used_project_admissible F allocation m ε sigma e
    (sigma.symm side) w (by simpa only [sigma.apply_symm_apply] using hw)

end MatrixMultiplication.AllFieldGroupAssignmentRetention

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_CWShapePhysicalPermutation
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.CWShapePhysicalPermutation

open MatrixMultiplication.Foundation CWStrands
open scoped BigOperators

variable {F : Type*} [CommRing F]

theorem shapeTensor_permute {P : Type*} [Fintype P]
    (σ : Equiv.Perm (Fin 3)) (g : Fin 3 → ℕ) (a : Fin 3 → P → Fin 7) :
    shapeTensor (F := F) P (g ∘ σ) (a (σ 0)) (a (σ 1)) (a (σ 2)) =
      shapeTensor P g (a 0) (a 1) (a 2) := by
  have hmask :
      (weight (a (σ 0)) = g (σ 0) ∧ weight (a (σ 1)) = g (σ 1) ∧
        weight (a (σ 2)) = g (σ 2)) ↔
      (weight (a 0) = g 0 ∧ weight (a 1) = g 1 ∧ weight (a 2) = g 2) := by
    constructor
    · rintro ⟨h0, h1, h2⟩
      have hs (s : Fin 3) : weight (a (σ s)) = g (σ s) := by
        fin_cases s <;> assumption
      exact ⟨by simpa using hs (σ.symm 0), by simpa using hs (σ.symm 1),
        by simpa using hs (σ.symm 2)⟩
    · rintro ⟨h0, h1, h2⟩
      have hs (s : Fin 3) : weight (a s) = g s := by
        fin_cases s <;> assumption
      exact ⟨hs (σ 0), hs (σ 1), hs (σ 2)⟩
  have hp := strand_permute (F := F) σ a
  simp only [shapeTensor, Function.comp_apply, hmask, hp]

end MatrixMultiplication.CWShapePhysicalPermutation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_GroupStatisticComplement
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldGroupStatisticComplement

open AllFieldHistory AllFieldHistoryChildLaws

theorem statistic_wordComplement {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (w : Fin (activeHalfLength h.val) → Fin 7) :
    statistic h.val (CWCompatibilityTransfer.wordComplement w) =
      AllFieldGroupOrbitData.complement h (statistic h.val w) := by
  rcases h with ⟨⟨⟨work, phi⟩, ht⟩, ho⟩
  cases work with
  | stageA a => exact CWCompleteStatistics.four_complement w
  | stageB b => exact CWCompleteStatistics.two_complement w
  | stageC c => rfl

end MatrixMultiplication.AllFieldGroupStatisticComplement

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_JointPopulationCWNonzero
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.branchPositionEquiv_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodePhysicalShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodeShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.initialExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.terminalExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.sidePermutation_refl _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.retarget_copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulationCWNonzero

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization JointCanonicalCW
open CWStrands InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [Field F]

omit [DecidableEq H] in
theorem class_half_products_nonzero
    (counts : H → Shape → ℕ) (leftLength rightLength : H → ℕ)
    (parentShape : H → Fin 3 → ℕ) (hleft : ∀ h, leftLength h ≤ 8)
    (hsupp : ∀ h u, 0 < counts h u → ∀ s, shapeNat u s ≤ parentShape h s)
    (e : Target counts)
    (x y z : RawPairs counts (Left leftLength) (Right rightLength))
    (hsource : sourceTensor counts (Left leftLength) (Right rightLength)
      (parentTensor (F := F) leftLength rightLength parentShape) x y z ≠ 0)
    (hx : coarseMask counts (Left leftLength) (Right rightLength)
      (coarse leftLength rightLength hleft) 0 e x)
    (hy : coarseMask counts (Left leftLength) (Right rightLength)
      (coarse leftLength rightLength hleft) 1 e y)
    (hz : coarseMask counts (Left leftLength) (Right rightLength)
      (coarse leftLength rightLength hleft) 2 e z)
    (h : H) (u : Shape) (hn : 0 < counts h u) :
    (∏ i : Class counts e h u,
      shapeTensor (F := F) (Fin (leftLength h)) (shapeNat u)
        (x h i.val).1 (y h i.val).1 (z h i.val).1) ≠ 0 ∧
    (∏ i : Class counts e h u,
      shapeTensor (F := F) (Fin (rightLength h)) (parentShape h - shapeNat u)
        (x h i.val).2 (y h i.val).2 (z h i.val).2) ≠ 0 := by
  change (∏ h' : H, ∏ i : Positions counts h',
    parentTensor (F := F) leftLength rightLength parentShape h'
      (x h' i) (y h' i) (z h' i)) ≠ 0 at hsource
  have hparent (i : Positions counts h) :
      parentTensor (F := F) leftLength rightLength parentShape h
        (x h i) (y h i) (z h i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp
      (Finset.prod_ne_zero_iff.mp hsource h (Finset.mem_univ h)) i (Finset.mem_univ i)
  have hhalves (i : Class counts e h u) :
      shapeTensor (F := F) (Fin (leftLength h)) (shapeNat u)
          (x h i.val).1 (y h i.val).1 (z h i.val).1 *
        shapeTensor (F := F) (Fin (rightLength h)) (parentShape h - shapeNat u)
          (x h i.val).2 (y h i.val).2 (z h i.val).2 ≠ 0 := by
    have hx' : coarse leftLength rightLength hleft 0 h (x h i.val) = u.1 := by
      simpa [shapeSide, i.property] using hx h i.val
    have hy' : coarse leftLength rightLength hleft 1 h (y h i.val) = u.2.1 := by
      simpa [shapeSide, i.property] using hy h i.val
    have hz' : coarse leftLength rightLength hleft 2 h (z h i.val) = u.2.2 := by
      simpa [shapeSide, i.property] using hz h i.val
    have hblock : block (Left leftLength) (Right rightLength)
        (parentTensor (F := F) leftLength rightLength parentShape)
        (coarse leftLength rightLength hleft) (h, u)
        (x h i.val) (y h i.val) (z h i.val) ≠ 0 := by
      simpa [block, hx', hy', hz'] using hparent i.val
    rw [block_eq_product leftLength rightLength parentShape hleft h u
      (hsupp h u hn)] at hblock
    exact hblock
  constructor
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (mul_ne_zero_iff.mp (hhalves i)).1
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (mul_ne_zero_iff.mp (hhalves i)).2

end MatrixMultiplication.JointPopulationCWNonzero

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_GroupAssignments
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupSourceSupport

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistorySupport
open AllFieldHistoryChildLaws AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData JointPopulation JointCanonicalization JointCanonicalCW
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

theorem masks_of_prepared (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (sigma : Placement)
    (x y z : GroupRaw (K := K) (tick := tick) allocation m sigma)
    (hT : groupPreparedSource F allocation m ε sigma x y z ≠ 0) :
    completeKeep allocation m ε 0 sigma x ∧
      completeKeep allocation m ε 1 sigma y ∧
      completeKeep allocation m ε 2 sigma z := by
  by_contra hn
  apply hT
  exact ite_eq_right hn

theorem raw_nonzero (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (sigma : Placement)
    (x y z : GroupRaw (K := K) (tick := tick) allocation m sigma)
    (hT : groupPreparedSource F allocation m ε sigma x y z ≠ 0) :
    groupRawSource F allocation m sigma x y z ≠ 0 := by
  have hm := masks_of_prepared F allocation m ε sigma x y z hT
  simpa only [groupPreparedSource, ExactRecovery.delete, ite_eq_left hm] using hT

theorem marginal_sideMask (allocation : Allocation) (m : ℕ) (side : Fin 3)
    (sigma : Placement) (w : GroupRaw (K := K) (tick := tick) allocation m sigma)
    (hm : marginal allocation m side sigma w) :
    JointCanonicalMixed.sideMask (groupCounts allocation m sigma)
      (fun h => activeHalfLength h.val) (fun h => activeHalfLength h.val)
      (fun h => AllFieldHistoryRecovery.halfLength_le_eight h.val) side w := by
  intro h a
  exact (hm h a).trans
    (marginal_population_eq (groupCounts allocation m sigma)
      (projectTarget allocation m sigma (canonicalTarget (activeCounts allocation m)))
      (canonicalTarget (groupCounts allocation m sigma)) h side a)

theorem marginal_source_nonzero (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (sigma : Placement)
    (x y z : GroupRaw (K := K) (tick := tick) allocation m sigma)
    (hT : groupPreparedSource F allocation m ε sigma x y z ≠ 0) :
    JointCanonicalMixed.maskedSource (F := F) (groupCounts allocation m sigma)
      (fun h => activeHalfLength h.val) (fun h => activeHalfLength h.val)
      (fun h => activeParentShape h.val) (fun _ => true)
      (fun h => AllFieldHistoryRecovery.halfLength_le_eight h.val) x y z ≠ 0 := by
  have hm := masks_of_prepared F allocation m ε sigma x y z hT
  have hx := marginal_sideMask allocation m 0 sigma x hm.1.1
  have hy := marginal_sideMask allocation m 1 sigma y hm.2.1.1
  have hz := marginal_sideMask allocation m 2 sigma z hm.2.2.1
  rw [JointCanonicalMixed.maskedSource, ExactRecovery.delete,
    ite_eq_left (And.intro hx (And.intro hy hz))]
  exact raw_nonzero F allocation m ε sigma x y z hT

theorem prepared_source_support (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (sigma : Placement)
    (x y z : GroupRaw (K := K) (tick := tick) allocation m sigma)
    (hT : groupPreparedSource F allocation m ε sigma x y z ≠ 0) :
    reorder sigma
      (ownWord allocation m sigma x, ownWord allocation m sigma y,
        ownWord allocation m sigma z) ∈ ambient allocation m sigma := by
  apply Finset.mem_image.mpr
  refine ⟨(ownWord allocation m sigma x, ownWord allocation m sigma y,
    ownWord allocation m sigma z), ?_, rfl⟩
  exact JointCanonicalMixed.maskedSource_support (groupCounts allocation m sigma)
    (fun h => activeHalfLength h.val) (fun h => activeHalfLength h.val)
    (fun h => activeParentShape h.val) (fun _ => true)
    (fun h => AllFieldHistoryRecovery.halfLength_le_eight h.val) x y z
    (marginal_source_nonzero F allocation m ε sigma x y z hT)

end MatrixMultiplication.AllFieldGroupSourceSupport

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupCompatibilityTransfer

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery AllFieldGroupOrbitData
open JointPopulation JointCanonicalization JointCanonicalCW CWStrands InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

theorem physical_coarseMask (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma)
    (hcoarse : reorder sigma (ownWord allocation m sigma (a 0),
      ownWord allocation m sigma (a 1), ownWord allocation m sigma (a 2)) =
        AllFieldGroupOrbitData.coarse allocation m sigma e)
    (s : Fin 3) :
    coarseMask (Counts allocation m sigma)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      groupCoarse s e (a s) := by
  have ht := reorder_injective sigma hcoarse
  intro h i
  have he := congrArg (fun t => tripleSide s t ⟨h, i⟩) ht
  fin_cases s <;> exact he

def halfShape {sigma : Placement} (right : Bool) (h : ActiveOrder K tick sigma)
    (u : JointPopulation.Shape) : Fin 3 → ℕ :=
  if right then activeParentShape h.val - shapeNat u else shapeNat u

def halfLaw {sigma : Placement} (right : Bool) (side : Fin 3) (h : ActiveOrder K tick sigma)
    (u : JointPopulation.Shape) : Statistic h.val → ℝ :=
  if right then rightLaw h.val u side else leftLaw h.val u side

theorem physical_half_product_nonzero (F : Type*) [Field F]
    (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma)
    (hraw : groupRawSource F allocation m sigma (a 0) (a 1) (a 2) ≠ 0)
    (hcoarse : reorder sigma (ownWord allocation m sigma (a 0),
      ownWord allocation m sigma (a 1), ownWord allocation m sigma (a 2)) =
        AllFieldGroupOrbitData.coarse allocation m sigma e)
    (right : Bool) (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape)
    (hu : 0 < Counts allocation m sigma h u) :
    (∏ i : Class (Counts allocation m sigma) e h u,
      shapeTensor (F := F) (Fin (activeHalfLength h.val)) (halfShape right h u)
        (if right then (a 0 h i.val).2 else (a 0 h i.val).1)
        (if right then (a 1 h i.val).2 else (a 1 h i.val).1)
        (if right then (a 2 h i.val).2 else (a 2 h i.val).1)) ≠ 0 := by
  have hsupp : ∀ (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape),
      0 < Counts allocation m sigma h u →
      ∀ s, shapeNat u s ≤ activeParentShape h.val s := by
    intro h u hu s
    exact jointCounts_support_le allocation m h.val.val u hu s
  have hsource : sourceTensor (F := F) (Counts (K := K) (tick := tick) allocation m sigma)
      (Left (fun h => activeHalfLength h.val)) (Right (fun h => activeHalfLength h.val))
      (parentTensor (F := F) (fun h : ActiveOrder K tick sigma => activeHalfLength h.val)
        (fun h : ActiveOrder K tick sigma => activeHalfLength h.val)
        (fun h : ActiveOrder K tick sigma => activeParentShape h.val))
      (a 0) (a 1) (a 2) ≠ 0 := by
    exact hraw
  have hp := JointPopulationCWNonzero.class_half_products_nonzero
    (Counts allocation m sigma) (fun h => activeHalfLength h.val)
    (fun h => activeHalfLength h.val) (fun h => activeParentShape h.val)
    (fun h => AllFieldHistoryRecovery.halfLength_le_eight h.val) hsupp e
    (a 0) (a 1) (a 2) hsource
    (physical_coarseMask allocation m sigma e a hcoarse 0)
    (physical_coarseMask allocation m sigma e a hcoarse 1)
    (physical_coarseMask allocation m sigma e a hcoarse 2) h u hu
  cases right
  · exact hp.1
  · exact hp.2

theorem priority_half_product_nonzero (F : Type*) [Field F]
    (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma)
    (hraw : groupRawSource F allocation m sigma (a 0) (a 1) (a 2) ≠ 0)
    (hcoarse : reorder sigma (ownWord allocation m sigma (a 0),
      ownWord allocation m sigma (a 1), ownWord allocation m sigma (a 2)) =
        AllFieldGroupOrbitData.coarse allocation m sigma e)
    (right : Bool) (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape)
    (hu : 0 < Counts allocation m sigma h u) :
    (∏ i : Class (Counts allocation m sigma) e h u,
      shapeTensor (F := F) (Fin (activeHalfLength h.val)) (halfShape right h u ∘ sigma)
        (if right then (a (sigma 0) h i.val).2 else (a (sigma 0) h i.val).1)
        (if right then (a (sigma 1) h i.val).2 else (a (sigma 1) h i.val).1)
        (if right then (a (sigma 2) h i.val).2 else (a (sigma 2) h i.val).1)) ≠ 0 := by
  have he := fun i : Class (Counts allocation m sigma) e h u =>
    CWShapePhysicalPermutation.shapeTensor_permute (F := F) sigma (halfShape right h u)
      (fun s => if right then (a s h i.val).2 else (a s h i.val).1)
  simp_rw [he]
  exact physical_half_product_nonzero F allocation m sigma e a hraw hcoarse right h u hu

theorem useful_half_window (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (s : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : groupIdealSide allocation m ε s sigma e w)
    (right : Bool) (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape)
    (hu : 0 < Counts allocation m sigma h u) :
    typeWindow (halfLaw right s h u) (AllFieldHistoryMasks.childWidth ε h.val)
      (fun i : Class (Counts allocation m sigma) e h u =>
        statistic h.val (if right then (w h i.val).2 else (w h i.val).1)) := by
  cases right
  · exact (hw.2 h u hu).1
  · exact (hw.2 h u hu).2

theorem own_coarse_guard (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma)
    (hcoarse : reorder sigma (ownWord allocation m sigma (a 0),
      ownWord allocation m sigma (a 1), ownWord allocation m sigma (a 2)) =
        AllFieldGroupOrbitData.coarse allocation m sigma e)
    (side : Fin 3) :
    tripleSide side (AllFieldGroupOrbitData.coarse allocation m sigma e) =
      ownWord allocation m sigma (a (sigma side)) := by
  rw [← hcoarse, tripleSide_reorder]
  generalize sigma side = s
  fin_cases s <;> rfl

theorem transferY (F : Type*) [Field F] (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma)
    (hraw : groupRawSource F allocation m sigma (a 0) (a 1) (a 2) ≠ 0)
    (hcoarse : reorder sigma (ownWord allocation m sigma (a 0),
      ownWord allocation m sigma (a 1), ownWord allocation m sigma (a 2)) =
        AllFieldGroupOrbitData.coarse allocation m sigma e)
    (huseX : groupIdealSide allocation m ε (sigma 0) sigma e (a (sigma 0))) :
    Compatible allocation m ε sigma 1 e (a (sigma 1)) := by
  refine ⟨own_coarse_guard allocation m sigma e a hcoarse 1, ?_⟩
  intro right h u hd
  apply JointPopulationCompatibility.shape_count_window_of_typeWindow
    (Counts allocation m sigma) e h u _ _ _
  intro hu
  have hz : halfShape right h u (sigma 2) = 0 := by
    cases right <;> simpa [designated, halfShape, shapeNat] using hd.2
  have hw := CWStrandCompatibility.zeroZ_transfer
    (fun _ : Class (Counts allocation m sigma) e h u => halfShape right h u ∘ sigma)
    (fun i => if right then (a (sigma 0) h i.val).2 else (a (sigma 0) h i.val).1)
    (fun i => if right then (a (sigma 1) h i.val).2 else (a (sigma 1) h i.val).1)
    (fun i => if right then (a (sigma 2) h i.val).2 else (a (sigma 2) h i.val).1)
    (priority_half_product_nonzero F allocation m sigma e a hraw hcoarse right h u hu)
    (statistic h.val) (complement h)
    (AllFieldGroupStatisticComplement.statistic_wordComplement h)
    (halfLaw right (sigma 0) h u) (AllFieldHistoryMasks.childWidth ε h.val)
    (fun _ => hz) (useful_half_window allocation m ε sigma (sigma 0) e _ huseX right h u hu)
  simpa [compatibilityLaw, halfLaw] using hw

theorem transferZ (F : Type*) [Field F] (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma)
    (hraw : groupRawSource F allocation m sigma (a 0) (a 1) (a 2) ≠ 0)
    (hcoarse : reorder sigma (ownWord allocation m sigma (a 0),
      ownWord allocation m sigma (a 1), ownWord allocation m sigma (a 2)) =
        AllFieldGroupOrbitData.coarse allocation m sigma e)
    (huseX : groupIdealSide allocation m ε (sigma 0) sigma e (a (sigma 0)))
    (huseY : groupIdealSide allocation m ε (sigma 1) sigma e (a (sigma 1))) :
    Compatible allocation m ε sigma 2 e (a (sigma 2)) := by
  refine ⟨own_coarse_guard allocation m sigma e a hcoarse 2, ?_⟩
  intro right h u hd
  apply JointPopulationCompatibility.shape_count_window_of_typeWindow
    (Counts allocation m sigma) e h u _ _ _
  intro hu
  have hz : halfShape right h u (sigma 0) * halfShape right h u (sigma 1) = 0 := by
    cases right <;> simpa [designated, halfShape, shapeNat] using hd.2
  have hp := priority_half_product_nonzero F allocation m sigma e a hraw hcoarse right h u hu
  by_cases hy : halfShape right h u (sigma 1) = 0
  · have hw := CWStrandCompatibility.zeroY_transfer
      (fun _ : Class (Counts allocation m sigma) e h u => halfShape right h u ∘ sigma)
      (fun i => if right then (a (sigma 0) h i.val).2 else (a (sigma 0) h i.val).1)
      (fun i => if right then (a (sigma 1) h i.val).2 else (a (sigma 1) h i.val).1)
      (fun i => if right then (a (sigma 2) h i.val).2 else (a (sigma 2) h i.val).1)
      hp (statistic h.val) (complement h)
      (AllFieldGroupStatisticComplement.statistic_wordComplement h)
      (halfLaw right (sigma 0) h u) (AllFieldHistoryMasks.childWidth ε h.val)
      (fun _ => hy) (useful_half_window allocation m ε sigma (sigma 0) e _ huseX right h u hu)
    have hy' : (if right then activeParentShape h.val (sigma 1) -
        (shapeSide (sigma 1) u).val else (shapeSide (sigma 1) u).val) = 0 := by
      cases right <;> simpa [halfShape, shapeNat] using hy
    simpa [compatibilityLaw, halfLaw, hy'] using hw
  · have hx : halfShape right h u (sigma 0) = 0 := (Nat.mul_eq_zero.mp hz).resolve_right hy
    have hw := CWStrandCompatibility.zeroX_transfer
      (fun _ : Class (Counts allocation m sigma) e h u => halfShape right h u ∘ sigma)
      (fun i => if right then (a (sigma 0) h i.val).2 else (a (sigma 0) h i.val).1)
      (fun i => if right then (a (sigma 1) h i.val).2 else (a (sigma 1) h i.val).1)
      (fun i => if right then (a (sigma 2) h i.val).2 else (a (sigma 2) h i.val).1)
      hp (statistic h.val) (complement h)
      (AllFieldGroupStatisticComplement.statistic_wordComplement h)
      (halfLaw right (sigma 1) h u) (AllFieldHistoryMasks.childWidth ε h.val)
      (fun _ => hx) (useful_half_window allocation m ε sigma (sigma 1) e _ huseY right h u hu)
    have hy' : (if right then activeParentShape h.val (sigma 1) -
        (shapeSide (sigma 1) u).val else (shapeSide (sigma 1) u).val) ≠ 0 := by
      cases right <;> simpa [halfShape, shapeNat] using hy
    simpa [compatibilityLaw, halfLaw, hy'] using hw

end MatrixMultiplication.AllFieldGroupCompatibilityTransfer

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupAssignments

open AllFieldHistory AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData AllFieldGroupAssignmentRetention JointCoarseHashing
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

theorem actualCompatible_own (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (t : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (v : Variable (K := K) (tick := tick) allocation m sigma)
    (hc : actualCompatible allocation m ε sigma t v) :
    tripleSide v.1 t = ownWord allocation m sigma v.2 := by
  obtain ⟨e, he, hc⟩ := hc
  rw [← he]
  exact hc.1

theorem physicalAssignment_coherent (F : Type*) [Field F]
    (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (sample : Sample (Pos (K := K) (tick := tick) allocation m sigma) k) :
    JointExtraction.Coherent (groupPreparedSource F allocation m ε sigma)
      (physicalAssignment allocation m ε sigma k U sample) := by
  intro x y z tx ty tz hT htx hty htz
  let a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma := (Matrix.vecCons (x) (Matrix.vecCons (y) (Matrix.vecCons (z) Matrix.vecEmpty)))
  let physicalTag : Fin 3 → Triple (Pos (K := K) (tick := tick) allocation m sigma) :=
    (Matrix.vecCons (tx) (Matrix.vecCons (ty) (Matrix.vecCons (tz) Matrix.vecEmpty)))
  let b : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma := fun r => a (sigma r)
  let tag : Fin 3 → Triple (Pos (K := K) (tick := tick) allocation m sigma) :=
    fun r => physicalTag (sigma r)
  have hphysical (r : Fin 3) :
      assigned allocation m ε sigma k U sample (sigma.symm r, a r) =
        some (physicalTag r) := by
    fin_cases r
    · exact htx
    · exact hty
    · exact htz
  have hassign (r : Fin 3) :
      assigned allocation m ε sigma k U sample (r, b r) = some (tag r) := by
    simpa only [b, tag, sigma.symm_apply_apply] using hphysical (sigma r)
  have hspec (r : Fin 3) :=
    assigned_spec allocation m ε sigma k U sample (r, b r) (tag r) (hassign r)
  let d := data (K := K) (tick := tick) allocation m ε sigma
  let hx := JointMaskedSelection.OrbitData.xFlag k U sample
  let hy := JointMaskedSelection.OrbitData.yFlag k U sample
  let hz := d.zFlag k U sample
  have heligible (r : Fin 3) :=
    (JointCoarseAssignment.mem_eligible_iff d.ambient d.actualTargets hx hy hz (tag r)).mp
      (hspec r).1
  let observed : Triple (Pos (K := K) (tick := tick) allocation m sigma) :=
    reorder sigma (ownWord allocation m sigma x,
      ownWord allocation m sigma y, ownWord allocation m sigma z)
  have hword (r : Fin 3) :
      ownWord allocation m sigma (a r) =
        tripleSide r (ownWord allocation m sigma x,
          ownWord allocation m sigma y, ownWord allocation m sigma z) := by
    fin_cases r <;> rfl
  have hobserved (r : Fin 3) : tripleSide r observed = tripleSide r (tag r) := by
    calc
      tripleSide r observed = ownWord allocation m sigma (b r) := by
        rw [show observed = reorder sigma (ownWord allocation m sigma x,
          ownWord allocation m sigma y, ownWord allocation m sigma z) from rfl,
          tripleSide_reorder]
        exact (hword (sigma r)).symm
      _ = tripleSide r (tag r) :=
        (actualCompatible_own allocation m ε sigma (tag r) (r, b r) (hspec r).2.1).symm
  have hobsX : observed.1 = (tag 0).1 := hobserved 0
  have hobsY : observed.2.1 = (tag 1).2.1 := hobserved 1
  have hobsZ : observed.2.2 = (tag 2).2.2 := hobserved 2
  have hsurvives : JointCoarseAssignment.survives hx hy hz observed := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hobsX]
      exact (heligible 0).2.2.1.1
    · rw [hobsY]
      exact (heligible 1).2.2.1.2.1
    · rw [hobsZ]
      exact (heligible 2).2.2.1.2.2
  have hsupport : observed ∈ d.ambient :=
    AllFieldGroupSourceSupport.prepared_source_support F allocation m ε sigma x y z hT
  have hobs : observed = tag 0 :=
    (heligible 0).2.2.2 observed hsupport hsurvives hobsX
  obtain ⟨e, he, huseX⟩ := (hspec 0).2.2.1
  have hcoarse : reorder sigma (ownWord allocation m sigma (a 0),
      ownWord allocation m sigma (a 1), ownWord allocation m sigma (a 2)) =
        coarse allocation m sigma e := hobs.trans he.symm
  have hraw : groupRawSource F allocation m sigma (a 0) (a 1) (a 2) ≠ 0 :=
    AllFieldGroupSourceSupport.raw_nonzero F allocation m ε sigma x y z hT
  have hcompY : actualCompatible allocation m ε sigma (tag 0) (1, b 1) :=
    ⟨e, he, AllFieldGroupCompatibilityTransfer.transferY F allocation m ε sigma e a
      hraw hcoarse huseX⟩
  have h01 : tag 0 = tag 1 := (hspec 1).2.2.2 (tag 0) (hspec 0).1 hcompY
  have huseY : groupIdealSide allocation m ε (sigma 1) sigma e (b 1) := by
    apply (actualUseful_coarse allocation m ε sigma e (1, b 1)).mp
    rw [he, h01]
    exact (hspec 1).2.2.1
  have hcompZ : actualCompatible allocation m ε sigma (tag 0) (2, b 2) :=
    ⟨e, he, AllFieldGroupCompatibilityTransfer.transferZ F allocation m ε sigma e a
      hraw hcoarse huseX huseY⟩
  have h02 : tag 0 = tag 2 := (hspec 2).2.2.2 (tag 0) (hspec 0).1 hcompZ
  have htag (r : Fin 3) : tag r = tag 0 := by
    fin_cases r
    · rfl
    · exact h01.symm
    · exact h02.symm
  have hphysicalTag (r : Fin 3) : physicalTag r = tag 0 := by
    simpa only [tag, sigma.apply_symm_apply] using htag (sigma.symm r)
  exact ⟨(hphysicalTag 0).trans (hphysicalTag 1).symm,
    (hphysicalTag 0).trans (hphysicalTag 2).symm⟩

end MatrixMultiplication.AllFieldGroupAssignments

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_GroupDegreeEnvelope
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldGroupDegreeEnvelope

open AllFieldHistory AllFieldGroupOrbitData Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

def variableDegree (allocation : Allocation) (m : ℕ) (width : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma) : ℕ :=
  ((data (K := K) (tick := tick) allocation m width sigma).orbits e).sup fun o =>
    ((data (K := K) (tick := tick) allocation m width sigma).passing e o).sup fun v =>
      ((data (K := K) (tick := tick) allocation m width sigma).competitors e o v).card

def uniformDegree (allocation : Allocation) (m : ℕ) (width : ℝ)
    (sigma : Placement) : ℕ :=
  Finset.univ.sup fun e : Targets (K := K) (tick := tick) allocation m sigma =>
    max ((data (K := K) (tick := tick) allocation m width sigma).eligibilityCompetitors e).card
      (variableDegree (K := K) (tick := tick) allocation m width sigma e)

end MatrixMultiplication.AllFieldGroupDegreeEnvelope

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_ScheduledPositivity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
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

def physicalYield (K : ℕ) (allocation : Allocation) : ℝ :=
  ∑ tick ∈ Finset.range (K + 2), ∑ sigma : Placement,
    Staggering.minCapacity (physicalTickCapacity allocation tick
      (workCapacity (K := K)) sigma)

def scheduledYield (K : ℕ) (allocation : Fin 3 → ℝ) : ℝ :=
  ∑ tick ∈ Finset.range (K + 2), Staggering.minCapacity
    (FiniteSchedule.tickCapacity K nativeLA nativeLB (nativeLC allocation) tick)

end MatrixMultiplication.AllFieldScheduledYield

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_GroupPairWindows
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
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
open AllFieldHistoryChildLaws AllFieldHistoryMasks AllFieldHistoryMaskLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupNativeLaws
open JointCompatibilityScaling JointCompatibilityRateLimit
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ} {sigma : Placement}

def base (allocation : Allocation) (sigma : Placement) (side : Fin 3) :=
  JointPopulationCompatibility.classCounts
    (Counts (K := K) (tick := tick) allocation 1 sigma) (sigma side)

def q (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c → ℝ :=
  JointPairMixtureControls.pairMixture (base (K := K) (tick := tick) allocation sigma side)
    (fun c u => supportedHalfLaw allocation false c.1.val u (sigma side))
    (fun c u => supportedHalfLaw allocation true c.1.val u (sigma side)) c

abbrev Positions (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (w : Raw (K := K) (tick := tick) allocation m sigma) :=
  JointPopulationCompatibility.ClassPos (Counts (K := K) (tick := tick) allocation m sigma)
    (ownWord (K := K) (tick := tick) allocation m sigma w)

def pairCounts (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (w : Raw (K := K) (tick := tick) allocation m sigma) :=
  JointPopulationCompatibility.statisticCounts (Counts (K := K) (tick := tick) allocation m sigma)
    (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
    (projectedStatistic (K := K) (tick := tick) sigma) (projectedStatistic (K := K) (tick := tick) sigma)
    (ownWord (K := K) (tick := tick) allocation m sigma w) w

def parentBase (allocation : Allocation) (h : ActiveOrder K tick sigma) : ℕ :=
  population allocation 1 (h.val.val.1.source, h.val.val.2)

def parentPair (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (h : ActiveOrder K tick sigma) (a : Statistic h.val × Statistic h.val) : ℝ :=
  (∑ u, (activeCounts allocation 1 h.val u : ℝ) *
    supportedHalfLaw allocation false h.val u (sigma side) a.1 *
    supportedHalfLaw allocation true h.val u (sigma side) a.2) / parentBase (K := K) (tick := tick) allocation h

def classMass (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) : ℝ :=
  (baseSize (base (K := K) (tick := tick) allocation sigma side) c : ℝ) / parentBase (K := K) (tick := tick) allocation c.1

def windowFactor (allocation : Allocation) (sigma : Placement) : ℝ :=
  1 + ∑ h : ActiveOrder K tick sigma, (parentBase (K := K) (tick := tick) allocation h : ℝ)

def parentStatistic (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (h : ActiveOrder K tick sigma)
    (j : JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) :
    Statistic h.val × Statistic h.val :=
  (statistic h.val (w h j).1, statistic h.val (w h j).2)

end MatrixMultiplication.AllFieldGroupPairWindows

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupCountRate
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupDegreeLaws

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupNativeLaws
open JointPopulation JointCanonicalization MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def nativeLaw (allocation : Allocation) (right : Bool) (side : Fin 3)
    (sigma : Placement) (c : Class (K := K) (tick := tick) sigma)
    (u : JointPopulation.Shape) : Symbol (K := K) (tick := tick) sigma c → ℝ :=
  supportedHalfLaw allocation right c.1.val u (sigma side)

def nativeCount (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) : ℕ :=
  JointPopulationCompatibility.compatibleTargetCount (Counts (K := K) (tick := tick) allocation m sigma)
    (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
    (projectedStatistic sigma) (projectedStatistic sigma)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (nativeLaw allocation false side sigma) (nativeLaw allocation true side sigma) χ
    (sigma side) (ownWord allocation m sigma w) w

end MatrixMultiplication.AllFieldGroupDegreeLaws

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupCountRate

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupDegreeLaws
open AllFieldGroupNativeLaws AllFieldGroupPairWindows
open JointCompatibilityControls JointCompatibilityScaling JointCompatibilityRateLimit
open JointPopulationCompatibility JointTypeCounts MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def nativeCompatibilityRate (allocation : Allocation) (sigma : Placement) (side : Fin 3) : ℝ :=
  compatibilityRate (base (K := K) (tick := tick) allocation sigma side)
    (q allocation sigma side)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (groupCap (base allocation sigma side) (classDesignated false side sigma)
      (nativeLaw allocation false side sigma) 0)
    (groupCap (base allocation sigma side) (classDesignated true side sigma)
      (nativeLaw allocation true side sigma) 0)

end MatrixMultiplication.AllFieldGroupCountRate

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupPairEntropy
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupPairEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldHistoryChildLaws AllFieldGroupOrbitData
open AllFieldGroupDegrees AllFieldGroupNativeLaws AllFieldGroupPairWindows
open JointCompatibilityScaling JointCompatibilityRateLimit JointPairClassWindows
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} {sigma : Placement}

def observedEntropy (h : ActiveOrder K tick sigma) (side : Fin 3) : ℝ :=
  if h.val.val.1.stage ≠ 2 then
    finiteEntropy (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass
  else finiteEntropy (JointPopulationRates.sideMass (orderLaw h).mass (sigma side))

end MatrixMultiplication.AllFieldGroupPairEntropy

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupProjectedEntropy
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointNativeGroupedEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section NativeSupport

variable {A : Type*} [Fintype A]

def ownWeight (support : List Shape) (priority : Placement) (position : Fin 3)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17)
    (i : SupportIndex support) : Fin 17 :=
  ⟨support[i.val] (priority position), hbound i⟩

def nativeGroup (support : List Shape) (priority : Placement) (position : Fin 3)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17) :
    SupportIndex support → SupportIndex support ⊕ Fin 17 :=
  singletonResidualGroup
    (fun i => AllFieldNativeCapacity.designated priority position support[i.val])
    (ownWeight support priority position hbound)

end NativeSupport

end MatrixMultiplication.JointNativeGroupedEntropy

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldNativeGroupedRates

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open JointNativeGroupedEntropy
open AllFieldNativeCapacity AllFieldPairConditionalEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def twoHalfConditionalCost {A : Type*} [Fintype A]
    (support : List Shape) (s : Shape) (priority : Placement) (position : Fin 3)
    (q : Shape → A → ℝ) (law : FiniteLaw (SupportIndex support))
    (weight : SupportIndex support → Fin 17) : ℝ :=
  ∑ k : Fin 17, (law.map weight).mass k *
    (JointCompatibilityIncidence.groupedEntropy (law.conditional weight k).mass
      (JointCompatibilityIncidence.designatedGroup (fun i =>
        AllFieldNativeCapacity.designated priority position support[i.val]))
      (fun i => q support[i.val]) +
    JointCompatibilityIncidence.groupedEntropy (law.conditional weight k).mass
      (JointCompatibilityIncidence.designatedGroup (fun i =>
        AllFieldNativeCapacity.designated priority position (complement s support[i.val])))
      (fun i => q (complement s support[i.val])))

end MatrixMultiplication.AllFieldNativeGroupedRates

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupProjectedEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldGroupDegrees
open AllFieldGroupNativeLaws AllFieldGroupPairWindows AllFieldGroupDegreeLaws
open JointCompatibilityScaling JointCompatibilityRateLimit JointCompatibilityControls
open JointCompatibilityIncidence JointGroupedEntropyEmbedding
open AllFieldGroupBranchDesignation AllFieldNativeGroupedRates
open AllFieldScheduledYield AllFieldGroupPairEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} {sigma : Placement}

def maskedBranchMass (h : ActiveOrder K tick sigma) (side : Fin 3) (k : Fin 17)
    (b : h.val.val.1.Branch) : ℝ :=
  if nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side) b = k
  then (branchLaw h.val.val.1).mass b else 0

def branchHalfLaw (w : Work K) (right : Bool) (side : Fin 3)
    (b : w.Branch) (a : w.Statistic) : ℝ :=
  (w.childLaw (halfShape w.parentShape (w.splitShape b) right) (w.priority side) a : ℝ)

def branchConditionalCost (w : Work K) (side : Fin 3) : ℝ :=
  ∑ k : Fin 17,
    ((branchLaw w).map (nativeSplitWeightCode w (w.priority side))).mass k *
      (groupedEntropy ((branchLaw w).conditional
          (nativeSplitWeightCode w (w.priority side)) k).mass
        (designatedGroup (nativeBranchDesignated w false side)) (branchHalfLaw w false side) +
      groupedEntropy ((branchLaw w).conditional
          (nativeSplitWeightCode w (w.priority side)) k).mass
        (designatedGroup (nativeBranchDesignated w true side)) (branchHalfLaw w true side))

end MatrixMultiplication.AllFieldGroupProjectedEntropy

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_GroupNativeDegreeBound
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupNativeDegreeBound

open AllFieldHistory AllFieldActiveLaws AllFieldActiveCapacity
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupDegreeLaws
open AllFieldGroupCountRate AllFieldGroupPairWindows AllFieldGroupPairEntropy
open AllFieldGroupProjectedEntropy JointCompatibilityRateLimit
open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def maxNativeDegree (allocation : Allocation) (sigma : Placement) : ℝ :=
  max (orderNativeDegree (K := K) (tick := tick) allocation sigma 0)
    (max (orderNativeDegree (K := K) (tick := tick) allocation sigma 1)
      (orderNativeDegree (K := K) (tick := tick) allocation sigma 2))

end MatrixMultiplication.AllFieldGroupNativeDegreeBound

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_StageCTerminalRates
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldStageCTerminalRates

open AllFieldHistory AllFieldParameters CWStageCProducts
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

def interiorS2 : ℝ :=
  (positiveSecond.map (fun t =>
    (((below t).filter positive).map (fun u =>
      2 * (secondMass t : ℝ) * (stageBLaw t u : ℝ) *
        (2 - (binaryParameter t u : ℝ)) * Real.log 5)).sum)).sum

end MatrixMultiplication.AllFieldStageCTerminalRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_ZeroHistorySums
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldZeroHistorySums

open AllFieldHistory AllFieldParameters AllFieldTerminalStatisticLaws
open AllFieldTerminalRates AllFieldStageCTerminalRates
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def zeroRate {K : ℕ} : TerminalZero K → ℝ
  | .inl h => AllFieldZeroLeafRates.fourRate (aShape h.1.val)
  | .inr h => statisticRate (binaryParameter (bParent h) (bShape h.1.val)) (bWeight h)

end MatrixMultiplication.AllFieldZeroHistorySums

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_ConstructionLabels
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false
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

theorem card_selected_product (allocation : Allocation) (δ : ℝ) (m : ℕ) :
    Fintype.card (SelectedLabels (K := K) allocation δ m) =
      (∏ slot : Slot K, FloorExponentialRates.count (selectionRate allocation δ slot) m) := by
  rw [card_selected]
  simp [Slot, initialCount, groupCount, Fintype.prod_sum_type, Fintype.prod_prod_type]

theorem selected_pos (allocation : Allocation) (δ : ℝ)
    (hδ : ∀ slot : Slot K, δ ≤ (denominator (K := K) allocation : ℝ) *
      capacity allocation slot) (m : ℕ) :
    0 < Fintype.card (SelectedLabels (K := K) allocation δ m) := by
  rw [card_selected_product]
  exact Finset.prod_pos fun slot _ =>
    FloorExponentialRates.count_pos (sub_nonneg.mpr (hδ slot)) m

end MatrixMultiplication.AllFieldConstructionRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ConstructionRates
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldConstructionRates

open MatrixMultiplication.Foundation AllFieldHistory Filter
open scoped BigOperators Topology Classical

variable {K : ℕ}

abbrev Copies (allocation : Allocation) (ε : ℝ) (m : ℕ) :=
  ∀ tick : Fin (K + 2), InverseLinearRecovery.MaskRectangles
    (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick.val) allocation ε m)

end MatrixMultiplication.AllFieldConstructionRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_RateLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldRateLimit

open Filter
open scoped Topology

variable {F : Type*} [Field F]

structure HasRates (W : ℕ → AllFieldWitness F) (scale : ℕ → ℝ)
    (Y S R : ℝ) : Prop where
  scale_positive : ∀ᶠ n in atTop, 0 < scale n
  yield_limit : Tendsto (fun n => Real.log ((W n).multiplicity : ℝ) / scale n) atTop (𝓝 Y)
  volume_limit : Tendsto (fun n => Real.log ((W n).volume : ℝ) / scale n) atTop (𝓝 S)
  rank_limit : Tendsto (fun n => Real.log ((W n).rankBound : ℝ) / scale n) atTop (𝓝 R)

end MatrixMultiplication.AllFieldRateLimit

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_Subdivision
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

omit [DecidableEq I] [∀ index, DecidableEq (P index)] in
theorem statisticWindow_concatenate_at {A X Q : Type*}
    [Fintype A] [DecidableEq A] [Fintype Q] [DecidableEq Q]
    (e : Q ≃ (Σ i, P i)) (statistic : X → A)
    (ν : A → ℝ) (η : ℝ) (ηpart : I → ℝ)
    (hη : 0 ≤ η) (hwidth : ∀ i, ηpart i ≤ η)
    (hsize : 0 < Fintype.card (Σ i, P i)) (w : ∀ i, P i → X)
    (hw : partWindows P ν ηpart (fun i => statistic ∘ w i)) :
    typeWindow ν η (statistic ∘ (concatenate P w ∘ e)) := by
  change typeWindow ν η ((statistic ∘ concatenate P w) ∘ e)
  exact (typeWindow_reindex ν η _ e).mpr
    (statisticWindow_concatenate P statistic ν η ηpart hη hwidth hsize w hw)

end MatrixMultiplication.Subdivision

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_GroupSelection
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
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

def orbitPrefactor (allocation : Allocation) (sigma : Placement) : ℕ :=
  3 * (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick)
    allocation + 1) ^ AllFieldGroupOrbitCount.groupDegree K tick sigma

end MatrixMultiplication.AllFieldGroupSelection

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryIteration
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

theorem afterB_mask_of_part_masks (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (h : BPositive K) (phi : Placement) (side : Fin 3)
    (w : ∀ i : Fin 3, HistoryWord allocation dilation (.partC (h, i), phi))
    (hw : ∀ i, residentMask allocation dilation ε (.partC (h, i), phi) side (w i)) :
    residentMask allocation dilation ε (.afterB h.val, phi) side
      (fun j => w (bSubdivisionPositionEquiv allocation dilation h phi j).1
        (bSubdivisionPositionEquiv allocation dilation h phi j).2) := by
  intro hp
  let P : Fin 3 → Type := fun i =>
    Fin (population allocation dilation (.partC (h, i), phi))
  let e := bSubdivisionPositionEquiv allocation dilation h phi
  have hsize : 0 < Fintype.card (Σ i, P i) := by
    rw [← Fintype.card_congr e]
    simpa only [Fintype.card_fin] using hp
  have hwidth : ∀ _ : Fin 3, ε / 256 ≤ ε / 128 := by
    intro i
    linarith
  have hparts : Subdivision.partWindows P
      (residentLaw (.afterB h.val, phi) side) (fun _ => ε / 256)
      (fun i => CWCompleteStatistics.twoStatistic ∘ w i) := by
    intro i hi
    have hi' : 0 < population allocation dilation (.partC (h, i), phi) := by
      simpa only [P, Fintype.card_fin] using hi
    exact hw i hi'
  exact Subdivision.statisticWindow_concatenate_at
    (A := ResidentStatistic (.afterB h.val)) P e CWCompleteStatistics.twoStatistic
    (residentLaw (.afterB h.val, phi) side) (ε / 128) (fun _ => ε / 256)
    (div_nonneg hε (by norm_num)) hwidth hsize w hparts

theorem producedChildWord_mask (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h))
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool) :
    residentMask allocation dilation ε (h.val.1.child b right, h.val.2) side
      (producedChildWord allocation dilation x h b right) := by
  rcases h with ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA parent => exact hx ⟨(.afterA ⟨parent, b, right⟩, phi), ht.symm⟩
  | stageB parent =>
      by_cases hp : positive (bShape (⟨parent, b, right⟩ : AfterB K)) = true
      · simp only [producedChildWord]
        erw [dite_eq_left hp]
        exact afterB_mask_of_part_masks allocation dilation hε
          ⟨⟨parent, b, right⟩, hp⟩ phi side
          (fun i => x ⟨(.partC (⟨⟨parent, b, right⟩, hp⟩, i), phi), ht.symm⟩)
          (fun i => hx ⟨(.partC (⟨⟨parent, b, right⟩, hp⟩, i), phi), ht.symm⟩)
      · simp only [producedChildWord]
        erw [dite_eq_right hp]
        exact hx (⟨(.afterB ⟨parent, b, right⟩, phi), ht.symm, hp⟩ : Produced K tick)
  | stageC parent => trivial

theorem producedHalfWord_eq_childHalfWord (allocation : Allocation) (dilation : ℕ)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool) :
    producedHalfWord allocation dilation x h b right =
      childHalfWord allocation dilation h b right
        (producedChildWord allocation dilation x h b right) := by
  rcases h with ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA parent => rfl
  | stageB parent =>
      by_cases hp : positive (bShape (⟨parent, b, right⟩ : AfterB K)) = true
      · funext i
        let g : BPositive K := ⟨⟨parent, b, right⟩, hp⟩
        let part := bSubdivisionPositionEquiv allocation dilation g phi
          (halfPosition allocation dilation (.stageB parent, phi) b right i)
        let q : ProducedPositions (K := K) (tick := tick) allocation dilation :=
          ⟨⟨(.partC (g, part.1), phi), ht.symm⟩, part.2⟩
        have hq : (producedPositionEquiv allocation dilation).symm
            ⟨⟨(.stageB parent, phi), ht⟩, b, right, i⟩ = q := by
          simp only [producedPositionEquiv, Equiv.symm, Equiv.coe_fn_mk,
            splitToProduced, dite_eq_left hp]
          rfl
        simp only [producedHalfWord, producedChildWord]
        erw [dite_eq_left hp]
        exact splitWord_eq_of_position allocation dilation x
            ⟨⟨(.stageB parent, phi), ht⟩, b, right, i⟩ q hq rfl
      · funext i
        let q : ProducedPositions (K := K) (tick := tick) allocation dilation :=
          ⟨⟨(.afterB ⟨parent, b, right⟩, phi), ht.symm, hp⟩,
            halfPosition allocation dilation (.stageB parent, phi) b right i⟩
        have hq : (producedPositionEquiv allocation dilation).symm
            ⟨⟨(.stageB parent, phi), ht⟩, b, right, i⟩ = q := by
          simp only [producedPositionEquiv, Equiv.symm, Equiv.coe_fn_mk,
            splitToProduced, dite_eq_right hp]
          rfl
        simp only [producedHalfWord, producedChildWord]
        erw [dite_eq_right hp]
        exact splitWord_eq_of_position allocation dilation x
            ⟨⟨(.stageB parent, phi), ht⟩, b, right, i⟩ q hq rfl
  | stageC parent => rfl

theorem producedHalfWord_window (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h))
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool)
    (hp : 0 < branchPopulation allocation dilation h.val b) :
    typeWindow (fun a => (h.val.1.childLaw
        (halfShape h.val.1.parentShape (h.val.1.splitShape b) right)
        (h.val.2.symm side) a : ℝ)) (nativeChildWidth ε h)
      (h.val.1.statistic ∘ producedHalfWord allocation dilation x h b right) := by
  rw [producedHalfWord_eq_childHalfWord]
  exact childHalfWord_window allocation dilation hε side h b right _
    (producedChildWord_mask allocation dilation hε side x hx h b right) hp

theorem regroupBranch_window (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h))
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool)
    (hp : 0 < branchPopulation allocation dilation h.val b) :
    typeWindow (fun a => (placedChildLawRat h.val (branchShape h.val b) side right a : ℝ))
      (nativeChildWidth ε h)
      (statistic h ∘ (if right then (regroupWords allocation dilation x).right
        (h, branchShape h.val b) else (regroupWords allocation dilation x).left
        (h, branchShape h.val b))) := by
  apply (Subdivision.typeWindow_reindex _ _ _ (branchClassEquiv allocation dilation h b)).mp
  have he : (statistic h ∘ (if right then (regroupWords allocation dilation x).right
      (h, branchShape h.val b) else (regroupWords allocation dilation x).left
      (h, branchShape h.val b))) ∘ branchClassEquiv allocation dilation h b =
        h.val.1.statistic ∘ producedHalfWord allocation dilation x h b right := by
    funext i
    have hi := regroupWords_branch allocation dilation x h b right i
    cases right <;> exact congrArg h.val.1.statistic hi
  rw [he]
  simpa only [placedChildLawRat_branchShape] using
    producedHalfWord_window allocation dilation hε side x hx h b right hp

theorem canonicalWindows_of_produced_masks (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h)) :
    HistorySymmetry.childWindows
      (fun c : Active K tick × JointPopulation.Shape => statistic c.1)
      (fun c : Active K tick × JointPopulation.Shape => statistic c.1)
      (activeLaw (activeCounts allocation dilation) (fun c => leftLaw c.1 c.2 side))
      (activeLaw (activeCounts allocation dilation) (fun c => rightLaw c.1 c.2 side))
      (activeWidth (activeCounts allocation dilation) (fun c => nativeChildWidth ε c.1))
      (activeWidth (activeCounts allocation dilation) (fun c => nativeChildWidth ε c.1))
      (regroupWords allocation dilation x) := by
  rintro ⟨h, u⟩
  by_cases hp : 0 < activeCounts allocation dilation h u
  · obtain ⟨b, hb, hpos⟩ := shapeCounts_positive (branchShape h.val)
      (branchPopulation allocation dilation h.val) u hp
    subst u
    have hl := regroupBranch_window allocation dilation hε side x hx h b false hpos
    have hr := regroupBranch_window allocation dilation hε side x hx h b true hpos
    rw [activeLaw_of_pos (activeCounts allocation dilation)
      (fun c => leftLaw c.1 c.2 side) (h, branchShape h.val b) hp,
      activeLaw_of_pos (activeCounts allocation dilation)
      (fun c => rightLaw c.1 c.2 side) (h, branchShape h.val b) hp]
    simp only [activeWidth, ite_eq_left hp]
    exact ⟨hl, hr⟩
  · have hz : activeCounts allocation dilation h u = 0 := Nat.eq_zero_of_not_pos hp
    simp only [activeLaw, activeWidth, typeWindow, empiricalLaw,
      Fintype.card_fin, hz, Nat.cast_zero, div_zero, sub_zero, abs_zero,
      le_refl, implies_true, and_self, Nat.lt_irrefl, ite_false, if_false]

end MatrixMultiplication.AllFieldHistoryProducedMasks

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryProducedMasks

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws AllFieldHistoryMasks InheritedMasks
open JointCanonicalization
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem childWindows_of_produced_masks (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h)) :
    AllFieldHistoryMasks.childWindows allocation dilation ε side
      (regroupWords allocation dilation x) :=
  canonicalWindows_of_produced_masks allocation dilation hε side x hx

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

theorem delete_pulled (F : Type*) [Field F] {ε : ℝ} (hε : 0 ≤ ε) :
    ExactRecovery.delete (pulled (K := K) (tick := tick) allocation m F ε)
      (passes allocation m ε 0) (passes allocation m ε 1) (passes allocation m ε 2) =
    AllFieldHistoryRegrouping.producedTensor (K := K) (tick := tick) allocation m F ε := by
  rw [producedTensor_eq_delete]
  funext x y z
  by_cases hp : passes allocation m ε 0 x ∧ passes allocation m ε 1 y ∧
      passes allocation m ε 2 z
  · simp only [ExactRecovery.delete, ite_eq_left hp]
    unfold pulled Tensor.pullback
    rw [canonical_eq_delete]
    have hx := childWindows_of_produced_masks allocation m hε 0 x hp.1
    have hy := childWindows_of_produced_masks allocation m hε 1 y hp.2.1
    have hz := childWindows_of_produced_masks allocation m hε 2 z hp.2.2
    unfold ExactRecovery.delete
    rw [ite_eq_left ⟨hx, hy, hz⟩]
    exact regroup_coefficient allocation m x y z
  · simp only [ExactRecovery.delete, ite_eq_right hp]

def pullbackMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (AllFieldHistoryRecovery.canonical F (K := K) (tick := tick) allocation m ε)
      (pulled (K := K) (tick := tick) allocation m F ε) := by
  apply LocalMap.ofExists
  exact ⟨_, _, _, (Tensor.pullback_eq_restrict
    (regroupWords (K := K) (tick := tick) allocation m)
    (regroupWords (K := K) (tick := tick) allocation m)
    (regroupWords (K := K) (tick := tick) allocation m) _).symm⟩

def map (F : Type*) [Field F] {ε : ℝ} (hε : 0 ≤ ε) :
    LocalMap (AllFieldHistoryRecovery.canonical F (K := K) (tick := tick) allocation m ε)
      (AllFieldHistoryRegrouping.producedTensor (K := K) (tick := tick) allocation m F ε) := by
  let first := pullbackMap (K := K) (tick := tick) allocation m F ε
  let last := LocalMap.delete (pulled (K := K) (tick := tick) allocation m F ε)
    (passes allocation m ε 0) (passes allocation m ε 1) (passes allocation m ε 2)
  let combined := first.comp last
  exact ⟨combined.x, combined.y, combined.z,
    combined.coefficient.trans (delete_pulled allocation m F hε)⟩

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

abbrev AmbientTag (sigma : Placement) :=
  JointCoarseHashing.Triple
    (AllFieldGroupOrbitData.Pos (K := K) (tick := tick) allocation m sigma)

local instance tagsDecidableEq (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    DecidableEq (Tags allocation m ε slack chosen) := Classical.decEq _

instance ambientTagFintype (sigma : Placement) :
    Fintype (AmbientTag (K := K) (tick := tick) allocation m sigma) :=
  coarseTripleFintype (AllFieldGroupOrbitData.Pos (K := K) (tick := tick) allocation m sigma)

instance ambientTagsFintype :
    Fintype (∀ sigma, AmbientTag (K := K) (tick := tick) allocation m sigma) := inferInstance

def select (chosen : Choices (K := K) (tick := tick) allocation m ε slack)
    (j : Tags allocation m ε slack chosen) :
    ∀ sigma, AmbientTag (K := K) (tick := tick) allocation m sigma :=
  fun sigma => AllFieldGroupOrbitData.coarse allocation m sigma (j sigma).val

theorem select_injective
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Function.Injective (select allocation m ε slack chosen) := by
  intro j k h
  funext sigma
  apply Subtype.ext
  exact AllFieldGroupOrbitData.coarse_injective allocation m sigma (congrFun h sigma)

def targets (chosen : Choices (K := K) (tick := tick) allocation m ε slack)
    (j : Tags allocation m ε slack chosen) :
    AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m :=
  joinGroupTargets (activeCounts allocation m) (fun sigma => (j sigma).val)

def assignments (chosen : Choices (K := K) (tick := tick) allocation m ε slack)
    (sigma : Placement) :=
  AllFieldGroupAssignmentRetention.physicalAssignment allocation m ε sigma
    (JointOrdinarySelection.hashLevel
      (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
    (JointOrdinarySelection.hashSet
      (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
    (chosen sigma).sample

def assignment (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :=
  groupedAssignment allocation m (AmbientTag (K := K) (tick := tick) allocation m)
    (assignments allocation m ε slack chosen)

theorem coherent (F : Type*) [Field F]
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    JointExtraction.Coherent
      (AllFieldHistorySource.preparedSource (K := K) (tick := tick) allocation m F ε)
      (assignment allocation m ε slack chosen) := by
  apply AllFieldHistorySource.groupedAssignment_coherent allocation m F ε
  intro sigma
  exact AllFieldGroupAssignments.physicalAssignment_coherent F allocation m ε sigma
    _ _ (chosen sigma).sample

theorem repair (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack)
    (j : Tags allocation m ε slack chosen) :
    InverseLinearRecovery.RecoveredBy
      (AllFieldHistoryRecovery.ideal F allocation m ε (targets allocation m ε slack chosen j))
      (JointExtraction.branch
        (AllFieldHistorySource.preparedSource (K := K) (tick := tick) allocation m F ε)
        (assignment allocation m ε slack chosen) (select allocation m ε slack chosen j))
      (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m) := by
  rw [AllFieldHistorySource.preparedSource_eq_delete]
  apply repair_grouped F allocation hε hm
    (AmbientTag (K := K) (tick := tick) allocation m)
    (assignments allocation m ε slack chosen)
    (select allocation m ε slack chosen j) (fun sigma => (j sigma).val)
  · intro sigma w hw
    have hs := AllFieldGroupAssignmentRetention.assigned_some_idealSide
      allocation m ε sigma _ _ (chosen sigma).sample (j sigma).val (sigma.symm 0, w) hw
    simpa only [Equiv.apply_symm_apply] using hs
  · intro sigma w hw
    have hs := AllFieldGroupAssignmentRetention.assigned_some_idealSide
      allocation m ε sigma _ _ (chosen sigma).sample (j sigma).val (sigma.symm 1, w) hw
    simpa only [Equiv.apply_symm_apply] using hs
  · intro sigma w hw
    have hs := AllFieldGroupAssignmentRetention.assigned_some_idealSide
      allocation m ε sigma _ _ (chosen sigma).sample (j sigma).val (sigma.symm 2, w) hw
    simpa only [Equiv.apply_symm_apply] using hs
  · intro side w hw sigma
    have hg := (chosen sigma).good (j sigma).val (j sigma).property
    have hh := AllFieldGroupAssignmentRetention.good_projected_failure_le F
      allocation m ε sigma _ _
      (JointOrdinarySelection.hashSet_AP (selectionHashRate allocation sigma slack) m)
      (m : ℝ) (chosen sigma).sample (targets allocation m ε slack chosen j)
      (by simpa only [targets, project_joinGroupTargets] using hg) side w hw
    simp only [targets, project_joinGroupTargets, assignments, select] at hh ⊢
    exact hh

def canonicalMap (F : Type*) [Field F]
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m) :
    LocalMap (AllFieldHistoryRecovery.ideal F allocation m ε e)
      (AllFieldHistoryRecovery.canonical (K := K) (tick := tick) F allocation m ε) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (AllFieldHistoryRecovery.coordinates allocation m e).symm
    (AllFieldHistoryRecovery.coordinates allocation m e).symm
    (AllFieldHistoryRecovery.coordinates allocation m e).symm _).symm.trans ?_⟩
  funext x y z
  change AllFieldHistoryRecovery.ideal F allocation m ε e _ _ _ = _
  rw [AllFieldHistoryRecovery.ideal_coordinates]
  simp only [Equiv.apply_symm_apply]

def activeExecution (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Execution
      (AllFieldHistoryRegrouping.activeTensor (K := K) (tick := tick) allocation m F ε)
      (Tensor.directSum (fun _ : Tags allocation m ε slack chosen =>
        AllFieldHistoryRegrouping.producedTensor (K := K) (tick := tick) allocation m F ε)) := by
  let prepared := (Execution.initial
    (AllFieldHistoryRegrouping.activeTensor (K := K) (tick := tick) allocation m F ε)).restrict _
      (AllFieldHistorySource.preparedMap (K := K) (tick := tick) allocation m F ε)
  let repaired := prepared.extractSelectedAndRepair
    (assignment allocation m ε slack chosen) (coherent allocation m ε slack F chosen)
    (select allocation m ε slack chosen) (select_injective allocation m ε slack chosen)
    (fun j => AllFieldHistoryRecovery.ideal F allocation m ε (targets allocation m ε slack chosen j))
    (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m)
    (repair allocation m ε slack F hε hm chosen)
  let canonical := repaired.restrict _ (LocalMap.directSum _ _
    (fun j => canonicalMap allocation m ε F (targets allocation m ε slack chosen j)))
  exact canonical.restrict _
    ((AllFieldHistoryProduced.map (K := K) (tick := tick) allocation m F hε.le).parallelCopies _)

def execution (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Execution (stateTensor F (K := K) allocation m ε tick)
      (Tensor.directSum (fun _ : Tags allocation m ε slack chosen =>
        stateTensor F (K := K) allocation m ε (tick + 1))) :=
  AllFieldHistoryTickCarry.liftExecution (K := K) (tick := tick) allocation m F ε
    (activeExecution allocation m ε slack F hε hm chosen)

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

variable {K : ℕ} (allocation : Allocation) (m : ℕ) (ε slack : ℝ)

variable (F : Type*) [Field F] (hε : 0 < ε)
    (hm : ∀ t : Fin (K + 2),
      AllFieldHistoryRecovery.minimumDilation (K := K) (tick := t.val) allocation ε ≤ m)
    (chosen : ScheduleChoices (K := K) allocation m ε slack)
    {InitialTag : Type} [Fintype InitialTag]
    (start : Execution (cwSource F K (populationLength (K := K) allocation m))
      (Tensor.directSum (fun _ : InitialTag => stateTensor F (K := K) allocation m ε 0)))

def run : (n : ℕ) → (hn : n ≤ K + 2) →
    Execution (cwSource F K (populationLength (K := K) allocation m))
      (Tensor.directSum (fun _ : Labels allocation m ε slack InitialTag chosen n hn =>
        stateTensor F (K := K) allocation m ε n))
  | 0, _ => start
  | n + 1, hn =>
      let step := AllFieldHistoryTick.execution allocation m ε slack F hε
        (hm ⟨n, hn⟩) (chosen ⟨n, hn⟩)
      let operation := Execution.branchOperation
        (stateTensor F (K := K) allocation m ε n)
        (stateTensor F (K := K) allocation m ε (n + 1))
        (run n (Nat.le_of_succ_le hn)) step.copies_positive step.map
      retarget operation (by
        funext x y z
        simp only [Tensor.directSum]
        split_ifs <;> first | rfl | contradiction)

def execution :
    Execution (cwSource F K (populationLength (K := K) allocation m))
      (Tensor.directSum (fun _ : Tags allocation m ε slack InitialTag chosen =>
        stateTensor F (K := K) allocation m ε (K + 2))) :=
  run allocation m ε slack F hε hm chosen start (K + 2) le_rfl

end MatrixMultiplication.AllFieldHistoryIteration

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_OrderedLimits
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldConstructionData

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ}

variable (allocation : Allocation) (dilation : ℕ) (width slack : ℝ)

def execution (F : Type*) [Field F] (hwidth : 0 < width)
    (data : Data (K := K) allocation dilation width slack) :
    Execution (cwSource F K (populationLength (K := K) allocation dilation))
      (Tensor.directSum (fun _ : Tags allocation dilation width slack data =>
        stateTensor F (K := K) allocation dilation width (K + 2))) :=
  AllFieldHistoryIteration.execution allocation dilation width slack F hwidth
    data.threshold data.groups
    (AllFieldInitialChoice.execution allocation dilation slack data.initial F width)

theorem tags_pos
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation dilation width slack) :
    0 < Fintype.card (Tags allocation dilation width slack data) := by
  rw [card_tags]
  exact AllFieldConstructionRates.selected_pos allocation slack hslack dilation

variable {F : Type*} [Field F] (m : ℕ)

def witness (hm : 0 < m) (hwidth : 0 < width)
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K m) width slack) : AllFieldWitness F :=
  AllFieldFinishedWitness.witness allocation m hm hwidth.le
    (execution allocation (AllFieldTerminalRates.terminalDilation K m) width slack F hwidth data)
    (tags_pos allocation (AllFieldTerminalRates.terminalDilation K m) width slack hslack data)

@[simp] theorem witness_volume (hm : 0 < m) (hwidth : 0 < width)
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K m) width slack) :
    (witness (F := F) allocation width slack m hm hwidth hslack data).volume =
      AllFieldTerminalRates.terminalVolume (K := K) allocation m :=
  AllFieldFinishedWitness.witness_volume _ _ _ _ _ _

@[simp] theorem witness_multiplicity (hm : 0 < m) (hwidth : 0 < width)
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K m) width slack) :
    (witness (F := F) allocation width slack m hm hwidth hslack data).multiplicity =
      Fintype.card (AllFieldConstructionRates.SelectedLabels
        (K := K) allocation slack (AllFieldTerminalRates.terminalDilation K m)) := by
  change Fintype.card (Tags _ _ _ _ data) = _
  exact card_tags _ _ _ _ data

end MatrixMultiplication.AllFieldConstructionData

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldConstructionFamily

open MatrixMultiplication.Foundation AllFieldHistory AllFieldConstructionData
open AllFieldConstructionRates Filter
open scoped BigOperators Topology Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ}

def yieldRate (allocation : Allocation) (slack : ℝ) : ℝ :=
  AllFieldInitialEntropy.nativeH0 + AllFieldScheduledYield.physicalYield K allocation / K -
    (1 + 6 * (K + 2) : ℕ) * slack /
      ((K : ℝ) * denominator (K := K) allocation)

end MatrixMultiplication.AllFieldConstructionFamily

end
end

end MatrixAllFields

end OAI
end


