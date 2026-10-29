-- Prove2me | Definitions.Def_OAIQ089A004
-- name    : OAIQ089A004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T02:54:52.919115+00:00
-- url     : https://prove2.me/theorems/fdcdb708-5c37-4fbf-bc51-f0a4521138d1
-- title:
--   Definitions bundle OAIQ089A004 of the split of OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 737 declarations of OpenAI's Lean: 422 definitions, 2 inductive types or structures, 5 instances and 308 theorems. The definitions and types are `OAI.ContingencyTables.CompanionCanonicalHistory.canonicalLookup`, `OAI.ContingencyTables.CompanionCanonicalHistory.extend`, `OAI.ContingencyTables.CompanionCanonicalHistory.project`, `OAI.ContingencyTables.CompanionCappedReturn.returnDefault`, `OAI.ContingencyTables.CompanionComputedInitial.initialDraw`, `OAI.ContingencyTables.CompanionInitialDraw.draw`, `OAI.ContingencyTables.CompanionInitialDraw.idealLaw`, `OAI.ContingencyTables.CompanionInitialDraw.indexEquiv`, `OAI.ContingencyTables.CompanionInitialMatrixProgram.denominatorRealizer`, `OAI.ContingencyTables.CompanionPhaseFinishProgram.rationalResult`, `OAI.ContingencyTables.CompanionPhysicalNormalizer.smallProfilesEquiv`, `OAI.ContingencyTables.CompanionPhysicalTables.Feasible`, `OAI.ContingencyTables.CompanionPhysicalTables.PhysicalTables`, `OAI.ContingencyTables.CompanionPhysicalTables.fromBounded`, `OAI.ContingencyTables.CompanionPhysicalTables.physicalTable`, `OAI.ContingencyTables.CompanionPhysicalTables.tablesEquiv`, `OAI.ContingencyTables.CompanionPhysicalTables.toBounded`, `OAI.ContingencyTables.CompanionRationalUpdates.CountsPositive`, `OAI.ContingencyTables.CompanionRationalUpdates.checkedUpdate`, `OAI.ContingencyTables.CompanionRationalUpdates.defectCount`, `OAI.ContingencyTables.CompanionRationalUpdates.plainCount`, `OAI.ContingencyTables.CompanionTerminalRegions.integerDeviation`, `OAI.ContingencyTables.CompanionTraceWords.firstHit`, `OAI.ContingencyTables.CompanionTraceWords.returnValue`, `OAI.ContingencyTables.CompletionTranslation.completionChain`, `OAI.ContingencyTables.CountingAdaptiveInputProgram.Input`, `OAI.ContingencyTables.CountingAdaptiveInputProgram.Output`, `OAI.ContingencyTables.CountingAdaptiveInputProgram.Prepared`, `OAI.ContingencyTables.CountingAdaptiveInputProgram.Stored`, `OAI.ContingencyTables.CountingBaseProgram.Input`, `OAI.ContingencyTables.CountingBaseProgram.dimension`, `OAI.ContingencyTables.CountingBaseProgram.half`, `OAI.ContingencyTables.CountingBaseProgram.halfRealizer`, `OAI.ContingencyTables.CountingBranchProgram.budgetPolynomial`, `OAI.ContingencyTables.CountingCoefficientProgram.Input`, `OAI.ContingencyTables.CountingCoefficientProgram.allowance`, `OAI.ContingencyTables.CountingCoefficientProgram.coefficient`, `OAI.ContingencyTables.CountingCoefficientProgram.numerator`, `OAI.ContingencyTables.CountingCoefficientProgram.precision`, `OAI.ContingencyTables.CountingComputedSettings.Input` and 384 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `ContingencyTables_Counting_CompanionCanonicalHistory`, `ContingencyTables_Counting_CompanionCanonicalHistoryLaw`, `ContingencyTables_Counting_CompanionCappedReturn`, `ContingencyTables_Counting_CompanionComputedInitial`, `ContingencyTables_Counting_CompanionInitialDraw`, `ContingencyTables_Counting_CompanionInitialMatrixProgram`, `ContingencyTables_Counting_CompanionPhaseFinishSemantics`, `ContingencyTables_Counting_CompanionPhysicalNormalizer`, `ContingencyTables_Counting_CompanionPhysicalTables`, `ContingencyTables_Counting_CompanionRationalUpdates`, `ContingencyTables_Counting_CompanionTerminalRegions`, `ContingencyTables_Counting_CompanionTraceWords`, `ContingencyTables_Counting_CountingAdaptiveInputProgram`, `ContingencyTables_Counting_CountingBaseProgram`, `ContingencyTables_Counting_CountingBranchBudgetBound`, `ContingencyTables_Counting_CountingCoefficientProgram`, `ContingencyTables_Counting_CountingComputedSettings`, `ContingencyTables_Counting_CountingControlBounds`, `ContingencyTables_Counting_CountingDirectBudgetBound`, `ContingencyTables_Counting_CountingDirectWordBound`, `ContingencyTables_Counting_CountingInputParser`, `ContingencyTables_Counting_CountingLabelCountProgram`, `ContingencyTables_Counting_CountingOracleScheduleProgram`, `ContingencyTables_Counting_CountingPhaseScalarProgram`, `ContingencyTables_Counting_CountingPhaseSchedule`, `ContingencyTables_Counting_CountingPositiveProgram`, `ContingencyTables_Counting_CountingPositiveWordBound`, `ContingencyTables_Counting_CountingPreparedState`, `ContingencyTables_Counting_CountingPublicControls`, `ContingencyTables_Counting_CountingPublicTerminalBounds`, `ContingencyTables_Counting_CountingPublicWordBound`, `ContingencyTables_Counting_CountingScheduleSizes`, `ContingencyTables_Counting_CountingTerminalProgram`, `ContingencyTables_Counting_CountingTerminalSchedule`, `ContingencyTables_Dense_DenseAcceptance`, `ContingencyTables_Dense_DenseAffine`, `ContingencyTables_Dense_DenseAxisBits`, `ContingencyTables_Dense_DenseAxisProposal`, `ContingencyTables_Dense_DenseBitBudget`, `ContingencyTables_Dense_DenseBooleanDraw`, `ContingencyTables_Dense_DenseBooleanOffsets`, `ContingencyTables_Dense_DenseBooleanStep`, `ContingencyTables_Dense_DenseBooleanTrial`, `ContingencyTables_Dense_DenseBooleanWalk`, `ContingencyTables_Dense_DenseBoundedRejection`, `ContingencyTables_Dense_DenseBoundedTrial`, `ContingencyTables_Dense_DenseCandidateCounts`, `ContingencyTables_Dense_DenseCanonicalSemantics`, `ContingencyTables_Dense_DenseChain`, `ContingencyTables_Dense_DenseCoefficients`, `ContingencyTables_Dense_DenseCompletedMatrixProgram`, `ContingencyTables_Dense_DenseCompletionTest`, `ContingencyTables_Dense_DenseCountProgram`, `ContingencyTables_Dense_DenseDrawProgram`, `ContingencyTables_Dense_DenseEnumeratedMatrix`, `ContingencyTables_Dense_DenseExponentBound`, `ContingencyTables_Dense_DenseExponentListProgram`, `ContingencyTables_Dense_DenseExponentListSemantics`, `ContingencyTables_Dense_DenseExponentProgram`, `ContingencyTables_Dense_DenseFiniteTransition`, `ContingencyTables_Dense_DenseFiniteWalk`, `ContingencyTables_Dense_DenseFlatExponentProgram`, `ContingencyTables_Dense_DenseGeometry`, `ContingencyTables_Dense_DenseGoodBins`, `ContingencyTables_Dense_DenseGrid`, `ContingencyTables_Dense_DenseGridExponentProgram`, `ContingencyTables_Dense_DenseIdealRejection`, `ContingencyTables_Dense_DenseIntegerLaw`, `ContingencyTables_Dense_DenseIntegerTable`, `ContingencyTables_Dense_DenseInteriorVolume`, `ContingencyTables_Dense_DenseLocalGeometry`, `ContingencyTables_Dense_DenseMatrixProgram`, `ContingencyTables_Dense_DenseMatrixTable`, `ContingencyTables_Dense_DenseMatrixWalk`, `ContingencyTables_Dense_DenseMetropolisProgram`, `ContingencyTables_Dense_DenseMixing`, `ContingencyTables_Dense_DenseNormalizeSemantics`, `ContingencyTables_Dense_DenseNormalizer`, `ContingencyTables_Dense_DenseOffsetProgram`, `ContingencyTables_Dense_DenseOffsets`, `ContingencyTables_Dense_DenseRational`, `ContingencyTables_Dense_DenseRationalKernel`, `ContingencyTables_Dense_DenseRationalTrial`, `ContingencyTables_Dense_DenseRegionVolume`, `ContingencyTables_Dense_DenseRegularity`, `ContingencyTables_Dense_DenseReindexedVolume`, `ContingencyTables_Dense_DenseScaleCellProgram`, `ContingencyTables_Dense_DenseScaleMatrixProgram`, `ContingencyTables_Dense_DenseTableCoordinates`, `ContingencyTables_Dense_DenseTransitionCounts`, `ContingencyTables_Dense_DenseTrial`, `ContingencyTables_Dense_DenseTrialAcceptance`, `ContingencyTables_Dense_DenseTrialCountProgram`, `ContingencyTables_Dense_DenseTrialProgram`, `ContingencyTables_Dense_DenseTrialSemantics`, `ContingencyTables_Dense_DenseTrialWeights`, `ContingencyTables_Dense_DenseWalkTabulation`, `ContingencyTables_Dense_DenseWeights`, `ContingencyTables_Dense_DenseWordProgram`, `ContingencyTables_Dense_DensityLayers`, `ContingencyTables_Dense_GridAdjacency`, `ContingencyTables_Dense_GridConductance`, `ContingencyTables_Dense_GridCover`, `ContingencyTables_Dense_GridCutFlow`, `ContingencyTables_Dense_GridIndexProgram`, `ContingencyTables_Dense_GridMass`, `ContingencyTables_Dense_GridMetropolis`, `ContingencyTables_Dense_GridMinCut`, `ContingencyTables_Dense_GridPartition`, `ContingencyTables_Dense_PublishedCheeger`, `ContingencyTables_Machines_CompletionEnumerationProgram`, `ContingencyTables_Machines_DependentWordProgram`, `ContingencyTables_Machines_DyadicRootProgram`, `ContingencyTables_Machines_FairBits`, `ContingencyTables_Machines_FiniteWordPadding`, `ContingencyTables_Machines_FiniteWordRejection`, `ContingencyTables_Machines_FiniteWordWalk`, `ContingencyTables_Machines_FractionOutputProgram`, `ContingencyTables_Machines_FractionRepetitionProgram`, `ContingencyTables_Machines_InitialFactorialBits`, `ContingencyTables_Machines_LiteralProgram`, `ContingencyTables_Machines_MatrixCodeEquality`, `ContingencyTables_Machines_MaximalListProgram`, `ContingencyTables_Machines_OffsetCountProgram`, `ContingencyTables_Machines_OnlineIntegerRetry`, `ContingencyTables_Machines_PairedDemandProgram`, `ContingencyTables_Machines_PreparedDenseCount`, `ContingencyTables_Machines_PreparedOffsetCount`, `ContingencyTables_Machines_RepeatedFractionProgram`, `ContingencyTables_Machines_RetryNumeratorProgram`, `ContingencyTables_Machines_ScalarScheduleBounds`, `ContingencyTables_Machines_ScalarScheduleProgram`, `ContingencyTables_Machines_ScheduledResidualProgram`, `ContingencyTables_Machines_TableIndexProgram`, `ContingencyTables_Machines_TranslationDecisionProgram`, `ContingencyTables_Machines_VectorRetryProgram`, `ContingencyTables_Machines_WeightedArgmaxProgram`, `ContingencyTables_PublishedInputs`, `ContingencyTables_Rooted_ForestScaledPenalty`, `ContingencyTables_Rooted_LargeMarginProgram`, `ContingencyTables_Rooted_LargeMarginSemantics`, `ContingencyTables_Rooted_RootedCountingSchedule`, `ContingencyTables_Rooted_TreeFeasibleMass`, `ContingencyTables_Sampling_ExactIntegerOnline`, `ContingencyTables_Sampling_ExactIntegerProgram`, `ContingencyTables_Sampling_ExactMatrixTrial`, `ContingencyTables_Sampling_ExactSamplingParameters`, `ContingencyTables_Sampling_FirstPaperBooleanProposal`, `ContingencyTables_Sampling_FirstPaperPreparedProposal`, `ContingencyTables_Sampling_FirstPaperSmallChain`, `ContingencyTables_Sampling_FirstPaperSmallMixing`, `ContingencyTables_Sampling_FirstPaperSuccessRatio`, `ContingencyTables_Sampling_OriginalBalancedJoint`, `ContingencyTables_Sampling_OriginalProfileProgram`, `ContingencyTables_Sampling_OriginalResidualVector`, `ContingencyTables_Sampling_OriginalTableCardinality`, `ContingencyTables_Sampling_OriginalTableCheck`, `ContingencyTables_Sampling_OriginalTableEnumeration`, `ContingencyTables_Sampling_OriginalTableIndex`, `ContingencyTables_Sampling_OuterTableProgram`, `ContingencyTables_Sampling_Padding`, `ContingencyTables_Sampling_ProfilePublicProgram`, `ContingencyTables_Sampling_ProfileWordProgram`, `ContingencyTables_Sampling_Repair`, `ContingencyTables_Sampling_RepairFibres`, `ContingencyTables_Sampling_RepairResiduals`, `ContingencyTables_Sampling_SmallCellCatalogProgram`, `ContingencyTables_Sampling_SmallCompletionAcceptance`, `ContingencyTables_Sampling_SmallContextCount`, `ContingencyTables_Sampling_SmallProfileFlatCode`, `ContingencyTables_Sampling_SmallProfileRepair`, `ContingencyTables_Transport_AxisProposalTest`, `ContingencyTables_Transport_BalancedJointConstruction`, `ContingencyTables_Transport_BooleanEnumeration`, `ContingencyTables_Transport_BoundedOffsetLaw`, `ContingencyTables_Transport_BoxGeometry`, `ContingencyTables_Transport_CompletionChainFlow`, `ContingencyTables_Transport_CompletionEnergyComparison`, `ContingencyTables_Transport_DegreeCompletion`, `ContingencyTables_Transport_DyadicAcceptance`, `ContingencyTables_Transport_DyadicRootBisection`, `ContingencyTables_Transport_EdmondsKarpDistance`, `ContingencyTables_Transport_EqualityReindex`, `ContingencyTables_Transport_EqualitySoftening`, `ContingencyTables_Transport_FiniteAcceptCounts`, `ContingencyTables_Transport_FiniteExchangeDegree`, `ContingencyTables_Transport_FiniteGridWords`, `ContingencyTables_Transport_FiniteMetropolis`, `ContingencyTables_Transport_FiniteScaledDraw`, `ContingencyTables_Transport_FirstSuccess`, `ContingencyTables_Transport_InitialFactorialLaw`, `ContingencyTables_Transport_InitialTransversals`, `ContingencyTables_Transport_IntegerEquivLaw`, `ContingencyTables_Transport_IntegerLaw`, `ContingencyTables_Transport_IntegerLeafEnergy`, `ContingencyTables_Transport_IntegerMatrixPoint`, `ContingencyTables_Transport_IntegerPropagation`, `ContingencyTables_Transport_MetropolisChain`, `ContingencyTables_Transport_ProductIntegerSignature`, `ContingencyTables_Transport_RationalMapProducts`, `ContingencyTables_Transport_RationalProducts`, `ContingencyTables_Transport_RationalReindex`, `ContingencyTables_Transport_RationalWalks`, `ContingencyTables_Transport_ReferenceDrawBounds`, `ContingencyTables_Transport_RejectionLaw`, `ContingencyTables_Transport_RowMajorEnumeration`, `ContingencyTables_Transport_RowMajorPrefixFibres`, `ContingencyTables_Transport_ScalarPenalty`, `ContingencyTables_Transport_TableTightening`, `ContingencyTables_Transport_TranslatedCompletionChain`, `MatchingCount_Arithmetic_ArithmeticSize`, `MatchingCount_Arithmetic_TreeFraction`, `MatchingCount_Machines_OnlineControl`, `MatchingCount_Machines_OnlineFold`, `MatchingCount_Machines_OnlineFrame`, `MatchingCount_Machines_OnlineTree`, `MatchingCount_Machines_TreePostRealization`, `MatchingCount_Sampling_TreeCategorical`, `MatchingCount_Tapes_Codec`, `MatchingCount_Tapes_OnlineComposition`, `MatchingCount_Tapes_Packed`.
--
--   **Imports.** It imports the published bundle `Def_ContingencyTables`; the bundles `OAIQ089A000`, `OAIQ089A001` and `OAIQ089A002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ089A006`, `OAIQ089A007` and `OAIQ089A008`; the statement `OAI.ContingencyTables.ObservableTrajectory.omission_chain_dual`; the proof of `OAI.ContingencyTables.ObservableTrajectory.omission_chain_dual`.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A000
import Definitions.Def_OAIQ089A001
import Definitions.Def_OAIQ089A002

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ProductIntegerSignature
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Raw integer signatures of the actual line and unary product

The line groups are disjoint. Integer counts at zero are masked; a repeated
removal from a count below two uses a zero second-update factor. This
identifies the actual integer matrix, including its box boundaries, with a
congruence of the proved line/unary update matrix.
-/

namespace ContingencyTables.ProductIntegerSignature

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures

variable {I G : Type*} [Fintype I] [Fintype G]

noncomputable def productWeight (line : I → G) (a : G → ℕ → ℝ) (b : I → ℕ → ℝ)
    (z : I → ℕ) : ℝ := (∏ g, a g (lineTotal line z g)) * ∏ i, b i (z i)

omit [Fintype G] in
lemma lineTotal_removeOne (line : I → G) (z : I → ℕ) (i : I) (hi : 0 < z i) (g : G) :
    lineTotal line (removeOne z i) g + (if line i = g then 1 else 0) = lineTotal line z g := by
  have h1 := Finset.sum_erase_add (s := Finset.univ) (a := i)
    (fun k => if line k = g then z k else 0) (Finset.mem_univ i)
  have h2 := Finset.sum_erase_add (s := Finset.univ) (a := i)
    (fun k => if line k = g then removeOne z i k else 0) (Finset.mem_univ i)
  have he : (∑ k ∈ Finset.univ.erase i, if line k = g then removeOne z i k else 0) =
      ∑ k ∈ Finset.univ.erase i, if line k = g then z k else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [removeOne,(Finset.mem_erase.mp hk).1]
  rw [he] at h2
  have hepi : removeOne z i i = z i-1 := by simp [removeOne]
  rw [hepi] at h2
  unfold lineTotal
  by_cases hg : line i = g <;> simp only [hg,ite_true, if_true,ite_false] at h1 h2 ⊢ <;> omega

omit [Fintype G] in
lemma lineTotal_removeTwo (line : I → G) (z : I → ℕ) (i j : I)
    (hvalid : ValidPair z i j) (g : G) :
    lineTotal line (removeTwo z i j) g + (if line i = g then 1 else 0) +
      (if line j = g then 1 else 0) = lineTotal line z g := by
  have hj : 0 < removeOne z i j := hvalid.2
  have h1 := lineTotal_removeOne line z i hvalid.1 g
  have h2 := lineTotal_removeOne line (removeOne z i) j hj g
  change lineTotal line (removeOne (removeOne z i) j) g + _ + _ = _
  omega

/-- Literal product values after a valid integer removal coincide with
all line and unary update products. -/
theorem productWeight_removeTwo (line : I → G) (a : G → ℕ → ℝ) (b : I → ℕ → ℝ)
    (z : I → ℕ) (i j : I) (hvalid : ValidPair z i j) :
    productWeight line a b (removeTwo z i j) =
      lineUnaryRemoval line
        (fun g => a g (lineTotal line z g))
        (fun g => a g (lineTotal line z g-1))
        (fun g => if 2 ≤ lineTotal line z g then a g (lineTotal line z g-2) else 0)
        (fun k => b k (z k)) (fun k => b k (z k-1))
        (fun k => if 2 ≤ z k then b k (z k-2) else 0) i j := by
  unfold productWeight lineUnaryRemoval productTwoUpdates
  congr 1
  · apply Finset.prod_congr rfl
    intro g _
    have ht := lineTotal_removeTwo line z i j hvalid g
    by_cases hi : g = line i
    · by_cases hj : g = line j
      · have hn : 2 ≤ lineTotal line z g := by simp only [hi.symm,hj.symm,ite_true, if_true] at ht; omega
        have he : lineTotal line (removeTwo z i j) g = lineTotal line z g-2 := by
          simp only [hi.symm,hj.symm,ite_true, if_true] at ht; omega
        simp only [ite_eq_left hi,ite_eq_left hj,ite_eq_left hn,he]
      · have he : lineTotal line (removeTwo z i j) g = lineTotal line z g-1 := by
          simp only [hi.symm,ite_true, if_true,Ne.symm hj,ite_false] at ht; omega
        simp only [ite_eq_left hi,ite_eq_right hj,he]
    · by_cases hj : g = line j
      · have he : lineTotal line (removeTwo z i j) g = lineTotal line z g-1 := by
          simp only [Ne.symm hi,ite_false,hj.symm,ite_true, if_true] at ht; omega
        simp only [ite_eq_right hi,ite_eq_left hj,he]
      · have he : lineTotal line (removeTwo z i j) g = lineTotal line z g := by
          simp only [Ne.symm hi,Ne.symm hj,ite_false,add_zero] at ht; exact ht
        simp only [ite_eq_right hi,ite_eq_right hj,he]
  · apply Finset.prod_congr rfl
    intro k _
    by_cases hi : k = i
    · by_cases hj : k = j
      · have hn : 2 ≤ z k := by subst i; subst j; simp [ValidPair] at hvalid; omega
        have he : removeTwo z i j k = z k-2 := by simp [removeTwo,removeOne,hi.symm.trans hj,hi,Nat.sub_sub]
        simp only [ite_eq_left hi,ite_eq_left hj,ite_eq_left hn,he]
      · have he : removeTwo z i j k = z k-1 := by
          simp only [removeTwo,removeOne,ite_eq_left hi,ite_eq_right hj,Nat.sub_zero]
        simp only [ite_eq_left hi,ite_eq_right hj,he]
    · by_cases hj : k = j
      · have he : removeTwo z i j k = z k-1 := by
          simp only [removeTwo,removeOne,ite_eq_right hi,ite_eq_left hj,Nat.sub_zero]
        simp only [ite_eq_right hi,ite_eq_left hj,he]
      · simp only [removeTwo,removeOne,ite_eq_right hi,ite_eq_right hj,Nat.sub_zero]

end ContingencyTables.ProductIntegerSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ScalarPenalty
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual positive scalar softening factors

Absolute affine deviations, positive parts and interval distances have
convex integer exponents. Their powers of two are positive log-concave
sequences, supplying the concrete line and unary factors of both papers.
-/

namespace ContingencyTables.ScalarPenalty

open scoped BigOperators

/-- The positive equality softener tends to its exact equality indicator.
This is the actual finite limiting operation used after marginalization. -/
theorem factor_limit (D : ℝ) (hD : 0 ≤ D) :
    Filter.Tendsto (fun A : ℝ => (2:ℝ)^(-A*D)) Filter.atTop
      (nhds (if D=0 then 1 else 0)) := by
  by_cases hzero : D=0
  · simp [hzero]
  · have hpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hzero)
    let b : ℝ := (2:ℝ)^(-D)
    have hb₀ : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
    have hb₁ : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hpos)
    have hlim := tendsto_rpow_atTop_of_base_lt_one b (by linarith) hb₁
    rw [ite_eq_right hzero]
    convert hlim using 1
    all_goals try with_reducible_and_instances rfl
    funext A
    dsimp [b]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring

end ContingencyTables.ScalarPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_EqualitySoftening
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Root penalties and exact nonroot equations

Root lines carry their actual absolute-deviation penalty. Nonroot lines
carry a positive equality softener; its limit is the exact prescribed-line
indicator. Unary interval penalties include the companion's tree factors.
All balanced large-cell sums are performed before this finite limit.
-/

namespace ContingencyTables.EqualitySoftening

open scoped BigOperators Classical Matrix Topology
open Filter CommonBasesFPRAS FactorialSignatures ProductIntegerSignature
open ScalarPenalty IntegerMarginal BalancedBox BalancedFamily

variable {C G : Type*} [Fintype C] [Fintype G]

noncomputable def softenedWeight (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (L : ℝ) :
    (C → ℕ) → ℝ :=
  productWeight line (lineFactor root rate offset slope L) (unaryFactor urate ell uslope cap)

noncomputable def exactWeight (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) : (C → ℕ) → ℝ :=
  productWeight line (exactLineFactor root rate offset slope) (unaryFactor urate ell uslope cap)

lemma softenedWeight_positive (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (L : ℝ) (z : C → ℕ) :
    0 < softenedWeight line root rate offset slope urate ell uslope cap L z := by
  apply mul_pos <;> apply Finset.prod_pos <;> intro i _ <;> apply factor_positive

end ContingencyTables.EqualitySoftening

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_EqualityReindex
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Equality factors under the actual physical coordinate bijection

A bijection of coordinates preserves the line totals and unary products.
Consequently the balanced marginal signature applies to the literal
physical factor family after all cell-index bookkeeping has been proved.
-/

namespace ContingencyTables.EqualityReindex

open scoped BigOperators Classical
open ProductIntegerSignature EqualitySoftening BalancedFamily BalancedBox

variable {C D G : Type*} [Fintype C] [Fintype D] [Fintype G]

omit [Fintype G] in
lemma lineTotal_reindex (e : C ≃ D) (line : D → G) (z : C → ℕ) (g : G) :
    lineTotal (line ∘ e) z g=lineTotal line (z ∘ e.symm) g := by
  unfold lineTotal
  have h := e.sum_comp (fun d => if line d=g then z (e.symm d) else 0)
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using h

lemma productWeight_reindex (e : C ≃ D) (line : D → G)
    (a : G → ℕ → ℝ) (b : D → ℕ → ℝ) (z : C → ℕ) :
    productWeight (line ∘ e) a (fun c => b (e c)) z=
      productWeight line a b (z ∘ e.symm) := by
  unfold productWeight
  simp_rw [lineTotal_reindex]
  congr 1
  have h := e.prod_comp (fun d => b d (z (e.symm d)))
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using h

lemma exactWeight_reindex (e : C ≃ D) (line : D → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : D → ℝ) (z : C → ℕ) :
    exactWeight (line ∘ e) root rate offset slope (urate ∘ e) (ell ∘ e)
      (uslope ∘ e) (cap ∘ e) z=
      exactWeight line root rate offset slope urate ell uslope cap (z ∘ e.symm) := by
  unfold exactWeight
  exact productWeight_reindex e line (exactLineFactor root rate offset slope)
    (unaryFactor urate ell uslope cap) z

end ContingencyTables.EqualityReindex

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_InitialTransversals
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The initial transversal sum is an actual finite row-label choice sum

For every cell, a choice of row labels gives exactly one paired
transversal. Its factorial weight is the local factorial weight used in
the evaluated initialization brackets.
-/

namespace ContingencyTables.InitialTransversals

open scoped BigOperators Classical
open Nat
open CommonBasesFPRAS TwoLiftStates LabelledFactorial InitialLocalChoices

variable {C : Type*} [Fintype C] (b : C → ℕ)

lemma encode_plain (S : (c : C) → Finset (Fin (b c))) : PlainState pairs (encode b S) := by
  intro p hp
  obtain ⟨a,rfl⟩ : ∃ a, TwoLiftStates.pair a=p := by simpa [pairs] using hp
  by_cases hs : a.2∈S a.1
  · exact Or.inl (by simp [TwoLiftStates.pair,hs])
  · exact Or.inr (by simp [TwoLiftStates.pair,hs])

noncomputable def plainEquivChoices :
    {S : Set (Copy b×Bool) // PlainState pairs S} ≃ ((c : C) → Finset (Fin (b c))) where
  toFun S c := Finset.univ.filter (fun k => ((⟨c,k⟩,false):Copy b×Bool)∈S.val)
  invFun S := ⟨encode b S,encode_plain b S⟩
  left_inv S := by
    apply Subtype.ext
    ext ⟨⟨c,k⟩,t⟩
    have h := S.property (TwoLiftStates.pair (⟨c,k⟩:Copy b)) (pair_mem (⟨c,k⟩:Copy b))
    cases t
    · simp
    · simp only [encode_true,Finset.mem_filter,Finset.mem_univ,true_and]
      change (¬((⟨c,k⟩,false):Copy b×Bool)∈S.val)↔((⟨c,k⟩,true):Copy b×Bool)∈S.val
      rcases h with ⟨ha,hb⟩|⟨ha,hb⟩ <;> simp [TwoLiftStates.pair] at ha hb ⊢ <;> tauto
  right_inv S := by
    funext c
    ext k
    simp

end ContingencyTables.InitialTransversals

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FirstSuccess
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# First-success law and finite-law error bounds

The bounded outer sampler repeats independent trials and uses a fixed
feasible fallback. Its geometric output law has a stationary uniform-mixture
specialization. Total-variation bounds are preserved by deterministic output
maps.
-/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {α β : Type*} [Fintype α] [Fintype β]

variable [Nonempty α]

omit [Nonempty α] in
/-- Successful stationary pairs have equal mass; the repeated-trial law
is exactly a uniform law mixed with the fallback, without conditioning on
the implemented approximate trial's success. -/
theorem stationary_output_mass [DecidableEq α] (s : ℚ) (J : ℕ) (fallback z : α) :
    outputMass (fun _ => s * uniformMass (α := α)) (1 - s) J fallback z =
      (1 - (1 - s) ^ J) * uniformMass (α := α) +
        if z = fallback then (1 - s) ^ J else 0 := by
  have hgeom := geometric_balance (1 - s) J
  have hgeom' : s * (∑ j ∈ Finset.range J, (1 - s) ^ j) = 1 - (1 - s) ^ J := by
    nlinarith [hgeom]
  dsimp [outputMass]
  rw [mul_assoc, mul_comm (uniformMass (α := α)), ← mul_assoc, hgeom']

omit [Nonempty α] in
lemma point_mass_variation [DecidableEq α] (p : RationalLaw α) (fallback : α) :
    (∑ z, |(if z = fallback then (1 : ℚ) else 0) - p.mass z|) / 2 ≤ 1 := by
  have hsum : (∑ z, |(if z = fallback then (1 : ℚ) else 0) - p.mass z|) ≤ 2 := by
    calc
      _ ≤ ∑ z, ((if z = fallback then (1 : ℚ) else 0) + p.mass z) := by
        apply Finset.sum_le_sum
        intro z _
        have hi : (0 : ℚ) ≤ if z = fallback then 1 else 0 := by split_ifs <;> norm_num
        calc
          _ ≤ |if z = fallback then (1 : ℚ) else 0| + |p.mass z| := abs_sub _ _
          _ = _ := by rw [abs_of_nonneg hi, abs_of_nonneg (p.nonnegative z)]
      _ = 2 := by simp [Finset.sum_add_distrib, p.total]; norm_num
  linarith

/-- The stationary repeated-trial error is at most the probability that
all trials fail. No error term is divided by a success probability. -/
theorem stationary_variation [DecidableEq α] (s : ℚ) (_hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (J : ℕ) (fallback : α) :
    (∑ z, |outputMass (fun _ => s * uniformMass (α := α)) (1 - s) J fallback z -
      uniformMass (α := α)|) / 2 ≤ (1 - s) ^ J := by
  have hf : 0 ≤ (1 - s) ^ J := pow_nonneg (sub_nonneg.mpr hs1) _
  have hpoint := point_mass_variation (uniformLaw (α := α)) fallback
  have hterm (z : α) :
      |outputMass (fun _ => s * uniformMass (α := α)) (1 - s) J fallback z -
        uniformMass (α := α)| =
      (1 - s) ^ J * |(if z = fallback then (1 : ℚ) else 0) - uniformMass (α := α)| := by
    rw [stationary_output_mass]
    have heq : (1 - (1 - s) ^ J) * uniformMass (α := α) +
        (if z = fallback then (1 - s) ^ J else 0) - uniformMass (α := α) =
        (1 - s) ^ J * ((if z = fallback then 1 else 0) - uniformMass (α := α)) := by
      split_ifs <;> ring
    rw [heq, abs_mul, abs_of_nonneg hf]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  change (1 - s) ^ J * (∑ z, |(if z = fallback then 1 else 0) - uniformMass (α := α)|) / 2 ≤ _
  change (∑ z, |(if z = fallback then 1 else 0) - uniformMass (α := α)|) / 2 ≤ 1 at hpoint
  nlinarith [mul_le_mul_of_nonneg_left hpoint hf]

omit [Nonempty α] in
/-- Independent trials accumulate their errors additively, before the
deterministic first-success map is applied. -/
theorem variation_product (p q : RationalLaw α) (r s : RationalLaw β) :
    variation (productLaw p r) (productLaw q s) ≤ variation p q + variation r s := by
  have hpoint (a : α) (b : β) : |p.mass a * r.mass b - q.mass a * s.mass b| ≤
      p.mass a * |r.mass b - s.mass b| + |p.mass a - q.mass a| * s.mass b := by
    calc
      _ = |p.mass a * (r.mass b - s.mass b) + (p.mass a - q.mass a) * s.mass b| := by
        congr 1
        ring
      _ ≤ |p.mass a * (r.mass b - s.mass b)| + |(p.mass a - q.mass a) * s.mass b| :=
        abs_add_le _ _
      _ = _ := by
        rw [abs_mul, abs_mul, abs_of_nonneg (p.nonnegative a), abs_of_nonneg (s.nonnegative b)]
  have hsum : (∑ a, ∑ b, |p.mass a * r.mass b - q.mass a * s.mass b|) ≤
      (∑ a, |p.mass a - q.mass a|) + (∑ b, |r.mass b - s.mass b|) := by
    calc
      _ ≤ ∑ a, ∑ b, (p.mass a * |r.mass b - s.mass b| +
          |p.mass a - q.mass a| * s.mass b) := by
        apply Finset.sum_le_sum
        intro a _
        exact Finset.sum_le_sum fun b _ => hpoint a b
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
          p.total, s.total, one_mul, mul_one]
        ring
  unfold variation
  simp only [productLaw, Fintype.sum_prod_type]
  linarith

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalReindex
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite rational laws transported through bijections -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {α β : Type*} [Fintype α] [Fintype β]

theorem variation_equiv (e : α ≃ β) (p q : RationalLaw α) :
    variation (equivLaw e p) (equivLaw e q) = variation p q := by
  unfold variation equivLaw
  congr 1
  symm
  apply Fintype.sum_equiv e
  intro x
  simp

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RejectionLaw
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite repeated-trial laws and their approximation error -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

theorem variation_self (p : RationalLaw α) : variation p p = 0 := by
  simp [variation]

theorem variation_triangle (p q r : RationalLaw α) :
    variation p r ≤ variation p q + variation q r := by
  have hsum : (∑ x, |p.mass x - r.mass x|) ≤
      (∑ x, |p.mass x - q.mass x|) + ∑ x, |q.mass x - r.mass x| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ => abs_sub_le (p.mass x) (q.mass x) (r.mass x)
  unfold variation
  linarith

def retryStep (p : RationalLaw α) (f : α → Option β) (tail : RationalLaw β) : RationalLaw β :=
  mapLaw (productLaw p tail) (fun z => (f z.1).getD z.2)

def retryLaw (p : RationalLaw α) (f : α → Option β) (fallback : β) : ℕ → RationalLaw β
  | 0 => pointLaw fallback
  | n + 1 => retryStep p f (retryLaw p f fallback n)

def successMass (p : RationalLaw α) (f : α → Option β) (z : β) : ℚ :=
  ∑ x, if f x = some z then p.mass x else 0

def failureMass (p : RationalLaw α) (f : α → Option β) : ℚ :=
  ∑ x, if f x = none then p.mass x else 0

theorem success_failure_total (p : RationalLaw α) (f : α → Option β) :
    (∑ z, successMass p f z) + failureMass p f = 1 := by
  unfold successMass failureMass
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  calc
    _ = ∑ x, p.mass x := by
      apply Finset.sum_congr rfl
      intro x _
      cases f x <;> simp
    _ = 1 := p.total

theorem retryStep_mass (p : RationalLaw α) (f : α → Option β)
    (tail : RationalLaw β) (z : β) :
    (retryStep p f tail).mass z = successMass p f z + failureMass p f * tail.mass z := by
  change (∑ x : α × β, if (f x.1).getD x.2 = z then p.mass x.1 * tail.mass x.2 else 0) = _
  rw [Fintype.sum_prod_type]
  unfold successMass failureMass
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases hfx : f x with
  | none => simp [hfx]
  | some y =>
    by_cases hy : y = z
    · subst y
      simp only [hfx, Option.getD_some, ite_true, if_true, ite_false,
        reduceCtorEq, zero_mul, add_zero]
      rw [← Finset.mul_sum, tail.total, mul_one]
    · simp [hfx, hy]

/-- The law of finitely many independent trials, each of which can either
return a value or fail, is the geometric first-success law. -/
theorem retryLaw_mass (p : RationalLaw α) (f : α → Option β)
    (fallback z : β) (n : ℕ) :
    (retryLaw p f fallback n).mass z =
      outputMass (successMass p f) (failureMass p f) n fallback z := by
  induction n with
  | zero => simp [retryLaw, pointLaw, outputMass]
  | succ n ih =>
    rw [retryLaw, retryStep_mass, ih, outputMass_succ]

/-- Approximate independent trials incur their error before the success
test. Rejection never divides that error by a success probability. -/
theorem retryLaw_variation (p q : RationalLaw α) (f : α → Option β)
    (fallback : β) (n : ℕ) :
    variation (retryLaw p f fallback n) (retryLaw q f fallback n) ≤
      (n : ℚ) * variation p q := by
  induction n with
  | zero => simp [retryLaw, variation_self]
  | succ n ih =>
    calc
      _ ≤ variation p q + variation (retryLaw p f fallback n) (retryLaw q f fallback n) :=
        (variation_map (productLaw p (retryLaw p f fallback n))
          (productLaw q (retryLaw q f fallback n)) _).trans (variation_product _ _ _ _)
      _ ≤ variation p q + (n : ℚ) * variation p q := add_le_add le_rfl ih
      _ = _ := by push_cast; ring

end

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalWalks
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent composition of finite rational transition experiments -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {α β : Type*} [Fintype α] [Fintype β]

variable [DecidableEq α]

/-- Each transition uses a fresh independent finite experiment. -/
def walkLaw (K : α → RationalLaw α) (a : α) : ℕ → RationalLaw α
  | 0 => pointLaw a
  | n + 1 => bindLaw (walkLaw K a n) K

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordWalk
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact laws of a walk driven by independent fixed-length Boolean words -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem uniform_map_mass {A : Type*} [Fintype A] [Nonempty A] (f : A → α) (y : α) :
    (mapLaw (uniformLaw (α := A)) f).mass y = uniformMapMass f y := by
  change (∑ x, if f x = y then 1 / (Fintype.card A : ℚ) else 0) =
    (∑ x, if f x = y then (1 : ℚ) else 0) / Fintype.card A
  rw [Finset.sum_div]
  simp only [ite_div, zero_div]

def wordWalkLaw {k : ℕ} (step : α → (Fin k → Bool) → α) (a : α) (n : ℕ) : RationalLaw α :=
  mapLaw (uniformLaw (α := Fin n → Fin k → Bool)) (wordWalk step a n)

/-- A uniform finite Boolean array realizes the independent transition-law
composition, with no random-length source or conditioning. -/
theorem wordWalkLaw_eq {k : ℕ} (step : α → (Fin k → Bool) → α) (a : α) (n : ℕ) :
    wordWalkLaw step a n = walkLaw (fun s => mapLaw (uniformLaw (α := Fin k → Bool)) (step s)) a n := by
  induction n with
  | zero =>
    apply RationalLaw.ext
    funext b
    simp [wordWalkLaw, wordWalk, walkLaw, pointLaw, mapLaw, uniformLaw, uniformMass, eq_comm]
  | succ n ih =>
    let E : ((Fin n → Fin k → Bool) × (Fin k → Bool)) ≃ (Fin (n + 1) → Fin k → Bool) :=
      (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Fin k → Bool))
    have hc : (wordWalk step a (n + 1)) ∘ E =
        fun ab => step (wordWalk step a n ab.1) ab.2 := by
      funext ab
      rcases ab with ⟨pref, last⟩
      change step (wordWalk step a n (Fin.init
        (Fin.snoc (α := fun _ : Fin (n + 1) => Fin k → Bool) pref last)))
        ((Fin.snoc (α := fun _ : Fin (n + 1) => Fin k → Bool) pref last) (Fin.last n)) = _
      simp only [Fin.init_snoc, Fin.snoc_last]
    apply RationalLaw.ext
    funext b
    change (wordWalkLaw step a (n + 1)).mass b =
      (bindLaw (walkLaw (fun s => mapLaw (uniformLaw (α := Fin k → Bool)) (step s)) a n)
        (fun s => mapLaw (uniformLaw (α := Fin k → Bool)) (step s))).mass b
    rw [← ih]
    simp only [wordWalkLaw, bindLaw, uniform_map_mass]
    have he := uniformMapMass_equiv E (wordWalk step a (n + 1)) b
    rw [hc] at he
    rw [← he]
    exact uniformMapMass_prod (wordWalk step a n) step b

end

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalProducts
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite product laws for the independent bounded offset draws -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

theorem variation_pi_succ {n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, Fintype (α i)]
    (p q : ∀ i, RationalLaw (α i)) :
    variation (piLaw p) (piLaw q) =
      variation (productLaw (p 0) (piLaw (fun i : Fin n => p i.succ)))
        (productLaw (q 0) (piLaw (fun i : Fin n => q i.succ))) := by
  unfold variation
  congr 1
  apply Fintype.sum_equiv (Fin.consEquiv α).symm
  intro x
  change |(∏ i, (p i).mass (x i)) - (∏ i, (q i).mass (x i))| =
    |(p 0).mass (x 0) * (∏ i : Fin n, (p i.succ).mass (x i.succ)) -
      (q 0).mass (x 0) * (∏ i : Fin n, (q i.succ).mass (x i.succ))|
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]

/-- Errors in independent coordinate draws add before any success test
or deterministic table completion is applied. -/
theorem variation_pi {n : ℕ} (α : Fin n → Type*) [∀ i, Fintype (α i)]
    (p q : ∀ i, RationalLaw (α i)) :
    variation (piLaw p) (piLaw q) ≤ ∑ i, variation (p i) (q i) := by
  induction n with
  | zero => simp [variation, piLaw]
  | succ n ih =>
    have hi := ih (fun i : Fin n => α i.succ)
      (fun i : Fin n => p i.succ) (fun i : Fin n => q i.succ)
    calc
      _ = _ := variation_pi_succ α p q
      _ ≤ variation (p 0) (q 0) +
          variation (piLaw (fun i : Fin n => p i.succ)) (piLaw (fun i : Fin n => q i.succ)) :=
        variation_product _ _ _ _
      _ ≤ variation (p 0) (q 0) + ∑ i : Fin n, variation (p i.succ) (q i.succ) :=
        add_le_add le_rfl hi
      _ = _ := (Fin.sum_univ_succ (fun i => variation (p i) (q i))).symm

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalMapProducts
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent finite coordinate maps and uniform product laws -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section

theorem mapLaw_id {A : Type*} [Fintype A] [DecidableEq A] (p : RationalLaw A) : mapLaw p id = p := by
  apply RationalLaw.ext
  funext y
  simp [mapLaw]

theorem mapLaw_product {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq C] [DecidableEq D] [DecidableEq (C × D)]
    (p : RationalLaw A) (q : RationalLaw B) (f : A → C) (g : B → D) :
    mapLaw (productLaw p q) (fun z => (f z.1, g z.2)) = productLaw (mapLaw p f) (mapLaw q g) := by
  apply RationalLaw.ext
  funext z
  change (∑ x : A × B, if (f x.1, g x.2) = z then p.mass x.1 * q.mass x.2 else 0) =
    (∑ x, if f x = z.1 then p.mass x else 0) * (∑ y, if g y = z.2 then q.mass y else 0)
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : f x = z.1 <;> by_cases hy : g y = z.2 <;> simp [Prod.ext_iff, hx, hy]

theorem mapLaw_equiv_output {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C]
    (e : B ≃ C) (p : RationalLaw A) (f : A → B) :
    mapLaw p (fun x => e (f x)) = equivLaw e (mapLaw p f) := by
  apply RationalLaw.ext
  funext y
  change (∑ x, if e (f x) = y then p.mass x else 0) =
    ∑ x, if f x = e.symm y then p.mass x else 0
  simp only [← Equiv.eq_symm_apply]

variable {n : ℕ} {α β : Fin n → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]

theorem pi_mapLaw [∀ i, DecidableEq (β i)] [DecidableEq (∀ i, β i)] (p : ∀ i, RationalLaw (α i)) (f : ∀ i, α i → β i) :
    mapLaw (piLaw p) (fun x i => f i (x i)) = piLaw (fun i => mapLaw (p i) (f i)) := by
  apply RationalLaw.ext
  funext y
  change (∑ x : ∀ i, α i, if (fun i => f i (x i)) = y then ∏ i, (p i).mass (x i) else 0) =
    ∏ i, ∑ x : α i, if f i x = y i then (p i).mass x else 0
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_ite_zero]
  congr 1
  exact propext funext_iff

omit [∀ i, Fintype (β i)] in
theorem pi_uniformLaw [∀ i, Nonempty (α i)] :
    piLaw (fun i => uniformLaw (α := α i)) = uniformLaw (α := ∀ i, α i) := by
  apply RationalLaw.ext
  funext x
  change (∏ i, (1 : ℚ) / Fintype.card (α i)) = 1 / Fintype.card (∀ i, α i)
  rw [Finset.prod_div_distrib, Finset.prod_const_one, ← Nat.cast_prod, Fintype.card_pi]

end

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FairBits
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded fair-bit scaling

Both papers for result 200 implement a bounded approximately uniform integer
choice by drawing `z` uniformly from `0,...,Q-1` and returning `⌊M*z/Q⌋`.
When `Q = 2^k`, the input choice uses exactly `k` fair bits.

We prove the exact integer fiber formula in 200-01, equation
`eq:dense-offset-count`, and the pointwise and total-variation error estimates
used in 200-02, Lemma `lem:dyadic-integer-draw`. The arguments are direct
finite arithmetic and have no published-input hypotheses.
-/

open scoped BigOperators

namespace ContingencyTables.FairBits

/-- Every point mass differs from uniform by at most `1/Q`. -/
theorem outputMass_error {M Q β : ℕ} (hM : 0 < M) (hQ : 0 < Q) (hβ : β < M) :
    |outputMass M Q β - 1 / (M : ℚ)| ≤ 1 / (Q : ℚ) := by
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hQn : (Q : ℚ) ≠ 0 := ne_of_gt hQq
  have herr := (fiber_card_error hM hQ hβ).le
  have heq : outputMass M Q β - 1 / (M : ℚ) =
      (((fiber M Q β).card : ℚ) - (Q : ℚ) / M) / Q := by
    dsimp [outputMass]
    field_simp
  rw [heq, abs_div, abs_of_pos hQq]
  exact (div_le_div_iff_of_pos_right hQq).mpr herr

/-- Total variation with the manuscript's convention `½ ∑ |p-u|`. -/
def variationFromUniform (M Q : ℕ) : ℚ :=
  (1 / 2) * ∑ β ∈ Finset.range M, |outputMass M Q β - 1 / (M : ℚ)|

/-- The bounded integer draw has total-variation error at most `M/(2Q)`.
The papers use the weaker bound `M/Q`. -/
theorem variation_bound {M Q : ℕ} (hM : 0 < M) (hQ : 0 < Q) :
    variationFromUniform M Q ≤ (M : ℚ) / (2 * Q) := by
  have hsum : (∑ β ∈ Finset.range M, |outputMass M Q β - 1 / (M : ℚ)|) ≤
      (M : ℚ) * (1 / (Q : ℚ)) := by
    calc
      _ ≤ ∑ _β ∈ Finset.range M, (1 / (Q : ℚ)) := by
        apply Finset.sum_le_sum
        intro β hβ
        exact outputMass_error hM hQ (Finset.mem_range.mp hβ)
      _ = _ := by simp
  dsimp [variationFromUniform]
  calc
    _ ≤ (1 / 2 : ℚ) * ((M : ℚ) * (1 / (Q : ℚ))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedOffsetLaw
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bounded scaling laws for the dense offsets -/

namespace ContingencyTables.FairBits

open scoped BigOperators
open ResidualMixture FirstSuccess

theorem scaledLaw_variation (M k : ℕ) (hM : 0 < M) :
    variation (scaledLaw M k hM) (uniformIntLaw M hM) ≤ (M : ℚ) / (2 * (2 : ℚ) ^ k) := by
  have h := variation_bound hM (pow_pos (by decide : 0 < 2) k)
  change (1 / 2 : ℚ) * (∑ β ∈ Finset.range M, |outputMass M (2 ^ k) β - 1 / (M : ℚ)|) ≤ _ at h
  unfold variation
  simp only [scaledLaw, uniformIntLaw]
  have hs : (∑ β : Fin M, |outputMass M (2 ^ k) β.val - 1 / (M : ℚ)|) =
      ∑ β ∈ Finset.range M, |outputMass M (2 ^ k) β - 1 / (M : ℚ)| :=
    Fin.sum_univ_eq_sum_range (fun β => |outputMass M (2 ^ k) β - 1 / (M : ℚ)|) M
  rw [hs]
  simpa only [div_eq_mul_inv, mul_comm, Nat.cast_pow, Nat.cast_ofNat, one_mul] using h

/-- This law is the exact output law of multiplying the finite fair-bit
integer by w and taking the integer quotient. -/
theorem dense_scaled_offset_variation (w h d : ℕ) (hw : 0 < w) :
    variation (scaledLaw w (offsetBitLength w h d) hw) (uniformIntLaw w hw) ≤
      1 / (2 : ℚ) ^ (4 * (h + d)) := by
  apply (scaledLaw_variation w (offsetBitLength w h d) hw).trans
  have hpow : w ≤ 2 ^ Nat.clog 2 (w + 1) :=
    (Nat.le_succ w).trans (Nat.le_pow_clog (by decide) (w + 1))
  have hp : (w : ℚ) ≤ (2 : ℚ) ^ Nat.clog 2 (w + 1) := by exact_mod_cast hpow
  unfold offsetBitLength
  rw [pow_add]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_right hp
    (show (0 : ℚ) ≤ 2 ^ (4 * (h + d)) by positivity)
  nlinarith [pow_pos (by norm_num : (0 : ℚ) < 2) (4 * (h + d))]

theorem dense_offset_product_variation (q h d : ℕ) (w : Fin q → ℕ)
    (hw : ∀ i, 0 < w i) (hq : q ≤ d) :
    variation (piLaw (fun i => scaledLaw (w i) (offsetBitLength (w i) h d) (hw i)))
      (piLaw (fun i => uniformIntLaw (w i) (hw i))) ≤
        (d : ℚ) / (2 : ℚ) ^ (4 * (h + d)) := by
  calc
    _ ≤ ∑ i : Fin q, variation
        (scaledLaw (w i) (offsetBitLength (w i) h d) (hw i))
        (uniformIntLaw (w i) (hw i)) := variation_pi _ _ _
    _ ≤ ∑ _i : Fin q, 1 / (2 : ℚ) ^ (4 * (h + d)) :=
      Finset.sum_le_sum (fun i _ => dense_scaled_offset_variation (w i) h d (hw i))
    _ = (q : ℚ) / (2 : ℚ) ^ (4 * (h + d)) := by simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hq) (by positivity)

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteScaledDraw
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded quotient draw is realized by an actual Boolean word -/

namespace ContingencyTables.FairBits

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

theorem scaledIntegerLaw_eq (M k : ℕ) (hM : 0 < M) :
    mapLaw (uniformLaw (α := Fin (2 ^ k))) (scaledInteger M k hM) = scaledLaw M k hM := by
  apply RationalLaw.ext
  funext β
  rw [uniform_map_mass]
  change (∑ z : Fin (2 ^ k), if scaledInteger M k hM z = β then (1 : ℚ) else 0) /
    Fintype.card (Fin (2 ^ k)) = outputMass M (2 ^ k) β.val
  simp only [scaledInteger, Fin.ext_iff, ← scale_eq_div, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun z : ℕ =>
    if scale M (2 ^ k) z = β.val then (1 : ℚ) else 0) (2 ^ k)]
  unfold outputMass fiber
  rw [← Finset.sum_filter]
  simp

/-- The exact law of the finite Boolean quotient operation is the law
used in the dense offset error estimate and the tabulation formula. -/
theorem scaledBitIntegerLaw_eq (M k : ℕ) (hM : 0 < M) :
    mapLaw (uniformLaw (α := Fin k → Bool)) (scaledBitInteger M k hM) = scaledLaw M k hM := by
  unfold scaledBitInteger
  rw [← map_equiv (binaryWordEquiv k), uniform_equiv]
  exact scaledIntegerLaw_eq M k hM

end

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_InitialFactorialLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent initial cell choices give the literal companion law

The finite rational law is the product of the uniform-size subset laws.
Encoding a choice as its paired transversal yields exactly the initial
law of the companion's factorial lift, with its actual free-completion
normalizer cancelled.
-/

namespace ContingencyTables.InitialFactorialLaw

open CommonBasesFPRAS ResidualMixture FirstSuccess TwoLiftStates LabelledFactorial
open InitialTransversals FixedCardinalityMixture CompanionFactorialApplication
open scoped BigOperators Classical
noncomputable section

variable {C : Type*} [Fintype C] (b : C → ℕ)

def plainLaw : RationalLaw {S : Set (Copy b×Bool) // PlainState pairs S} :=
  equivLaw (plainEquivChoices b).symm (choiceLaw b)

variable {I J : Type*} [Fintype I] [Fintype J]

def companionLaw (A : Instance I J) :
    RationalLaw {S : Set (Labels A×Bool) // PlainState pairs S} :=
  plainLaw (fun s : SmallCell A => A.b s.val.1 s.val.2)

end
end ContingencyTables.InitialFactorialLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_InitialFactorialBits
attribute [-instance] _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One finite Boolean word for the actual initial transversal

The word is split into disjoint cell blocks; each block chooses a size
and then a subset of that size. The total variation errors add before
the exact paired-transversal encoding is applied.
-/

namespace ContingencyTables.InitialFactorialBits

open CommonBasesFPRAS ResidualMixture FirstSuccess FairBits TwoLiftStates
open FixedCardinalityMixture InitialFactorialLaw InitialTransversals
open CompanionFactorialApplication
open scoped BigOperators Classical
noncomputable section

variable {q : ℕ}

variable {C : Type*} [Fintype C]

def transversalDraw (b : C → ℕ) (e : C ≃ Fin q) (B : ℕ)
    (bits : Fin (bitCount (fun i => b (e.symm i)) B) → Bool) :
    {S : Set (Copy b×Bool) // PlainState pairs S} :=
  (plainEquivChoices b).symm
    (choiceEquiv b e (drawChoices (fun i => b (e.symm i)) B bits))

end
end ContingencyTables.InitialFactorialBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_PublishedCheeger
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published finite-chain Cheeger input

Levin and Peres, *Markov Chains and Mixing Times*, second edition (2017),
Theorem 13.10, equation (13.6), lower bound, together with the variational
characterization in Lemma 13.7. The theorem is attributed there to Sinclair
and Jerrum (1989) and Lawler and Sokal (1988).
Source: https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf

The finite reversible lazy-chain Poincaré consequence is expressed using
stationary cut flow and the symmetric Dirichlet energy.
-/

namespace ContingencyTables.PublishedInputs

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable (X : Type*) [Fintype X]

/-- The smallest Cheeger consequence needed here. The cut inequality uses
unnormalized stationary flow across each cut once; `energy` includes the
usual factor one half in its symmetric pair-sum formula. -/
def FiniteCheeger : Prop :=
  ∀ (C : FiniteChain X) (κ : ℝ), 0 < κ →
    (∀ S : Finset X,
      κ * min (∑ x ∈ S, C.π x) (∑ x ∈ Sᶜ, C.π x) ≤
        ∑ x ∈ S, ∑ y ∈ Sᶜ, C.π x * C.P x y) →
    ∀ f : X → ℝ, C.variance f ≤ (2 / κ ^ 2) * C.energy f

end

end ContingencyTables.PublishedInputs

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_MetropolisChain
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite weighted Metropolis chain

The holding probability, stationary law, and cut flow are proved from
positive weights, symmetric proposals, and the proposal-degree bound.
Only the final Poincaré consequence uses the explicit published Cheeger input.
-/

namespace ContingencyTables.MetropolisChain

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {X : Type*} [Fintype X] [Nonempty X]

omit [Nonempty X] in
theorem move_reversible (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (Adj : X → X → Prop) (hsym : ∀ x y, Adj x y ↔ Adj y x)
    (β : ℝ) (x y : X) :
    (w x / normalizer w) * move w Adj β x y =
      (w y / normalizer w) * move w Adj β y x := by
  unfold move
  by_cases h : Adj x y
  · rw [ite_eq_left h, ite_eq_left ((hsym x y).mp h)]
    have hx := accept_mass (w x) (w y) (hw x)
    have hy := accept_mass (w y) (w x) (hw y)
    calc
      _ = β * (w x * min 1 (w y / w x)) / normalizer w := by ring
      _ = β * min (w x) (w y) / normalizer w := by rw [hx]
      _ = β * (w y * min 1 (w x / w y)) / normalizer w := by rw [hy, min_comm]
      _ = _ := by ring
  · simp only [h, (hsym x y).not.mp h, ite_false, mul_zero]

def chain (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (Adj : X → X → Prop) (hsym : ∀ x y, Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x, (Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D : ℝ) * β ≤ 1 / 2) : FiniteChain X :=
  FiniteChain.ofMoves (fun x => w x / normalizer w) (move w Adj β)
    (fun x => div_pos (hw x) (normalizer_pos w hw))
    (by rw [← Finset.sum_div]; exact div_self (ne_of_gt (normalizer_pos w hw)))
    (move_nonnegative w hw Adj β hβ)
    (move_row_bound w Adj β hβ D hdegree hproposal)
    (move_reversible w hw Adj hsym β)

theorem chain_flow (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (Adj : X → X → Prop) (hsym : ∀ x y, Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x, (Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D : ℝ) * β ≤ 1 / 2) (x y : X) (hxy : x ≠ y) :
    let C := chain w hw Adj hsym β hβ D hdegree hproposal
    C.π x * C.P x y = if Adj x y then β * min (w x) (w y) / normalizer w else 0 := by
  change (w x / normalizer w) * (move w Adj β x y + if x = y then _ else 0) = _
  rw [ite_eq_right hxy, add_zero]
  unfold move
  split_ifs
  · have hx := accept_mass (w x) (w y) (hw x)
    calc
      _ = β * (w x * min 1 (w y / w x)) / normalizer w := by ring
      _ = _ := by rw [hx]
  · exact mul_zero _

theorem chain_cut_flow (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (Adj : X → X → Prop) (hsym : ∀ x y, Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x, (Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D : ℝ) * β ≤ 1 / 2) (S : Finset X) :
    let C := chain w hw Adj hsym β hβ D hdegree hproposal
    (∑ x ∈ S, ∑ y ∈ Sᶜ, C.π x * C.P x y) =
      (β / normalizer w) * (∑ x ∈ S, ∑ y ∈ Sᶜ, if Adj x y then min (w x) (w y) else 0) := by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  have hxy : x ≠ y := fun h => (Finset.mem_compl.mp hy) (h ▸ hx)
  rw [chain_flow w hw Adj hsym β hβ D hdegree hproposal x y hxy]
  split_ifs <;> ring

theorem poincare_of_weighted_cut (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (Adj : X → X → Prop) (hsym : ∀ x y, Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x, (Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D : ℝ) * β ≤ 1 / 2)
    (hCheeger : PublishedInputs.FiniteCheeger X) (κ : ℝ) (hκ : 0 < κ)
    (hcut : ∀ S : Finset X,
      κ * min (∑ x ∈ S, w x) (∑ x ∈ Sᶜ, w x) ≤
        β * (∑ x ∈ S, ∑ y ∈ Sᶜ, if Adj x y then min (w x) (w y) else 0)) :
    ∀ f : X → ℝ,
      (chain w hw Adj hsym β hβ D hdegree hproposal).variance f ≤
        (2 / κ ^ 2) * (chain w hw Adj hsym β hβ D hdegree hproposal).energy f := by
  apply hCheeger _ κ hκ
  intro S
  rw [chain_cut_flow]
  change κ * min (∑ x ∈ S, w x / normalizer w) (∑ x ∈ Sᶜ, w x / normalizer w) ≤ _
  rw [← Finset.sum_div, ← Finset.sum_div, min_div_div_right (normalizer_pos w hw).le]
  have hz := normalizer_pos w hw
  have h := div_le_div_of_nonneg_right (hcut S) hz.le
  first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

end

end ContingencyTables.MetropolisChain

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialDraw
attribute [-instance] _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bounded-word initialization of the companion trace

The output is in the literal `PlainIndex` used by the trace chain. Its
ideal rational law is exactly the source's phase-zero law; the bounded
word implementation is within 2^(-h), with an explicit word length.
-/

namespace ContingencyTables.CompanionInitialDraw

open CommonBasesFPRAS ResidualMixture FirstSuccess TwoLiftStates
open CompanionFactorialApplication InitialFactorialLaw InitialFactorialBits
open RealKernelApproximation
open scoped BigOperators Classical
noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def indexEquiv (A : Instance I J) :
    {S : Set (Labels A×Bool) // PlainState pairs S} ≃
      PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool))) where
  toFun S := ⟨⟨S.val,Or.inl S.property⟩,S.property⟩
  invFun S := ⟨S.val.val,S.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def idealLaw (A : Instance I J) :
    RationalLaw (PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))) :=
  equivLaw (indexEquiv A) (companionLaw A)

def draw (A : Instance I J) (B : ℕ) (bits : Fin (initialBits A B) → Bool) :
    PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool))) :=
  indexEquiv A (transversalDraw (fun s : SmallCell A => A.b s.val.1 s.val.2)
    (cellEnum A) B bits)

end
end ContingencyTables.CompanionInitialDraw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_PublishedInputs
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published analytic input for result 200

Prékopa, *On logarithmic concave measures and functions*, Acta Sci. Math.
(Szeged) 34 (1973), 335–343, Theorem 3, equation (2.3), with two source
functions. Source: https://acta.bibl.u-szeged.hu/14411/1/math_034_335-343.pdf
The one-dimensional input is Leindler (1972), *On a certain converse of
Hölder's inequality II*, 217–223, as identified in Prékopa's §2.

The finite-box specialization allows positive continuous functions on a
common compact coordinate box and finite unions of open boxes.
-/

namespace ContingencyTables.PublishedInputs

open MeasureTheory

/-- The bounded finite unions of open coordinate boxes used by the bin
conductance argument. Empty unions and empty coordinate boxes are allowed. -/
def IsFiniteBoxUnion {q : ℕ} (S : Set (Point q)) : Prop :=
  ∃ (n : ℕ) (lower upper : Fin n → Point q),
    S = {x | ∃ k : Fin n, ∀ i, lower k i < x i ∧ x i < upper k i}

/-- The weighted Minkowski interpolation with the manuscript convention. -/
def interpolate {q : ℕ} (t : ℝ) (S T : Set (Point q)) : Set (Point q) :=
  {z | ∃ x ∈ S, ∃ y ∈ T, z = (1 - t) • x + t • y}

/-- Precisely the previously published finite-box integral interpolation
input. The functions need only be positive and continuous on the common
compact coordinate box; all integrals are Lebesgue integrals. -/
def FiniteBoxPrekopaLeindler (q : ℕ) : Prop :=
  ∀ (t : ℝ), 0 < t → t < 1 →
  ∀ (lower upper : Point q) (S₀ S₁ S₂ : Set (Point q))
    (f₀ f₁ f₂ : Point q → ℝ),
    IsFiniteBoxUnion S₀ → IsFiniteBoxUnion S₁ → IsFiniteBoxUnion S₂ →
    closure S₀ ⊆ Set.Icc lower upper →
    closure S₁ ⊆ Set.Icc lower upper →
    closure S₂ ⊆ Set.Icc lower upper →
    ContinuousOn f₀ (Set.Icc lower upper) →
    ContinuousOn f₁ (Set.Icc lower upper) →
    ContinuousOn f₂ (Set.Icc lower upper) →
    (∀ x ∈ Set.Icc lower upper, 0 < f₀ x) →
    (∀ x ∈ Set.Icc lower upper, 0 < f₁ x) →
    (∀ x ∈ Set.Icc lower upper, 0 < f₂ x) →
    interpolate t S₁ S₂ ⊆ S₀ →
    (∀ x ∈ S₁, ∀ y ∈ S₂,
      (f₁ x) ^ (1 - t) * (f₂ y) ^ t ≤ f₀ ((1 - t) • x + t • y)) →
    (∫ x in S₁, f₁ x) ^ (1 - t) * (∫ y in S₂, f₂ y) ^ t ≤
      ∫ z in S₀, f₀ z

/-- Log-concavity is needed only on the common ambient box. -/
def LogConcaveOn {q : ℕ} (ρ : Point q → ℝ) (K : Set (Point q)) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ∀ t : ℝ, 0 < t → t < 1 →
    (ρ x) ^ (1 - t) * (ρ y) ^ t ≤ ρ ((1 - t) • x + t • y)

/-- Specialization of the published input to the one log-concave density
used for bin conductance. The geometric hypotheses specify the common ambient box. -/
theorem density_interpolation {q : ℕ} (hPL : FiniteBoxPrekopaLeindler q)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (lower upper : Point q) (S T : Set (Point q)) (ρ : Point q → ℝ)
    (hS : IsFiniteBoxUnion S) (hT : IsFiniteBoxUnion T)
    (hM : IsFiniteBoxUnion (interpolate t S T))
    (hSc : closure S ⊆ Set.Icc lower upper)
    (hTc : closure T ⊆ Set.Icc lower upper)
    (hMc : closure (interpolate t S T) ⊆ Set.Icc lower upper)
    (hρ : ContinuousOn ρ (Set.Icc lower upper))
    (hpos : ∀ x ∈ Set.Icc lower upper, 0 < ρ x)
    (hlc : LogConcaveOn ρ (Set.Icc lower upper)) :
    (∫ x in S, ρ x) ^ (1 - t) * (∫ y in T, ρ y) ^ t ≤
      ∫ z in interpolate t S T, ρ z := by
  apply hPL t ht ht1 lower upper (interpolate t S T) S T ρ ρ ρ
    hM hS hT hMc hSc hTc hρ hρ hρ hpos hpos hpos Set.Subset.rfl
  intro x hx y hy
  exact hlc x (hSc (subset_closure hx)) y (hTc (subset_closure hy)) t ht ht1

end ContingencyTables.PublishedInputs

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseWeights
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Continuous and dyadic bin weights

The actual floor-rounded weights used by the dense grid sampler. Convexity
of the penalty implies log-concavity of its density, and local changes of
the scaled penalty give explicit comparisons with the dyadic bin weights.
-/

namespace ContingencyTables.DenseWeights

noncomputable section

theorem density_pos {X : Type*} (A : ℝ) (p : X → ℝ) (x : X) :
    0 < density A p x := Real.rpow_pos_of_pos (by norm_num) _

theorem binWeight_pos {X : Type*} (A : ℝ) (p : X → ℝ) (v : X) :
    0 < binWeight A p v := Real.rpow_pos_of_pos (by norm_num) _

/-- A scaled-penalty change at most `s` gives the tube density bound. -/
theorem density_le_binWeight {X : Type*} (A : ℝ) (p : X → ℝ)
    (x v : X) (s : ℝ) (hchange : |A * p x - A * p v| ≤ s) :
    density A p x ≤ (2 : ℝ) ^ s * binWeight A p v := by
  have hlo := Int.floor_le (A * p v)
  have h := (abs_le.mp hchange).1
  calc
    density A p x ≤ (2 : ℝ) ^ (s - (⌊A * p v⌋ : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (2 : ℝ) ^ s * binWeight A p v := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num)]
      rfl

theorem binWeight_le_density {X : Type*} (A : ℝ) (p : X → ℝ)
    (x v : X) (s : ℝ) (hchange : |A * p x - A * p v| ≤ s) :
    binWeight A p v ≤ (2 : ℝ) ^ (s + 1) * density A p x := by
  have hhi := Int.lt_floor_add_one (A * p v)
  have h := (abs_le.mp hchange).2
  calc
    binWeight A p v ≤ (2 : ℝ) ^ ((s + 1) - A * p x) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (2 : ℝ) ^ (s + 1) * density A p x := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num)]
      rfl

theorem bin_density_comparison {X : Type*} (A : ℝ) (p : X → ℝ)
    (x v : X) (hchange : |A * p x - A * p v| ≤ 1) :
    binWeight A p v / 4 ≤ density A p x ∧ density A p x ≤ 2 * binWeight A p v := by
  have hl := binWeight_le_density A p x v 1 hchange
  have hu := density_le_binWeight A p x v 1 hchange
  norm_num at hl hu
  constructor <;> linarith

theorem tube_density_comparison {X : Type*} (A : ℝ) (p : X → ℝ)
    (x v : X) (hchange : |A * p x - A * p v| ≤ 2) :
    density A p x ≤ 4 * binWeight A p v := by
  have h := density_le_binWeight A p x v 2 hchange
  norm_num at h
  exact h

theorem density_continuous {X : Type*} [TopologicalSpace X]
    (A : ℝ) (p : X → ℝ) (hp : Continuous p) : Continuous (density A p) := by
  exact Real.continuous_const_rpow (by norm_num) |>.comp ((continuous_const.mul hp).neg)

/-- The continuous density used by the sampler is log-concave on every
convex domain on which its penalty is convex. -/
theorem density_logConcave {q : ℕ} (A : ℝ) (hA : 0 ≤ A)
    (p : PublishedInputs.Point q → ℝ) (K : Set (PublishedInputs.Point q))
    (hp : ConvexOn ℝ K p) : PublishedInputs.LogConcaveOn (density A p) K := by
  intro x hx y hy t ht ht₁
  have hc := hp.2 hx hy (sub_nonneg.mpr ht₁.le) ht.le (show (1 - t) + t = 1 by ring)
  simp only [smul_eq_mul] at hc
  have he : (density A p x) ^ (1 - t) * (density A p y) ^ t =
      (2 : ℝ) ^ (-A * ((1 - t) * p x + t * p y)) := by
    simp only [density, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [he]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hc hA]

end

end ContingencyTables.DenseWeights

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledPenalty
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convexity and the actual scaled forest-penalty Lipschitz bound -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestRootPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def scaledTree (A : Instance I J) (B : ℝ) (x q : I → J → ℤ)
    (v : FreeCell A.small A.T → ℝ) (t : TreeCell A.T) : ℝ :=
  AffinePenalty.affineValue (normalizedOffset A t x q) (normalizedCoefficient A B t) v

noncomputable def penalty (A : Instance I J) (C B : ℝ) (x q : I → J → ℤ)
    (v : FreeCell A.small A.T → ℝ) : ℝ :=
  C*(rootConstant A x q+∑ t : TreeCell A.T,intervalCost (scaledTree A B x q v t))

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_Padding
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Padding and the successful-table bijection

Padding a designated rectangle by a fixed amount gives a bijection from
original tables to enlarged-margin tables whose entries dominate the
padding. Each successful joint object therefore yields exactly one table.
-/

namespace ContingencyTables

open Finset
open scoped Classical

variable {I J : Type*} [Fintype I] [Fintype J]

def unpadTable {r : I → ℕ} {c : J → ℕ} (P : I → J → ℕ)
    (Y : Table (paddedRows r P) (paddedColumns c P))
    (hY : ∀ i j, P i j ≤ Y.val i j) : Table r c := by
  refine ⟨fun i j => Y.val i j - P i j, ?_, ?_⟩
  · intro i
    have hsum := sum_congr (s₁ := (univ : Finset J)) (f := fun j => Y.val i j)
      (g := fun j => (Y.val i j - P i j) + P i j) rfl
      (fun j _ => (Nat.sub_add_cancel (hY i j)).symm)
    rw [Y.property.1 i, sum_add_distrib] at hsum
    exact Nat.add_right_cancel hsum.symm
  · intro j
    have hsum := sum_congr (s₁ := (univ : Finset I)) (f := fun i => Y.val i j)
      (g := fun i => (Y.val i j - P i j) + P i j) rfl
      (fun i _ => (Nat.sub_add_cancel (hY i j)).symm)
    rw [Y.property.2 j, sum_add_distrib] at hsum
    exact Nat.add_right_cancel hsum.symm

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAffine
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Free coordinates of a dense completion block

`none` denotes the pivot row or column. The free coordinates are the other
cells. These are the manuscript's actual affine completion formulas; the
row and column constraints hold identically, and feasible tables are
uniquely determined by their free cells.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Recover an actual table from its scaled free coordinates. -/
theorem table_recover (R : Option I → ℝ) (P : Option J → ℝ) (w : I → J → ℝ)
    (hw : ∀ i j, w i j ≠ 0) (X : Option I → Option J → ℝ)
    (hR : ∀ i, ∑ j, X i j = R i) (hP : ∀ j, ∑ i, X i j = P j) :
    table R P w (fun p => X (some p.1) (some p.2) / w p.1 p.2) = X := by
  have htotal : ∑ i, R i = ∑ j, P j := by
    simp_rw [← hR, ← hP]
    exact Finset.sum_comm
  apply table_unique
  · intro i
    rw [table_rows, hR]
  · intro j
    rw [table_columns _ _ _ _ htotal, hP]
  · intro i j
    simp only [table]
    exact mul_div_cancel₀ _ (hw i j)

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCoefficients
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coefficients of normalized dense entries

Reordering maximum margins to the pivot makes each contributing free-cell
scale no larger than the dependent-cell scale. Thus every normalized
coefficient is bounded by `1/B`, as required by the actual penalty proof.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem table_affine (R : Option I → ℝ) (P : Option J → ℝ) (w : I → J → ℝ)
    (u : I × J → ℝ) (g : Option I × Option J) :
    table R P w u g.1 g.2 =
      AffinePenalty.affineValue (entryOffset R P g) (entryCoeff w g) u := by
  rcases g with ⟨i, j⟩
  cases i <;> cases j
  · simp [table, AffinePenalty.affineValue, entryOffset, entryCoeff, Fintype.sum_prod_type]
  · simp [table, AffinePenalty.affineValue, entryOffset, entryCoeff,
      Fintype.sum_prod_type, ite_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  · simp [table, AffinePenalty.affineValue, entryOffset, entryCoeff,
      Fintype.sum_prod_type, ite_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  · simp [table, AffinePenalty.affineValue, entryOffset, entryCoeff, ite_mul]

theorem normalized_table_affine (R : Option I → ℝ) (P : Option J → ℝ)
    (w : I → J → ℝ) (u : I × J → ℝ) (g : Option I × Option J) :
    table R P w u g.1 g.2 / cellScale R P g =
      AffinePenalty.affineValue (entryOffset R P g / cellScale R P g)
        (fun p => entryCoeff w g p / cellScale R P g) u := by
  rw [table_affine]
  unfold AffinePenalty.affineValue
  rw [add_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseRegularity
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regularity of the dense sampler's actual penalty

The natural margins, maximum pivots, integer quotient widths, and actual
parameters A=d⁴, B=d⁸ determine the penalty. Its regularity and scaled
change bounds follow from the normalized affine coefficients.
-/

namespace ContingencyTables.DenseAffine

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def densePenalty (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) :
    (I × J → ℝ) → ℝ :=
  AffinePenalty.penalty
    (fun g => entryOffset (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    (fun g p => entryCoeff (denseWidth R P d) g p /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    ((d : ℝ) / (d : ℝ) ^ 8)

theorem densePenalty_continuous (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) :
    Continuous (densePenalty R P d) := AffinePenalty.penalty_continuous _ _ _

theorem densePenalty_convex (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (K : Set (I × J → ℝ)) (hK : Convex ℝ K) : ConvexOn ℝ K (densePenalty R P d) :=
  AffinePenalty.penalty_convex _ _ _ K hK

/-- A coordinate displacement at most `r` changes the actual scaled
penalty A*p by at most `r`. In particular this is at most one in a bin
and at most two in the cut-face tubes. -/
theorem densePenalty_scaled_change (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (x y : I × J → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hxy : ∀ p, |x p - y p| ≤ r) :
    |(d : ℝ) ^ 4 * densePenalty R P d x - (d : ℝ) ^ 4 * densePenalty R P d y| ≤ r := by
  have hbase := AffinePenalty.penalty_change
    (fun g => entryOffset (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    (fun g p => entryCoeff (denseWidth R P d) g p /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    ((d : ℝ) / (d : ℝ) ^ 8) x y (1 / (d : ℝ) ^ 8) r (by positivity) hr
    (dense_normalized_coeff_bound R P d hd hR hP hRmax hPmax) hxy
  have hcard : (Fintype.card (I × J) : ℝ) ≤ d := by exact_mod_cast hfree
  have hscale : (d : ℝ) ^ 4 * Fintype.card (I × J) / (d : ℝ) ^ 8 ≤ 1 := by
    calc
      _ ≤ (d : ℝ) ^ 4 * d / (d : ℝ) ^ 8 := by gcongr
      _ ≤ 1 := dense_exponent_change_scale d hd
  calc
    _ = (d : ℝ) ^ 4 * |densePenalty R P d x - densePenalty R P d y| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 4)]
    _ ≤ (d : ℝ) ^ 4 * (Fintype.card (I × J) * (1 / (d : ℝ) ^ 8) * r) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = ((d : ℝ) ^ 4 * Fintype.card (I × J) / (d : ℝ) ^ 8) * r := by ring
    _ ≤ r := by simpa using mul_le_mul_of_nonneg_right hscale hr

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoxGeometry
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-box geometry for the conditional conductance argument

Finite unions of grid boxes remain finite unions of boxes under weighted
Minkowski interpolation, giving the domain hypothesis of Prékopa–Leindler.
-/

namespace ContingencyTables.PublishedInputs

open MeasureTheory

theorem finite_box_union_of_fintype {q : ℕ} {K : Type*} [Fintype K]
    (lower upper : K → Point q) :
    IsFiniteBoxUnion {x | ∃ k : K, ∀ i, lower k i < x i ∧ x i < upper k i} := by
  classical
  let e := (Fintype.equivFin K).symm
  refine ⟨Fintype.card K, (fun k => lower (e k)), (fun k => upper (e k)), ?_⟩
  ext x
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨e.symm k, by simpa using hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨e k, hk⟩

/-- Interpolation preserves exactly the finite-box class appearing in
Prékopa's published integral inequality. -/
theorem IsFiniteBoxUnion.interpolate {q : ℕ} {S T : Set (Point q)}
    (hS : IsFiniteBoxUnion S) (hT : IsFiniteBoxUnion T)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    IsFiniteBoxUnion (interpolate t S T) := by
  classical
  obtain ⟨n, l, u, rfl⟩ := hS
  obtain ⟨m, l', u', rfl⟩ := hT
  let K := {p : Fin n × Fin m //
    (∀ i, l p.1 i < u p.1 i) ∧ (∀ i, l' p.2 i < u' p.2 i)}
  let lower : K → Point q := fun p i => (1 - t) * l p.val.1 i + t * l' p.val.2 i
  let upper : K → Point q := fun p i => (1 - t) * u p.val.1 i + t * u' p.val.2 i
  have heq : PublishedInputs.interpolate t {x | ∃ k : Fin n, ∀ i, l k i < x i ∧ x i < u k i}
      {x | ∃ k : Fin m, ∀ i, l' k i < x i ∧ x i < u' k i} =
      {z | ∃ k : K, ∀ i, lower k i < z i ∧ z i < upper k i} := by
    ext z
    constructor
    · rintro ⟨x, ⟨k, hk⟩, y, ⟨k', hk'⟩, rfl⟩
      let p : K := ⟨(k, k'),
        (fun i => (hk i).1.trans (hk i).2),
        (fun i => (hk' i).1.trans (hk' i).2)⟩
      refine ⟨p, ?_⟩
      intro i
      change (1 - t) * l k i + t * l' k' i < (1 - t) * x i + t * y i ∧
        (1 - t) * x i + t * y i < (1 - t) * u k i + t * u' k' i
      constructor
      · exact add_lt_add
          (mul_lt_mul_of_pos_left (hk i).1 (sub_pos.mpr ht1))
          (mul_lt_mul_of_pos_left (hk' i).1 ht)
      · exact add_lt_add
          (mul_lt_mul_of_pos_left (hk i).2 (sub_pos.mpr ht1))
          (mul_lt_mul_of_pos_left (hk' i).2 ht)
    · rintro ⟨p, hp⟩
      have hw (i : Fin q) := scalar_box_interpolation t
        (l p.val.1 i) (u p.val.1 i) (l' p.val.2 i) (u' p.val.2 i) (z i)
        ht ht1 (p.property.1 i) (p.property.2 i) (hp i)
      choose w hw using hw
      refine ⟨(fun i => (w i).1), ⟨p.val.1, ?_⟩,
        (fun i => (w i).2), ⟨p.val.2, ?_⟩, ?_⟩
      · exact fun i => ⟨(hw i).1, (hw i).2.1⟩
      · exact fun i => ⟨(hw i).2.2.1, (hw i).2.2.2.1⟩
      · funext i
        exact (hw i).2.2.2.2
  rw [heq]
  exact finite_box_union_of_fintype lower upper

theorem IsFiniteBoxUnion.isOpen {q : ℕ} {S : Set (Point q)}
    (hS : IsFiniteBoxUnion S) : IsOpen S := by
  obtain ⟨n, l, u, rfl⟩ := hS
  have heq : {x : Point q | ∃ k : Fin n, ∀ i, l k i < x i ∧ x i < u k i} =
      ⋃ k : Fin n, ⋂ i : Fin q, {x : Point q | l k i < x i ∧ x i < u k i} := by
    ext x
    simp
  rw [heq]
  apply isOpen_iUnion
  intro k
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_lt (continuous_apply i) continuous_const)

theorem interpolation_closure_in_box {q : ℕ} {S T : Set (Point q)}
    {lower upper : Point q} (hS : closure S ⊆ Set.Icc lower upper)
    (hT : closure T ⊆ Set.Icc lower upper) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    closure (interpolate t S T) ⊆ Set.Icc lower upper := by
  apply isClosed_Icc.closure_subset_iff.mpr
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact convex_Icc lower upper (hS (subset_closure hx)) (hT (subset_closure hy))
    (sub_nonneg.mpr ht1) ht (by ring)

/-- The interpolation shell gains the mass used in the grid-cut proof.
This conditional result depends only on the precisely identified published
integral inequality; finite-box closure and integrability are proved here. -/
theorem interpolation_shell_gain {q : ℕ} (hPL : FiniteBoxPrekopaLeindler q)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (lower upper : Point q) (S T : Set (Point q)) (ρ : Point q → ℝ)
    (hS : IsFiniteBoxUnion S) (hT : IsFiniteBoxUnion T)
    (hSc : closure S ⊆ Set.Icc lower upper)
    (hTc : closure T ⊆ Set.Icc lower upper)
    (hρ : ContinuousOn ρ (Set.Icc lower upper))
    (hpos : ∀ x ∈ Set.Icc lower upper, 0 < ρ x)
    (hlc : LogConcaveOn ρ (Set.Icc lower upper))
    (hsub : S ⊆ interpolate t S T)
    (hSmass : 0 < ∫ x in S, ρ x)
    (hTmass : 2 * (∫ x in S, ρ x) ≤ ∫ x in T, ρ x) :
    ((2 : ℝ) ^ t - 1) * (∫ x in S, ρ x) ≤
      ∫ x in (interpolate t S T) \ S, ρ x := by
  have hMc := interpolation_closure_in_box hSc hTc t ht.le ht1.le
  have hM := hS.interpolate hT t ht ht1
  have hint : IntegrableOn ρ (interpolate t S T) :=
    hρ.integrableOn_Icc.mono_set (fun _ hx => hMc (subset_closure hx))
  rw [MeasureTheory.setIntegral_sdiff hS.isOpen.measurableSet hint hsub]
  have hPL' := density_interpolation hPL t ht ht1 lower upper S T ρ
    hS hT hM hSc hTc hMc hρ hpos hlc
  have hgain := weighted_geometric_doubling (∫ x in S, ρ x) (∫ x in T, ρ x)
    t hSmass hTmass ht.le
  nlinarith

end ContingencyTables.PublishedInputs

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridCover
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite cut-face cover of the interpolation shell

The continuous shell in the conductance argument is covered, except for
the null grid hyperplanes, by the finite collection of interior cut-face
tubes. No exterior faces or segment general-position hypotheses occur.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory

variable {I : Type*} [Fintype I] [DecidableEq I]

def mixGrid {K : ℕ} (a b : Grid (I := I) K) (S : Finset I) : Grid (I := I) K :=
  fun j => if j ∈ S then b j else a j

omit [Fintype I] in
theorem corner_mix {K : ℕ} (a b : Grid (I := I) K) (S : Finset I) :
    corner (mixGrid a b S) = mixed (corner a) (corner b) S := by
  ext j
  by_cases hj : j ∈ S <;> simp [corner, mixGrid, mixed, hj]

def selectedBins (K : ℕ) (P : (I → ℤ) → Prop) : Set (I → ℝ) :=
  {x | ∃ a : Grid K, P (corner a) ∧ OpenBin (corner a) x}

def IsGridEdge {K : ℕ} (p : Grid (I := I) K × Grid (I := I) K × I) : Prop :=
  corner p.2.1 p.2.2 = corner p.1 p.2.2 + 1 ∧
    ∀ j, j ≠ p.2.2 → p.2.1 j = p.1 j

abbrev CutEdge (K : ℕ) (P : (I → ℤ) → Prop) :=
  {p : Grid (I := I) K × Grid (I := I) K × I //
    IsGridEdge p ∧ (P (corner p.1) ↔ ¬ P (corner p.2.1))}

noncomputable instance instFintypeCutEdge (K : ℕ) (P : (I → ℤ) → Prop) : Fintype (CutEdge K P) :=
  Fintype.ofFinite _

def edgeTube {K : ℕ} {P : (I → ℤ) → Prop} (e : CutEdge K P) (r : ℝ) : Set (I → ℝ) :=
  faceTube (corner e.val.1) e.val.2.2 r

omit [Fintype I] [DecidableEq I] in
theorem openBin_in_cube {K : ℕ} (a : Grid (I := I) K) (x : I → ℝ)
    (hx : OpenBin (corner a) x) : Cube K x := by
  intro j
  have hl : (0 : ℝ) ≤ (corner a j : ℝ) := by exact_mod_cast (a j).property.1
  have hu : (corner a j : ℝ) ≤ (K : ℝ) - 1 := by exact_mod_cast (a j).property.2
  exact ⟨by linarith [(hx j).1], by linarith [(hx j).2]⟩

theorem near_finite_cut_tube {K : ℕ} (P : (I → ℤ) → Prop)
    (a b : Grid (I := I) K) (x z : I → ℝ) (r : ℝ)
    (ha : OpenBin (corner a) x) (hb : OpenBin (corner b) z)
    (hd : ∀ j, |z j - x j| < r) (hr : r ≤ 1)
    (hPa : P (corner a)) (hPb : ¬ P (corner b)) :
    ∃ e : CutEdge K P, z ∈ edgeTube e r := by
  classical
  obtain ⟨S, i, w, hi, hS, hSi, hadj, hw, hw', hdw⟩ :=
    near_cut_face P (corner a) (corner b) x z r ha hb hd hr hPa hPb
  let u := mixGrid a b S
  let v := mixGrid a b (insert i S)
  have hui : corner u i = corner a i := by simp [u, corner, mixGrid, hi]
  have hvi : corner v i = corner b i := by simp [v, corner, mixGrid]
  have hsame (j : I) (hj : j ≠ i) : v j = u j := by simp [v, u, mixGrid, hj]
  have hPu : P (corner u) := by simpa [u, corner_mix] using hS
  have hPv : ¬ P (corner v) := by simpa [v, corner_mix] using hSi
  have hwu : ClosedBin (corner u) w := by simpa [u, corner_mix] using hw
  have hwv : ClosedBin (corner v) w := by simpa [v, corner_mix] using hw'
  rcases hadj with hab | hab
  · have he : corner v i = corner u i + 1 := by rw [hui, hvi]; exact hab
    let e : CutEdge K P := ⟨(u, v, i), ⟨he, hsame⟩, by simp [hPu, hPv]⟩
    refine ⟨e, mem_faceTube_of_near (corner u) i r z w hwu ?_ hdw⟩
    have he' : (corner v i : ℝ) = (corner u i : ℝ) + 1 := by exact_mod_cast he
    exact le_antisymm (hwu i).2 (by linarith [(hwv i).1])
  · have he : corner u i = corner v i + 1 := by rw [hui, hvi]; exact hab
    let e : CutEdge K P := ⟨(v, u, i), ⟨he, fun j hj => (hsame j hj).symm⟩,
      by simp [hPu, hPv]⟩
    refine ⟨e, mem_faceTube_of_near (corner v) i r z w hwv ?_ hdw⟩
    have he' : (corner u i : ℝ) = (corner v i : ℝ) + 1 := by exact_mod_cast he
    exact le_antisymm (hwv i).2 (by linarith [(hwu i).1])

omit [Fintype I] [DecidableEq I] in
theorem floor_grid {K : ℕ} (z : I → ℝ) (hz : Cube K z) :
    ∃ b : Grid (I := I) K, ∀ j, corner b j = ⌊z j⌋ := by
  have h (j : I) : ⌊z j⌋ ∈ Set.Icc (0 : ℤ) ((K : ℤ) - 1) := by
    refine ⟨Int.floor_nonneg.mpr (hz j).1.le, ?_⟩
    have hlt : ⌊z j⌋ < (K : ℤ) := Int.floor_lt.mpr (by simpa using (hz j).2)
    omega
  exact ⟨fun j => ⟨⌊z j⌋, h j⟩, fun _ => rfl⟩

/-- Every shell point off the grid hyperplanes belongs to an interior
cut-face tube. This is the actual cover used by the manuscript. -/
theorem interpolation_shell_cover {q K : ℕ} (P : (Fin q → ℤ) → Prop)
    (t : ℝ) (ht : 0 < t) (ht₁ : t < 1) (hr : t * K ≤ 1)
    (z : Fin q → ℝ)
    (hz : z ∈ PublishedInputs.interpolate t (selectedBins K P) {y | Cube K y} \
      selectedBins K P)
    (hoff : ∀ j (k : ℤ), z j ≠ (k : ℝ)) :
    ∃ e : CutEdge K P, z ∈ edgeTube e (t * K) := by
  obtain ⟨⟨x, ⟨a, hPa, hax⟩, y, hy, rfl⟩, hnot⟩ := hz
  have hx := openBin_in_cube a x hax
  obtain ⟨hzCube, hd⟩ := interpolation_short x y t hx hy ht ht₁
  obtain ⟨b, hb⟩ := floor_grid _ hzCube
  have hzb : OpenBin (corner b) (fun j => (1 - t) * x j + t * y j) := by
    intro j
    rw [hb j]
    refine ⟨?_, Int.lt_floor_add_one _⟩
    exact lt_of_le_of_ne (Int.floor_le _) (Ne.symm (hoff j _))
  have hPb : ¬ P (corner b) := by
    intro hPb
    exact hnot ⟨b, hPb, hzb⟩
  exact near_finite_cut_tube P a b x _ (t * K) hax hzb hd hr hPa hPb

theorem interpolation_shell_cover_ae {q K : ℕ} (P : (Fin q → ℤ) → Prop)
    (t : ℝ) (ht : 0 < t) (ht₁ : t < 1) (hr : t * K ≤ 1) :
    ∀ᵐ z ∂volume, z ∈ PublishedInputs.interpolate t (selectedBins K P) {y | Cube K y} \
      selectedBins K P → ∃ e : CutEdge K P, z ∈ edgeTube e (t * K) := by
  filter_upwards [ae_off_grid (I := Fin q)] with z hz
  exact fun h => interpolation_shell_cover P t ht ht₁ hr z h hz

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridMass
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Continuous mass and weighted grid cuts

Unit bins have disjoint interiors and exact volume one. Their continuous
mass is compared with the discrete weights, and the finite shell cover
converts interpolation gain into a weighted cut-face sum.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators

variable {q K : ℕ}

def binSet (a : Grid (I := Fin q) K) : Set (Fin q → ℝ) :=
  {x | OpenBin (corner a) x}

abbrev Selected (K : ℕ) (P : (Fin q → ℤ) → Prop) :=
  {a : Grid (I := Fin q) K // P (corner a)}

noncomputable instance instFintypeSelected (P : (Fin q → ℤ) → Prop) : Fintype (Selected K P) :=
  Fintype.ofFinite _

theorem binSet_pi (a : Grid (I := Fin q) K) :
    binSet a = Set.pi Set.univ (fun j => Set.Ioo (corner a j : ℝ) ((corner a j : ℝ) + 1)) := by
  ext x
  simp [binSet, OpenBin]

theorem binSet_measurable (a : Grid (I := Fin q) K) : MeasurableSet (binSet a) := by
  rw [binSet_pi]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem binSet_volume (a : Grid (I := Fin q) K) : volume (binSet a) = 1 := by
  rw [binSet_pi, Real.volume_pi_Ioo]
  simp

theorem binSet_disjoint (a b : Grid (I := Fin q) K) (hab : a ≠ b) :
    Disjoint (binSet a) (binSet b) := by
  apply Set.disjoint_left.mpr
  intro x hax hbx
  apply hab
  funext j
  apply Subtype.ext
  have ha : ⌊x j⌋ = corner a j := Int.floor_eq_iff.mpr ⟨(hax j).1.le, (hax j).2⟩
  have hb : ⌊x j⌋ = corner b j := Int.floor_eq_iff.mpr ⟨(hbx j).1.le, (hbx j).2⟩
  exact ha.symm.trans hb

theorem binSet_subset_ambient (a : Grid (I := Fin q) K) : binSet a ⊆ ambientBox q K := by
  intro x hx
  have h := openBin_in_cube a x hx
  exact ⟨fun j => (h j).1.le, fun j => (h j).2.le⟩

theorem selectedBins_finiteBox (P : (Fin q → ℤ) → Prop) :
    PublishedInputs.IsFiniteBoxUnion (selectedBins K P) := by
  classical
  let e := (Fintype.equivFin (Selected K P)).symm
  refine ⟨Fintype.card (Selected K P), (fun k j => (corner (e k).val j : ℝ)),
    (fun k j => (corner (e k).val j : ℝ) + 1), ?_⟩
  ext x
  constructor
  · rintro ⟨a, ha, hx⟩
    exact ⟨e.symm ⟨a, ha⟩, by simpa [OpenBin] using hx⟩
  · rintro ⟨k, hk⟩
    exact ⟨(e k).val, (e k).property, hk⟩

theorem cube_finiteBox : PublishedInputs.IsFiniteBoxUnion {x : Fin q → ℝ | Cube K x} := by
  refine ⟨1, (fun _ _ => 0), (fun _ _ => (K : ℝ)), ?_⟩
  ext x
  simp [Cube]

theorem selectedBins_closure (P : (Fin q → ℤ) → Prop) :
    closure (selectedBins K P) ⊆ ambientBox q K := by
  apply isClosed_Icc.closure_subset_iff.mpr
  rintro x ⟨a, _, hx⟩
  exact binSet_subset_ambient a hx

theorem selectedBins_integral (P : (Fin q → ℤ) → Prop) (ρ : (Fin q → ℝ) → ℝ)
    (hi : IntegrableOn ρ (ambientBox q K)) :
    (∫ x in selectedBins K P, ρ x) = ∑ a : Selected K P, ∫ x in binSet a.val, ρ x := by
  have heq : selectedBins K P = ⋃ a : Selected K P, binSet a.val := by
    ext x
    simp only [selectedBins, binSet, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨a, ha, hx⟩
      exact ⟨⟨a, ha⟩, hx⟩
    · rintro ⟨a, hx⟩
      exact ⟨a.val, a.property, hx⟩
  rw [heq]
  apply integral_iUnion_fintype
  · exact fun a => binSet_measurable a.val
  · intro a b hab
    exact binSet_disjoint a.val b.val (fun h => hab (Subtype.ext h))
  · exact fun a => hi.mono_set (binSet_subset_ambient a.val)

/-- The selected side has at least one quarter of its own discrete mass;
it need not be the smaller side for the discrete weights. -/
theorem selectedBins_mass_lower (P : (Fin q → ℤ) → Prop) (ρ : (Fin q → ℝ) → ℝ)
    (w : Grid (I := Fin q) K → ℝ) (hi : IntegrableOn ρ (ambientBox q K))
    (hbin : ∀ a x, x ∈ binSet a → w a / 4 ≤ ρ x) :
    (∑ a : Selected K P, w a.val) / 4 ≤ ∫ x in selectedBins K P, ρ x := by
  rw [selectedBins_integral P ρ hi, Finset.sum_div]
  apply Finset.sum_le_sum
  intro a _
  have h := setIntegral_ge_of_const_le_real (binSet_measurable a.val)
    (show volume (binSet a.val) ≠ ⊤ by rw [binSet_volume]; simp)
    (hbin a.val) (hi.mono_set (binSet_subset_ambient a.val))
  simpa [Measure.real, binSet_volume] using h

theorem edgeTube_mass_upper (P : (Fin q → ℤ) → Prop) (e : CutEdge K P)
    (r : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 4)
    (hsize : (q - 1 : ℕ) * (2 * r) ≤ (1 / 2 : ℝ))
    (ρ : (Fin q → ℝ) → ℝ) (w : Grid (I := Fin q) K → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hi : IntegrableOn ρ (ambientBox q K))
    (hbound : ∀ x, x ∈ edgeTube e r ∩ {x | Cube K x} →
      ρ x ≤ 4 * min (w e.val.1) (w e.val.2.1)) :
    (∫ x in edgeTube e r ∩ {x | Cube K x}, ρ x) ≤
      4 * min (w e.val.1) (w e.val.2.1) := by
  let E := edgeTube e r ∩ {x | Cube K x}
  have hE : MeasurableSet E := (faceTube_measurable _ _ _).inter
    (cube_finiteBox (q := q) (K := K)).isOpen.measurableSet
  have hsub : E ⊆ ambientBox q K := fun x hx =>
    ⟨fun j => (hx.2 j).1.le, fun j => (hx.2 j).2.le⟩
  have hfin : volume (edgeTube e r) ≠ ⊤ := by
    rw [edgeTube, faceTube_volume _ _ _ hr]
    exact ENNReal.ofReal_ne_top
  have hfinE : volume E ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hvol : (volume E).toReal ≤ 1 := by
    calc
      _ ≤ (volume (edgeTube e r)).toReal := ENNReal.toReal_mono hfin
        (measure_mono Set.inter_subset_left)
      _ ≤ 1 := by
        exact faceTube_volume_le_one (corner e.val.1) e.val.2.2 r hr hr₁ (by simpa using hsize)
  have hb := setIntegral_mono_on (hi.mono_set hsub)
    (integrableOn_const hfinE) hE hbound
  rw [setIntegral_const, smul_eq_mul] at hb
  have hw' : 0 ≤ 4 * min (w e.val.1) (w e.val.2.1) :=
    mul_nonneg (by norm_num) (le_min (hw _) (hw _))
  exact hb.trans (by simpa [Measure.real] using mul_le_mul_of_nonneg_right hvol hw')

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridConductance
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conditional weighted grid-cut estimate

The finite-box Prékopa input is the only published hypothesis here. The
shell cover, tube volume, integral cover, and discrete/continuous mass
comparison yield the discrete cut estimate.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators

/-- The actual weighted cut bound before the proposal probability is
inserted. The selected side is the smaller continuous side; the conclusion
uses its own discrete weight and therefore also bounds the smaller discrete
side without identifying the two notions of smaller side. -/
theorem weighted_cut_of_interpolation {q K : ℕ}
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (P : (Fin q → ℤ) → Prop) (t : ℝ) (ht : 0 < t) (ht₁ : t < 1)
    (hr : t * K ≤ 1 / 4) (hsize : (q - 1 : ℕ) * (2 * (t * K)) ≤ (1 / 2 : ℝ))
    (ρ : (Fin q → ℝ) → ℝ) (w : Grid (I := Fin q) K → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hρ : ContinuousOn ρ (ambientBox q K))
    (hpos : ∀ x ∈ ambientBox q K, 0 < ρ x)
    (hlc : PublishedInputs.LogConcaveOn ρ (ambientBox q K))
    (hbin : ∀ a x, x ∈ binSet a → w a / 4 ≤ ρ x)
    (htube : ∀ (e : CutEdge K P) x, x ∈ edgeTube e (t * K) ∩ {x | Cube K x} →
      ρ x ≤ 4 * min (w e.val.1) (w e.val.2.1))
    (hSmass : 0 < ∫ x in selectedBins K P, ρ x)
    (hcut : 2 * (∫ x in selectedBins K P, ρ x) ≤ ∫ x in {x | Cube K x}, ρ x) :
    (((2 : ℝ) ^ t - 1) / 16) * (∑ a : Selected K P, w a.val) ≤
      ∑ e : CutEdge K P, min (w e.val.1) (w e.val.2.1) := by
  let S := selectedBins K P
  let D := {x : Fin q → ℝ | Cube K x}
  let M := PublishedInputs.interpolate t S D
  let E : CutEdge K P → Set (Fin q → ℝ) := fun e => edgeTube e (t * K) ∩ D
  have hS := selectedBins_finiteBox (K := K) P
  have hD := cube_finiteBox (q := q) (K := K)
  have hM := hS.interpolate hD t ht ht₁
  have hMsub : M ⊆ D := by
    rintro z ⟨x, ⟨a, _, hx⟩, y, hy, rfl⟩
    have hx' := openBin_in_cube a x hx
    intro j
    have hxt := mul_pos (sub_pos.mpr ht₁) (hx' j).1
    have hyt := mul_pos ht (hy j).1
    have hxu := mul_lt_mul_of_pos_left (hx' j).2 (sub_pos.mpr ht₁)
    have hyu := mul_lt_mul_of_pos_left (hy j).2 ht
    change 0 < (1 - t) * x j + t * y j ∧ (1 - t) * x j + t * y j < (K : ℝ)
    constructor <;> nlinarith
  have hsub : S ⊆ M := by
    rintro x hx
    refine ⟨x, hx, x, ?_, ?_⟩
    · obtain ⟨a, _, ha⟩ := hx
      exact openBin_in_cube a x ha
    · ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hi : IntegrableOn ρ (ambientBox q K) := hρ.integrableOn_Icc
  have hMc : closure M ⊆ ambientBox q K :=
    PublishedInputs.interpolation_closure_in_box
      (selectedBins_closure P) cube_closure t ht.le ht₁.le
  have hiShell : IntegrableOn ρ (M \ S) := hi.mono_set
    (fun x hx => hMc (subset_closure hx.1))
  have hcover : ∀ᵐ x ∂volume, x ∈ M \ S → ∃ e, x ∈ E e := by
    have hc := interpolation_shell_cover_ae P t ht ht₁ (show t * K ≤ 1 by linarith)
    filter_upwards [hc] with x hx
    intro hxS
    obtain ⟨e, he⟩ := hx hxS
    exact ⟨e, he, hMsub hxS.1⟩
  have hESub (e : CutEdge K P) : E e ⊆ ambientBox q K :=
    fun x hx => ⟨fun j => (hx.2 j).1.le, fun j => (hx.2 j).2.le⟩
  have hEm (e : CutEdge K P) : MeasurableSet (E e) :=
    (faceTube_measurable _ _ _).inter hD.isOpen.measurableSet
  have hcoverInt := ContingencyTables.integral_finite_cover (M \ S) E ρ
    (hM.isOpen.measurableSet.diff hS.isOpen.measurableSet) hEm hiShell
    (fun e => hi.mono_set (hESub e))
    (fun e x hx => (hpos x (hESub e hx)).le) hcover
  have hr₀ : 0 ≤ t * (K : ℝ) := mul_nonneg ht.le (Nat.cast_nonneg _)
  have hupper : (∫ x in M \ S, ρ x) ≤
      4 * ∑ e : CutEdge K P, min (w e.val.1) (w e.val.2.1) := by
    calc
      _ ≤ ∑ e : CutEdge K P, ∫ x in E e, ρ x := hcoverInt
      _ ≤ ∑ e : CutEdge K P, 4 * min (w e.val.1) (w e.val.2.1) := by
        apply Finset.sum_le_sum
        intro e _
        exact edgeTube_mass_upper P e (t * K) hr₀ hr hsize ρ w hw hi (htube e)
      _ = _ := by rw [Finset.mul_sum]
  have hgain := PublishedInputs.interpolation_shell_gain hPL t ht ht₁
    (fun _ => 0) (fun _ => (K : ℝ)) S D ρ hS hD
    (selectedBins_closure P) cube_closure hρ hpos hlc hsub hSmass hcut
  have hlower := selectedBins_mass_lower P ρ w hi hbin
  have hg : 0 ≤ (2 : ℝ) ^ t - 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ht.le
    exact sub_nonneg.mpr (by simpa using h)
  have hscaled := mul_le_mul_of_nonneg_left hlower hg
  dsimp only [S, D, M] at hupper hgain
  nlinarith

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseGrid
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conductance geometry for the actual dense penalty

The free table coordinates are reindexed by `Fin q`. The bin and cut-tube
density comparisons below follow from the actual margins and integer
widths. Thus the weighted cut theorem has no assumed penalty regularity
or bin comparison when used for the dense completion sampler.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseGridPenalty (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (x : Fin q → ℝ) : ℝ :=
  DenseAffine.densePenalty R P d (fun p => x (e p))

theorem denseGridPenalty_continuous (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (e : I × J ≃ Fin q) : Continuous (denseGridPenalty R P d e) := by
  exact (DenseAffine.densePenalty_continuous R P d).comp
    (continuous_pi fun p => continuous_apply (e p))

theorem denseGridPenalty_convex (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (e : I × J ≃ Fin q) :
    ConvexOn ℝ Set.univ (denseGridPenalty R P d e) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  exact (DenseAffine.densePenalty_convex R P d Set.univ convex_univ).2
    (Set.mem_univ _) (Set.mem_univ _) ha hb hab

theorem denseGridPenalty_change (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (x y : Fin q → ℝ) (r : ℝ) (hr : 0 ≤ r) (hxy : ∀ j, |x j - y j| ≤ r) :
    |(d : ℝ) ^ 4 * denseGridPenalty R P d e x -
      (d : ℝ) ^ 4 * denseGridPenalty R P d e y| ≤ r :=
  DenseAffine.densePenalty_scaled_change R P d hd hR hP hRmax hPmax hfree
    _ _ r hr (fun p => hxy (e p))

theorem closedBin_distance {K : ℕ} (a : Grid (I := Fin q) K)
    (x : Fin q → ℝ) (hx : ClosedBin (corner a) x) :
    ∀ j, |x j - realCorner a j| ≤ 1 := by
  intro j
  change |x j - (corner a j : ℝ)| ≤ 1
  apply abs_le.mpr
  constructor <;> linarith [(hx j).1, (hx j).2]

theorem tube_distances {K : ℕ} {Q : (Fin q → ℤ) → Prop}
    (edge : CutEdge K Q) (r : ℝ) (_hr : 0 ≤ r) (x : Fin q → ℝ)
    (hx : x ∈ edgeTube edge r) :
    (∀ j, |x j - realCorner edge.val.1 j| ≤ 1 + r) ∧
      (∀ j, |x j - realCorner edge.val.2.1 j| ≤ 1 + r) := by
  have hcoord (j : Fin q) := hx j (Set.mem_univ j)
  constructor
  · intro j
    have h := hcoord j
    dsimp [tubeLower, tubeUpper] at h
    change |x j - (corner edge.val.1 j : ℝ)| ≤ 1 + r
    by_cases hj : j = edge.val.2.2
    · subst j
      simp only [ite_true, if_true] at h
      apply abs_le.mpr
      constructor <;> linarith [h.1, h.2]
    · simp only [ite_eq_right hj] at h
      apply abs_le.mpr
      constructor <;> linarith [h.1, h.2]
  · intro j
    have h := hcoord j
    dsimp [tubeLower, tubeUpper] at h
    change |x j - (corner edge.val.2.1 j : ℝ)| ≤ 1 + r
    by_cases hj : j = edge.val.2.2
    · have hadj : (corner edge.val.2.1 j : ℝ) =
          (corner edge.val.1 j : ℝ) + 1 := by
        simpa only [hj, Int.cast_add, Int.cast_one] using
          congrArg (fun z : ℤ => (z : ℝ)) edge.property.1.1
      simp only [ite_eq_left hj] at h
      rw [hadj]
      apply abs_le.mpr
      constructor <;> linarith [h.1, h.2]
    · have heq : corner edge.val.2.1 j = corner edge.val.1 j :=
        congrArg Subtype.val (edge.property.1.2 j hj)
      simp only [ite_eq_right hj] at h
      rw [heq]
      apply abs_le.mpr
      constructor <;> linarith [h.1, h.2]

theorem denseGrid_bin_comparison (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    {K : ℕ} (a : Grid (I := Fin q) K) (x : Fin q → ℝ)
    (hx : ClosedBin (corner a) x) :
    DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner a) / 4 ≤
        DenseWeights.density ((d : ℝ) ^ 4) (denseGridPenalty R P d e) x ∧
      DenseWeights.density ((d : ℝ) ^ 4) (denseGridPenalty R P d e) x ≤
        2 * DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner a) :=
  DenseWeights.bin_density_comparison _ _ _ _
    (denseGridPenalty_change R P d hd hR hP hRmax hPmax hfree e x _ 1
      (by norm_num) (closedBin_distance a x hx))

theorem denseGrid_tube_comparison (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    {K : ℕ} {Q : (Fin q → ℤ) → Prop} (edge : CutEdge K Q) (r : ℝ)
    (hr : 0 ≤ r) (hr₁ : r ≤ 1) (x : Fin q → ℝ) (hx : x ∈ edgeTube edge r) :
    DenseWeights.density ((d : ℝ) ^ 4) (denseGridPenalty R P d e) x ≤
      4 * min
        (DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner edge.val.1))
        (DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner edge.val.2.1)) := by
  obtain ⟨hlo, hhi⟩ := tube_distances edge r hr x hx
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
  apply le_min
  · apply DenseWeights.tube_density_comparison
    exact (denseGridPenalty_change R P d hd hR hP hRmax hPmax hfree e x _ (1 + r)
      (by positivity) hlo).trans (by linarith)
  · apply DenseWeights.tube_density_comparison
    exact (denseGridPenalty_change R P d hd hR hP hRmax hPmax hfree e x _ (1 + r)
      (by positivity) hhi).trans (by linarith)

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridPartition
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Partition of cube mass by the finite bins

The union misses only grid hyperplanes. Thus a predicate and its complement
have continuous masses summing to the cube mass, which lets the conductance
argument select the smaller continuous side.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators

variable {q K : ℕ}

theorem cube_ae_all_bins :
    {x : Fin q → ℝ | Cube K x} =ᵐ[volume] selectedBins K (fun _ => True) := by
  filter_upwards [ae_off_grid (I := Fin q)] with x hoff
  apply propext
  constructor
  · intro hx
    have hb (j : Fin q) : ⌊x j⌋ ∈ Set.Icc (0 : ℤ) ((K : ℤ) - 1) := by
      refine ⟨Int.floor_nonneg.mpr (hx j).1.le, ?_⟩
      have hlt : ⌊x j⌋ < (K : ℤ) := Int.floor_lt.mpr (by simpa using (hx j).2)
      omega
    refine ⟨(fun j => ⟨⌊x j⌋, hb j⟩), trivial, ?_⟩
    intro j
    exact ⟨lt_of_le_of_ne (Int.floor_le _) (Ne.symm (hoff j _)), Int.lt_floor_add_one _⟩
  · rintro ⟨a, _, ha⟩
    exact openBin_in_cube a x ha

theorem cube_integral_bins (ρ : (Fin q → ℝ) → ℝ)
    (hi : IntegrableOn ρ (ambientBox q K)) :
    (∫ x in {x | Cube K x}, ρ x) =
      ∑ a : Grid (I := Fin q) K, ∫ x in binSet a, ρ x := by
  rw [setIntegral_congr_set cube_ae_all_bins, selectedBins_integral _ ρ hi]
  simpa only using
    (Finset.sum_subtype Finset.univ (fun _ => by simp)
      (fun a : Grid (I := Fin q) K => ∫ x in binSet a, ρ x)).symm

theorem selected_complement_integral (Q : (Fin q → ℤ) → Prop)
    (ρ : (Fin q → ℝ) → ℝ) (hi : IntegrableOn ρ (ambientBox q K)) :
    (∫ x in selectedBins K Q, ρ x) +
        (∫ x in selectedBins K (fun a => ¬ Q a), ρ x) =
      ∫ x in {x | Cube K x}, ρ x := by
  classical
  rw [selectedBins_integral Q ρ hi, selectedBins_integral (fun a => ¬ Q a) ρ hi,
    cube_integral_bins ρ hi]
  have hQ (Q : (Fin q → ℤ) → Prop) :
      (∑ a : Selected K Q, ∫ x in binSet a.val, ρ x) =
        ∑ a ∈ Finset.univ.filter (fun a : Grid (I := Fin q) K => Q (corner a)),
          ∫ x in binSet a, ρ x := by
    exact (Finset.sum_subtype (p := fun a : Grid (I := Fin q) K => Q (corner a))
      (F := instFintypeSelected Q)
      (Finset.univ.filter (fun a : Grid (I := Fin q) K => Q (corner a)))
      (fun a => by simp) (fun a => ∫ x in binSet a, ρ x)).symm
  rw [hQ Q, hQ (fun a => ¬ Q a)]
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : Q (corner a) <;> simp [h]

theorem selected_mass_positive (Q : (Fin q → ℤ) → Prop)
    (ρ : (Fin q → ℝ) → ℝ) (w : Grid (I := Fin q) K → ℝ)
    (hw : ∀ a, 0 < w a) (hi : IntegrableOn ρ (ambientBox q K))
    (hbin : ∀ a x, x ∈ binSet a → w a / 4 ≤ ρ x)
    (hne : Nonempty (Selected K Q)) : 0 < ∫ x in selectedBins K Q, ρ x := by
  have hs : 0 < ∑ a : Selected K Q, w a.val := by
    obtain ⟨a⟩ := hne
    apply Finset.sum_pos'
    · intro b _
      exact (hw b.val).le
    · exact ⟨a, Finset.mem_univ _, hw a.val⟩
  exact (div_pos hs (by norm_num)).trans_le (selectedBins_mass_lower Q ρ w hi hbin)

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridMinCut
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Every nontrivial cut of the actual dense grid

Choosing the smaller continuous side and then comparing its own discrete
mass gives a lower bound using the smaller discrete side. No assumption
identifying those two choices is made.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

variable {q K : ℕ}

def cutComplementEquiv (Q : (Fin q → ℤ) → Prop) :
    CutEdge K Q ≃ CutEdge K (fun a => ¬ Q a) where
  toFun e := ⟨e.val, e.property.1, not_congr e.property.2⟩
  invFun e := ⟨e.val, e.property.1, by simpa only [not_not] using not_congr e.property.2⟩
  left_inv e := Subtype.ext rfl
  right_inv e := Subtype.ext rfl

theorem cut_complement_sum (Q : (Fin q → ℤ) → Prop) (w : Grid (I := Fin q) K → ℝ) :
    (∑ e : CutEdge K Q, min (w e.val.1) (w e.val.2.1)) =
      ∑ e : CutEdge K (fun a => ¬ Q a), min (w e.val.1) (w e.val.2.1) := by
  exact Fintype.sum_equiv (cutComplementEquiv Q) _ _ (fun _ => rfl)

theorem weighted_min_cut (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (Q : (Fin q → ℤ) → Prop) (t : ℝ) (ht : 0 < t) (ht₁ : t < 1)
    (hr : t * K ≤ 1 / 4) (hsize : (q - 1 : ℕ) * (2 * (t * K)) ≤ (1 / 2 : ℝ))
    (ρ : (Fin q → ℝ) → ℝ) (w : Grid (I := Fin q) K → ℝ)
    (hw : ∀ a, 0 < w a) (hρ : ContinuousOn ρ (ambientBox q K))
    (hpos : ∀ x ∈ ambientBox q K, 0 < ρ x)
    (hlc : PublishedInputs.LogConcaveOn ρ (ambientBox q K))
    (hbin : ∀ a x, x ∈ binSet a → w a / 4 ≤ ρ x)
    (htube : ∀ (edge : CutEdge K Q) x,
      x ∈ edgeTube edge (t * K) ∩ {x | Cube K x} →
        ρ x ≤ 4 * min (w edge.val.1) (w edge.val.2.1))
    (hne : Nonempty (Selected K Q)) (hne' : Nonempty (Selected K (fun a => ¬ Q a))) :
    (((2 : ℝ) ^ t - 1) / 16) *
        min (∑ a : Selected K Q, w a.val) (∑ a : Selected K (fun b => ¬ Q b), w a.val) ≤
      ∑ edge : CutEdge K Q, min (w edge.val.1) (w edge.val.2.1) := by
  have hi : IntegrableOn ρ (ambientBox q K) := hρ.integrableOn_Icc
  have hsum := selected_complement_integral Q ρ hi
  have hc : 0 ≤ ((2 : ℝ) ^ t - 1) / 16 := by
    have hg := two_rpow_gain t ht.le
    exact div_nonneg ((show (0 : ℝ) ≤ t / 2 by positivity).trans hg) (by norm_num)
  by_cases hcut : 2 * (∫ x in selectedBins K Q, ρ x) ≤ ∫ x in {x | Cube K x}, ρ x
  · calc
      _ ≤ (((2 : ℝ) ^ t - 1) / 16) * (∑ a : Selected K Q, w a.val) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hc
      _ ≤ _ := weighted_cut_of_interpolation hPL Q t ht ht₁ hr hsize ρ w
        (fun a => (hw a).le) hρ hpos hlc hbin htube
        (selected_mass_positive Q ρ w hw hi hbin hne) hcut
  · have hcut' : 2 * (∫ x in selectedBins K (fun a => ¬ Q a), ρ x) ≤
        ∫ x in {x | Cube K x}, ρ x := by linarith
    have htube' (edge : CutEdge K (fun a => ¬ Q a)) (x : Fin q → ℝ)
        (hx : x ∈ edgeTube edge (t * K) ∩ {x | Cube K x}) :
        ρ x ≤ 4 * min (w edge.val.1) (w edge.val.2.1) :=
      htube ((cutComplementEquiv Q).symm edge) x hx
    calc
      _ ≤ (((2 : ℝ) ^ t - 1) / 16) * (∑ a : Selected K (fun b => ¬ Q b), w a.val) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hc
      _ ≤ ∑ edge : CutEdge K (fun a => ¬ Q a), min (w edge.val.1) (w edge.val.2.1) :=
        weighted_cut_of_interpolation hPL (fun a => ¬ Q a) t ht ht₁ hr hsize ρ w
          (fun a => (hw a).le) hρ hpos hlc hbin htube'
          (selected_mass_positive (fun a => ¬ Q a) ρ w hw hi hbin hne') hcut'
      _ = _ := (cut_complement_sum Q w).symm

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The actual dense sampler's dyadic weights satisfy every nontrivial
cut bound, with the manuscript interpolation parameter. -/
theorem denseGrid_min_cut (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q) (hK : 1 ≤ K)
    (Q : (Fin q → ℤ) → Prop)
    (hne : Nonempty (Selected K Q)) (hne' : Nonempty (Selected K (fun a => ¬ Q a))) :
    (1 / (128 * (d : ℝ) * K)) * min
        (∑ a : Selected K Q, DenseWeights.binWeight ((d : ℝ) ^ 4)
          (denseGridPenalty R P d e) (realCorner a.val))
        (∑ a : Selected K (fun b => ¬ Q b), DenseWeights.binWeight ((d : ℝ) ^ 4)
          (denseGridPenalty R P d e) (realCorner a.val)) ≤
      ∑ edge : CutEdge K Q, min
        (DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner edge.val.1))
        (DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner edge.val.2.1)) := by
  let p := denseGridPenalty R P d e
  let w := fun a : Grid (I := Fin q) K => DenseWeights.binWeight ((d : ℝ) ^ 4) p (realCorner a)
  let ρ := DenseWeights.density ((d : ℝ) ^ 4) p
  have hq : q ≤ d := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin] at hc
    omega
  obtain ⟨ht, ht₁, hr, hsize⟩ := denseInterpolation_bounds d K q hd hK hq
  have hbound := weighted_min_cut hPL Q (denseInterpolation d K) ht ht₁ hr hsize ρ w
    (fun a => DenseWeights.binWeight_pos _ _ _)
    ((DenseWeights.density_continuous _ _ (denseGridPenalty_continuous R P d e)).continuousOn)
    (fun x _ => DenseWeights.density_pos _ _ _) (fun x _ y _ t ht ht₁ =>
      DenseWeights.density_logConcave _ (by positivity) _ Set.univ
        (denseGridPenalty_convex R P d e) x (Set.mem_univ _) y (Set.mem_univ _) t ht ht₁)
    (fun a x hx => (denseGrid_bin_comparison R P d hd hR hP hRmax hPmax hfree e a x
      (fun j => ⟨(hx j).1.le, (hx j).2.le⟩)).1)
    (fun edge x hx => denseGrid_tube_comparison R P d hd hR hP hRmax hPmax hfree e edge
      (denseInterpolation d K * K) (mul_nonneg ht.le (Nat.cast_nonneg _)) (by linarith) x hx.1)
    hne hne'
  have hs : 0 ≤ min (∑ a : Selected K Q, w a.val)
      (∑ a : Selected K (fun b => ¬ Q b), w a.val) := by
    apply le_min <;> exact Finset.sum_nonneg (fun a _ => (DenseWeights.binWeight_pos _ _ _).le)
  have hgain := two_rpow_gain (denseInterpolation d K) ht.le
  have hd₀ : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hK₀ : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  calc
    _ = (denseInterpolation d K / 32) * min
        (∑ a : Selected K Q, w a.val) (∑ a : Selected K (fun b => ¬ Q b), w a.val) := by
      unfold denseInterpolation
      congr 1
      field_simp [hd₀, hK₀]
      norm_num
    _ ≤ (((2 : ℝ) ^ denseInterpolation d K - 1) / 16) * min
        (∑ a : Selected K Q, w a.val) (∑ a : Selected K (fun b => ¬ Q b), w a.val) :=
      mul_le_mul_of_nonneg_right (by linarith) hs
    _ ≤ _ := hbound

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridAdjacency
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual axis neighbours and the `2q` proposal-degree bound -/

namespace ContingencyTables.GridBoundary

open scoped Classical

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] {K : ℕ}

def OrientedNeighbor (a b : Grid (I := I) K) (i : I) (sign : Bool) : Prop :=
  if sign then IsGridEdge (a, b, i) else IsGridEdge (b, a, i)

def Neighbor (a b : Grid (I := I) K) : Prop := ∃ i sign, OrientedNeighbor a b i sign

omit [Fintype I] [DecidableEq I] in
theorem neighbor_symm (a b : Grid (I := I) K) : Neighbor a b ↔ Neighbor b a := by
  constructor <;> rintro ⟨i, sign, h⟩ <;> refine ⟨i, !sign, ?_⟩ <;>
    cases sign <;> exact h

omit [Fintype I] [DecidableEq I] in
theorem oriented_target_unique (a b c : Grid (I := I) K) (i : I) (sign : Bool)
    (hb : OrientedNeighbor a b i sign) (hc : OrientedNeighbor a c i sign) : b = c := by
  funext j
  apply Subtype.ext
  change corner b j = corner c j
  cases sign <;> change IsGridEdge _ at hb hc
  · by_cases hj : j = i
    · subst j
      have hbi : corner a i = corner b i + 1 := hb.1
      have hci : corner a i = corner c i + 1 := hc.1
      omega
    · have hbj := congrArg Subtype.val (hb.2 j hj)
      have hcj := congrArg Subtype.val (hc.2 j hj)
      exact hbj.symm.trans hcj
  · by_cases hj : j = i
    · subst j
      exact hb.1.trans hc.1.symm
    · have hbj := congrArg Subtype.val (hb.2 j hj)
      have hcj := congrArg Subtype.val (hc.2 j hj)
      exact hbj.trans hcj.symm

def neighborDirection (a : Grid (I := I) K) (b : {b // Neighbor a b}) : I × Bool :=
  ⟨Classical.choose b.property, Classical.choose (Classical.choose_spec b.property)⟩

omit [Fintype I] [DecidableEq I] in
theorem neighborDirection_spec (a : Grid (I := I) K) (b : {b // Neighbor a b}) :
    OrientedNeighbor a b.val (neighborDirection a b).1 (neighborDirection a b).2 :=
  Classical.choose_spec (Classical.choose_spec b.property)

omit [Fintype I] [DecidableEq I] in
theorem neighborDirection_injective (a : Grid (I := I) K) :
    Function.Injective (neighborDirection a) := by
  intro b c h
  have hi := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  apply Subtype.ext
  apply oriented_target_unique a b.val c.val (neighborDirection a b).1 (neighborDirection a b).2
    (neighborDirection_spec a b)
  simpa only [hi, hs] using neighborDirection_spec a c

theorem neighbor_degree (a : Grid (I := I) K) :
    (Finset.univ.filter (Neighbor a)).card ≤ 2 * Fintype.card I := by
  have h := Fintype.card_le_of_injective (neighborDirection a) (neighborDirection_injective a)
  rw [Fintype.card_subtype] at h
  simpa only [Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using h

omit [Fintype I] [DecidableEq I] in
theorem edge_axis_unique (a b : Grid (I := I) K) (i j : I)
    (hi : IsGridEdge (a, b, i)) (hj : IsGridEdge (a, b, j)) : i = j := by
  by_contra h
  have heq : corner b i = corner a i := congrArg Subtype.val (hj.2 i h)
  have hplus : corner b i = corner a i + 1 := hi.1
  omega

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridCutFlow
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From geometric cut faces to Metropolis cut flow -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical

noncomputable section

variable {q K : ℕ}

theorem edge_not_reverse (a b : Grid (I := Fin q) K) (i j : Fin q)
    (hi : IsGridEdge (a, b, i)) (hj : IsGridEdge (b, a, j)) : False := by
  by_cases h : i = j
  · subst j
    have ha : corner b i = corner a i + 1 := hi.1
    have hb : corner a i = corner b i + 1 := hj.1
    omega
  · have heq : corner a i = corner b i := congrArg Subtype.val (hj.2 i h)
    have hplus : corner b i = corner a i + 1 := hi.1
    omega

theorem cutEdge_eq {Q : (Fin q → ℤ) → Prop} (e f : CutEdge K Q)
    (ha : e.val.1 = f.val.1) (hb : e.val.2.1 = f.val.2.1) : e = f := by
  have hi : e.val.2.2 = f.val.2.2 := by
    apply edge_axis_unique e.val.1 e.val.2.1 _ _ e.property.1
    rw [ha, hb]
    exact f.property.1
  apply Subtype.ext
  exact Prod.ext ha (Prod.ext hb hi)

def cutPair (Q : (Fin q → ℤ) → Prop) (e : CutEdge K Q) :
    Selected K Q × Selected K (fun a => ¬ Q a) :=
  if h : Q (corner e.val.1) then
    (⟨e.val.1, h⟩, ⟨e.val.2.1, e.property.2.mp h⟩)
  else
    (⟨e.val.2.1, by
      by_contra hn
      exact h (e.property.2.mpr hn)⟩, ⟨e.val.1, h⟩)

theorem cutPair_neighbor (Q : (Fin q → ℤ) → Prop) (e : CutEdge K Q) :
    Neighbor (cutPair Q e).1.val (cutPair Q e).2.val := by
  unfold cutPair
  split_ifs
  · exact ⟨e.val.2.2, true, e.property.1⟩
  · exact ⟨e.val.2.2, false, e.property.1⟩

theorem cutPair_weight (Q : (Fin q → ℤ) → Prop) (w : Grid (I := Fin q) K → ℝ)
    (e : CutEdge K Q) :
    min (w (cutPair Q e).1.val) (w (cutPair Q e).2.val) =
      min (w e.val.1) (w e.val.2.1) := by
  unfold cutPair
  split_ifs <;> simp only [min_comm]

theorem cutPair_injective (Q : (Fin q → ℤ) → Prop) : Function.Injective (cutPair (K := K) Q) := by
  intro e f h
  have hp := congrArg (fun p : Selected K Q × Selected K (fun a => ¬ Q a) => p.1.val) h
  have hn := congrArg (fun p : Selected K Q × Selected K (fun a => ¬ Q a) => p.2.val) h
  by_cases he : Q (corner e.val.1) <;> by_cases hf : Q (corner f.val.1)
  · simp only [cutPair, dite_eq_left he, dite_eq_left hf] at hp hn
    exact cutEdge_eq e f hp hn
  · simp only [cutPair, dite_eq_left he, dite_eq_right hf] at hp hn
    exfalso
    apply edge_not_reverse e.val.1 e.val.2.1 e.val.2.2 f.val.2.2 e.property.1
    rw [hp, hn]
    exact f.property.1
  · simp only [cutPair, dite_eq_right he, dite_eq_left hf] at hp hn
    exfalso
    apply edge_not_reverse e.val.1 e.val.2.1 e.val.2.2 f.val.2.2 e.property.1
    rw [hp, hn]
    exact f.property.1
  · simp only [cutPair, dite_eq_right he, dite_eq_right hf] at hp hn
    exact cutEdge_eq e f hn hp

theorem selected_sum_eq_filter (Q : (Fin q → ℤ) → Prop) (f : Grid (I := Fin q) K → ℝ) :
    (∑ a : Selected K Q, f a.val) = ∑ a ∈ Finset.univ.filter (fun a => Q (corner a)), f a := by
  exact (Finset.sum_subtype (p := fun a : Grid (I := Fin q) K => Q (corner a))
    (F := instFintypeSelected Q) (Finset.univ.filter (fun a => Q (corner a)))
    (fun a => by simp) f).symm

/-- Every geometric cut face contributes its weight once to the actual
ordered cut flow. An injection suffices; no exterior or duplicate face is
counted in the conductance lower bound. -/
theorem cut_faces_le_neighbor_flow (Q : (Fin q → ℤ) → Prop)
    (w : Grid (I := Fin q) K → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (∑ e : CutEdge K Q, min (w e.val.1) (w e.val.2.1)) ≤
      ∑ a ∈ Finset.univ.filter (fun a : Grid (I := Fin q) K => Q (corner a)),
        ∑ b ∈ Finset.univ.filter (fun b : Grid (I := Fin q) K => ¬ Q (corner b)),
          if Neighbor a b then min (w a) (w b) else 0 := by
  calc
    _ ≤ ∑ p : Selected K Q × Selected K (fun a => ¬ Q a),
        if Neighbor p.1.val p.2.val then min (w p.1.val) (w p.2.val) else 0 := by
      refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ (Finset.univ.image (cutPair Q))) ?_)
      · rw [Finset.sum_image (fun x _ y _ h => cutPair_injective Q h)]
        apply Finset.sum_le_sum
        intro e _
        rw [ite_eq_left (cutPair_neighbor Q e), cutPair_weight]
      · intro p _ _
        split_ifs
        · exact le_min (hw _) (hw _)
        · exact le_rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      change (∑ a : Selected K Q, ∑ b : Selected K (fun a => ¬ Q a),
        if Neighbor a.val b.val then min (w a.val) (w b.val) else 0) = _
      rw [selected_sum_eq_filter Q (fun a => ∑ b : Selected K (fun a => ¬ Q a),
        if Neighbor a b.val then min (w a) (w b.val) else 0)]
      apply Finset.sum_congr rfl
      intro a _
      convert selected_sum_eq_filter (fun a => ¬ Q a)
        (fun b => if Neighbor a b then min (w a) (w b) else 0) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ext b
      simp

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridMetropolis
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual dyadic axis-proposal chain -/

namespace ContingencyTables.GridBoundary

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

theorem binProposal_bounds (d : ℕ) (hd : 14 ≤ d) :
    0 < binProposal d ∧ 1 / (16 * (d : ℝ)) ≤ binProposal d ∧
      binProposal d ≤ 1 / (8 * (d : ℝ)) := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hn : 1 < 8 * d := by omega
  have hlow := Nat.le_pow_clog (by decide : 1 < 2) (8 * d)
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn
  have hpos := Nat.clog_pos (by decide : 1 < 2) hn
  have hupp : 2 ^ Nat.clog 2 (8 * d) ≤ 16 * d := by
    have heq : 2 ^ Nat.clog 2 (8 * d) = 2 ^ (Nat.clog 2 (8 * d)).pred * 2 := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
      exact pow_succ _ _
    rw [heq]
    omega
  have hlow' : 8 * (d : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 (8 * d) := by exact_mod_cast hlow
  have hupp' : (2 : ℝ) ^ Nat.clog 2 (8 * d) ≤ 16 * (d : ℝ) := by exact_mod_cast hupp
  refine ⟨by unfold binProposal; positivity, ?_, ?_⟩
  · exact one_div_le_one_div_of_le (by positivity) hupp'
  · exact one_div_le_one_div_of_le (by positivity) hlow'

theorem binProposal_degree (q d : ℕ) (hd : 14 ≤ d) (hq : q ≤ d) :
    ((2 * q : ℕ) : ℝ) * binProposal d ≤ 1 / 4 := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hqd : (q : ℝ) ≤ d := by exact_mod_cast hq
  have hb := binProposal_bounds d hd
  calc
    _ ≤ (2 * (q : ℝ)) * (1 / (8 * (d : ℝ))) := by
      push_cast
      exact mul_le_mul_of_nonneg_left hb.2.2 (by positivity)
    _ ≤ (2 * (d : ℝ)) * (1 / (8 * (d : ℝ))) := by gcongr
    _ = 1 / 4 := by field_simp; ring

def gridChain {q K : ℕ} (d : ℕ) (hd : 14 ≤ d) (hq : q ≤ d) (hK : 1 ≤ K)
    (w : Grid (I := Fin q) K → ℝ) (hw : ∀ a, 0 < w a) : FiniteChain (Grid (I := Fin q) K) := by
  letI : Nonempty (Grid (I := Fin q) K) := ⟨fun _ => ⟨0, by constructor <;> omega⟩⟩
  exact MetropolisChain.chain w hw Neighbor neighbor_symm (binProposal d)
    (binProposal_bounds d hd).1.le (2 * q) (fun a => by simpa using neighbor_degree a)
    ((binProposal_degree q d hd hq).trans (by norm_num))

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisProposal
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer signed-coordinate proposals for the dense grid -/

namespace ContingencyTables.GridBoundary

open scoped Classical

variable {I : Type*} [DecidableEq I] {K : ℕ}

theorem axisStep_sound (a b : Grid (I := I) K) (i : I) (sign : Bool)
    (h : axisStep a i sign = some b) : OrientedNeighbor a b i sign := by
  cases sign
  · unfold axisStep at h
    simp only [Bool.false_eq_true, ite_false] at h
    split_ifs at h with hc
    · have hb := Option.some.inj h
      rw [← hb]
      change IsGridEdge _
      constructor
      · simp only [corner, Function.update_self]
        omega
      · intro j hj
        change j ≠ i at hj
        simp [Function.update_of_ne hj]
  · unfold axisStep at h
    simp only [ite_true, if_true] at h
    split_ifs at h with hc
    · have hb := Option.some.inj h
      rw [← hb]
      change IsGridEdge _
      constructor
      · simp [corner]
      · intro j hj
        change j ≠ i at hj
        simp [Function.update_of_ne hj]

theorem axisStep_complete (a b : Grid (I := I) K) (i : I) (sign : Bool)
    (h : OrientedNeighbor a b i sign) : axisStep a i sign = some b := by
  cases sign
  · change IsGridEdge (b, a, i) at h
    have hc : 0 ≤ corner a i - 1 := by
      have := (b i).property.1
      have he := h.1
      change corner a i = corner b i + 1 at he
      change 0 ≤ corner b i at this
      omega
    unfold axisStep
    simp only [Bool.false_eq_true, ite_false, dite_eq_left hc, Option.some.injEq]
    funext j
    apply Subtype.ext
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
      have he := h.1
      change corner a i = corner b i + 1 at he
      change corner a i - 1 = corner b i
      omega
    · simp only [Function.update_of_ne hj]
      exact congrArg Subtype.val (h.2 j hj)
  · change IsGridEdge (a, b, i) at h
    have hc : corner a i + 1 ≤ (K : ℤ) - 1 := by
      have := (b i).property.2
      have he := h.1
      change corner b i = corner a i + 1 at he
      change corner b i ≤ (K : ℤ) - 1 at this
      omega
    unfold axisStep
    simp only [ite_true, if_true, dite_eq_left hc, Option.some.injEq]
    funext j
    apply Subtype.ext
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
      exact h.1.symm
    · simp only [Function.update_of_ne hj]
      exact congrArg Subtype.val (h.2 j hj).symm

/-- Each neighbouring bin has exactly one signed-coordinate proposal. -/
theorem oriented_direction_unique (a b : Grid (I := I) K) (i j : I) (s t : Bool)
    (hi : OrientedNeighbor a b i s) (hj : OrientedNeighbor a b j t) : (i, s) = (j, t) := by
  have hij : i = j := by
    by_contra hne
    have he : corner a i = corner b i := by
      cases t
      · exact congrArg Subtype.val (hj.2 i hne)
      · exact (congrArg Subtype.val (hj.2 i hne)).symm
    cases s
    · have hp := hi.1
      change corner a i = corner b i + 1 at hp
      omega
    · have hp := hi.1
      change corner b i = corner a i + 1 at hp
      omega
  subst j
  have hst : s = t := by
    cases s <;> cases t
    · rfl
    · have h₁ := hi.1
      have h₂ := hj.1
      change corner a i = corner b i + 1 at h₁
      change corner b i = corner a i + 1 at h₂
      omega
    · have h₁ := hi.1
      have h₂ := hj.1
      change corner b i = corner a i + 1 at h₁
      change corner a i = corner b i + 1 at h₂
      omega
    · rfl
  subst t
  rfl

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisBits
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact proposal frequencies from a bounded fair-bit integer -/

namespace ContingencyTables.GridBoundary

open scoped Classical

theorem axisCodeStep_sound {q K M : ℕ} (a b : Grid (I := Fin q) K) (z : Fin M)
    (h : axisCodeStep a z = some b) : Neighbor a b := by
  unfold axisCodeStep at h
  split_ifs at h with hz
  exact ⟨_, _, axisStep_sound _ _ _ _ h⟩

theorem axisCodeStep_unique {q K M : ℕ} (a b : Grid (I := Fin q) K)
    (z z' : Fin M) (h : axisCodeStep a z = some b) (h' : axisCodeStep a z' = some b) : z = z' := by
  unfold axisCodeStep at h h'
  split_ifs at h with hz
  split_ifs at h' with hz'
  have hd := oriented_direction_unique a b _ _ _ _
    (axisStep_sound _ _ _ _ h) (axisStep_sound _ _ _ _ h')
  have he := congrArg (directionCodeEquiv q) hd
  have he' : (⟨z.val, hz⟩ : Fin (q * 2)) = ⟨z'.val, hz'⟩ := by
    simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using he
  exact Fin.ext (congrArg (fun x : Fin (q * 2) => x.val) he')

theorem axisCodeStep_exists {q K M : ℕ} (hM : q * 2 ≤ M)
    (a b : Grid (I := Fin q) K) (h : Neighbor a b) :
    ∃ z : Fin M, axisCodeStep a z = some b := by
  obtain ⟨i, sign, hi⟩ := h
  let dir := directionCodeEquiv q (i, sign)
  let z : Fin M := ⟨dir.val, dir.isLt.trans_le hM⟩
  refine ⟨z, ?_⟩
  unfold axisCodeStep
  have hz : z.val < q * 2 := dir.isLt
  rw [dite_eq_left hz]
  change axisStep a ((directionCodeEquiv q).symm dir).1
    ((directionCodeEquiv q).symm dir).2 = some b
  rw [Equiv.symm_apply_apply]
  exact axisStep_complete a b i sign hi

/-- Every valid signed direction has exactly one fair-bit integer code;
all unused codes and boundary steps are rejected. -/
theorem axisCodeStep_count {q K M : ℕ} (hM : q * 2 ≤ M)
    (a b : Grid (I := Fin q) K) :
    (Finset.univ.filter (fun z : Fin M => axisCodeStep a z = some b)).card =
      if Neighbor a b then 1 else 0 := by
  by_cases hab : Neighbor a b
  · rw [ite_eq_left hab, Finset.card_eq_one_iff_existsUnique]
    obtain ⟨z, hz⟩ := axisCodeStep_exists hM a b hab
    refine ⟨z, by simpa, ?_⟩
    intro z' hz'
    exact axisCodeStep_unique a b z' z (by simpa using hz') hz
  · rw [ite_eq_right hab, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hab (axisCodeStep_sound a b z (by simpa using hz))

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseChain
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conditional Poincaré bound for the actual dense bin chain

Both published inputs are explicit: finite-box Prékopa interpolation and
finite-chain Cheeger. All margin, penalty, cut, and proposal obligations
for this chain follow from the dense completion geometry.
-/

namespace ContingencyTables.GridBoundary

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q K : ℕ}

def denseBinWeight (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) : ℝ :=
  DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner a)

def denseBinChain (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hfree : Fintype.card (I × J) ≤ d)
    (e : I × J ≃ Fin q) (hK : 1 ≤ K) : FiniteChain (Grid (I := Fin q) K) := by
  have hq : q ≤ d := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin] at hc
    omega
  exact gridChain d hd hq hK (denseBinWeight R P d e) (fun a => DenseWeights.binWeight_pos _ _ _)

def denseCutConstant (d K : ℕ) : ℝ := binProposal d / (128 * (d : ℝ) * K)

theorem corner_injective : Function.Injective (corner (I := Fin q) (K := K)) := by
  intro a b h
  funext j
  apply Subtype.ext
  exact congrFun h j

theorem denseBinChain_poincare (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q) (hK : 1 ≤ K)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) K)) :
    ∀ f : Grid (I := Fin q) K → ℝ,
      (denseBinChain R P d hd hfree e hK).variance f ≤
        (2 / (denseCutConstant d K) ^ 2) * (denseBinChain R P d hd hfree e hK).energy f := by
  classical
  let : DecidableEq (Grid (I := Fin q) K) := Classical.decEq _
  let : Nonempty (Grid (I := Fin q) K) := ⟨fun _ => ⟨0, by constructor <;> omega⟩⟩
  let w := denseBinWeight R P d e (K := K)
  have hw : ∀ a, 0 < w a := fun a => DenseWeights.binWeight_pos _ _ _
  have hq : q ≤ d := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin] at hc
    omega
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hK₀ : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hβ := (binProposal_bounds d hd).1
  have hκ : 0 < denseCutConstant d K := by unfold denseCutConstant; positivity
  apply MetropolisChain.poincare_of_weighted_cut w hw Neighbor neighbor_symm (binProposal d) hβ.le
    (2 * q) (fun a => by simpa using neighbor_degree a)
    ((binProposal_degree q d hd hq).trans (by norm_num)) hCheeger (denseCutConstant d K) hκ
  intro S
  change denseCutConstant d K * min (∑ a ∈ S, w a) (∑ a ∈ Sᶜ, w a) ≤
    binProposal d * (∑ a ∈ S, ∑ b ∈ Sᶜ, if Neighbor a b then min (w a) (w b) else 0)
  have hSw : 0 ≤ ∑ a ∈ S, w a := Finset.sum_nonneg (fun a _ => (hw a).le)
  have hScw : 0 ≤ ∑ a ∈ Sᶜ, w a := Finset.sum_nonneg (fun a _ => (hw a).le)
  by_cases hs : S.Nonempty
  · by_cases hsc : Sᶜ.Nonempty
    · let Q : (Fin q → ℤ) → Prop := fun z => ∃ a ∈ S, corner a = z
      have hQ (a : Grid (I := Fin q) K) : Q (corner a) ↔ a ∈ S := by
        constructor
        · rintro ⟨b, hb, he⟩
          exact corner_injective he ▸ hb
        · intro ha
          exact ⟨a, ha, rfl⟩
      have hne : Nonempty (Selected K Q) := by
        obtain ⟨a, ha⟩ := hs
        exact ⟨⟨a, (hQ a).mpr ha⟩⟩
      have hne' : Nonempty (Selected K (fun a => ¬ Q a)) := by
        obtain ⟨a, ha⟩ := hsc
        exact ⟨⟨a, fun h => (Finset.mem_compl.mp ha) ((hQ a).mp h)⟩⟩
      have hdense := denseGrid_min_cut R P d hd hR hP hRmax hPmax hfree e hPL hK Q hne hne'
      change (1 / (128 * (d : ℝ) * K)) *
        min (∑ a : Selected K Q, w a.val) (∑ a : Selected K (fun a => ¬ Q a), w a.val) ≤
          ∑ edge : CutEdge K Q, min (w edge.val.1) (w edge.val.2.1) at hdense
      have hsum : (∑ a : Selected K Q, w a.val) = ∑ a ∈ S, w a := by
        rw [selected_sum_eq_filter Q w]
        apply Finset.sum_congr ?_ (fun _ _ => rfl)
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hQ]
      have hsum' : (∑ a : Selected K (fun a => ¬ Q a), w a.val) = ∑ a ∈ Sᶜ, w a := by
        rw [selected_sum_eq_filter (fun a => ¬ Q a) w]
        apply Finset.sum_congr ?_ (fun _ _ => rfl)
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hQ, Finset.mem_compl]
      rw [hsum, hsum'] at hdense
      have hflow := cut_faces_le_neighbor_flow Q w (fun a => (hw a).le)
      have hflow' : (∑ edge : CutEdge K Q, min (w edge.val.1) (w edge.val.2.1)) ≤
          ∑ a ∈ S, ∑ b ∈ Sᶜ, if Neighbor a b then min (w a) (w b) else 0 := by
        convert hflow using 1
        all_goals try with_reducible_and_instances rfl
        apply Finset.sum_congr ?_ ?_
        · ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hQ]
        · intro a _
          apply Finset.sum_congr ?_ (fun _ _ => rfl)
          ext b
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hQ, Finset.mem_compl]
      have hbound := hdense.trans hflow'
      calc
        _ = binProposal d * ((1 / (128 * (d : ℝ) * K)) *
            min (∑ a ∈ S, w a) (∑ a ∈ Sᶜ, w a)) := by unfold denseCutConstant; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hbound hβ.le
    · have he : Sᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsc
      rw [he]
      simp only [Finset.sum_empty, min_eq_right hSw, mul_zero, Finset.sum_const_zero]
      exact le_rfl
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [he] at hScw ⊢
    simp only [Finset.sum_empty, min_eq_left hScw, mul_zero]
    exact le_rfl

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseGeometry
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Feasible region and interior point of the dense block

These statements use the actual integer margins and quotient widths. Every
feasible real completion lies in the declared scaled cube, and one scaled
completion has normalized slack at least `1/(2d)` in every cell.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def Feasible (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (u : I × J → ℝ) : Prop :=
  ∀ i j, 0 ≤ table (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (denseWidth R P d) u i j

omit [DecidableEq I] [DecidableEq J] in
theorem table_entry_upper (R : Option I → ℝ) (P : Option J → ℝ)
    (w : I → J → ℝ) (u : I × J → ℝ) (htotal : ∑ i, R i = ∑ j, P j)
    (hfeas : ∀ i j, 0 ≤ table R P w u i j) (i : Option I) (j : Option J) :
    table R P w u i j ≤ min (R i) (P j) := by
  apply le_min
  · have h := Finset.single_le_sum (fun k _ => hfeas i k) (Finset.mem_univ j)
    rwa [table_rows] at h
  · have h := Finset.single_le_sum (fun k _ => hfeas k j) (Finset.mem_univ i)
    rwa [table_columns _ _ _ _ htotal] at h

omit [DecidableEq I] [DecidableEq J] in
theorem feasible_in_cube (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (htotal : ∑ i, R i = ∑ j, P j) (u : I × J → ℝ) (hu : Feasible R P d u) :
    ∀ p, 0 ≤ u p ∧ u p ≤ 2 * (d : ℝ) ^ 8 := by
  intro p
  have hw := denseWidth_pos R P d hd hR hP p.1 p.2
  have hlo := hu (some p.1) (some p.2)
  have ht : (∑ i, (R i : ℝ)) = ∑ j, (P j : ℝ) := by exact_mod_cast htotal
  have hhi := table_entry_upper (fun i => (R i : ℝ)) (fun j => (P j : ℝ))
    (denseWidth R P d) u ht hu (some p.1) (some p.2)
  change denseWidth R P d p.1 p.2 * u p ≤ min (R (some p.1) : ℝ) (P (some p.2) : ℝ) at hhi
  change 0 ≤ denseWidth R P d p.1 p.2 * u p at hlo
  have hwidth := (dense_width_bounds d (min (R (some p.1)) (P (some p.2))) hd
    (le_min (hR _) (hP _))).1
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hs : min (R (some p.1) : ℝ) (P (some p.2) : ℝ) ≤
      denseWidth R P d p.1 p.2 * (2 * (d : ℝ) ^ 8) := by
    apply (div_le_iff₀ (show (0 : ℝ) < 2 * (d : ℝ) ^ 8 by positivity)).mp
    simpa only [Nat.cast_min, denseWidth] using hwidth
  exact ⟨nonneg_of_mul_nonneg_right hlo hw, le_of_mul_le_mul_left (hhi.trans hs) hw⟩

omit [DecidableEq I] [DecidableEq J] in
/-- Real residual completion constructs the strict interior point. -/
theorem dense_interior_exists (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (htotal : ∑ i, R i = ∑ j, P j) :
    ∃ u : I × J → ℝ, Feasible R P d u ∧
      (∀ p, 0 ≤ u p ∧ u p ≤ 2 * (d : ℝ) ^ 8) ∧
      ∀ g : Option I × Option J,
        1 / (2 * (d : ℝ)) ≤
          table (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (denseWidth R P d) u g.1 g.2 /
            cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hscale (g : Option I × Option J) :
      0 < cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g := by
    change 0 < min (R g.1 : ℝ) (P g.2 : ℝ)
    apply lt_min
    · exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < d by omega) _) (hR _))
    · exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < d by omega) _) (hP _))
  obtain ⟨X, hX, hXR, hXP⟩ := strict_real_completion
    (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (d : ℝ) hd₀
    (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)
    (by exact_mod_cast hdimR) (by exact_mod_cast hdimP) (by exact_mod_cast htotal)
  let u : I × J → ℝ := fun p => X (some p.1) (some p.2) / denseWidth R P d p.1 p.2
  have heq : table (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (denseWidth R P d) u = X :=
    table_recover _ _ _ (fun i j => ne_of_gt (denseWidth_pos R P d hd hR hP i j)) X hXR hXP
  have hfeas : Feasible R P d u := by
    intro i j
    rw [heq]
    exact (div_nonneg (hscale (i, j)).le (by positivity)).trans (hX i j)
  refine ⟨u, hfeas, feasible_in_cube R P d hd hR hP htotal u hfeas, ?_⟩
  intro g
  rw [heq]
  apply (le_div_iff₀ (hscale g)).mpr
  simpa only [cellScale, div_mul_eq_mul_div, one_mul] using hX g.1 g.2

theorem densePenalty_eq_zero_of_feasible (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (u : I × J → ℝ) (hu : Feasible R P d u) : densePenalty R P d u = 0 := by
  apply le_antisymm
  · unfold densePenalty AffinePenalty.penalty
    apply Finset.sup'_le
    intro g _
    cases g with
    | none => exact le_rfl
    | some g =>
      change -AffinePenalty.affineValue _ _ u - (d : ℝ) / (d : ℝ) ^ 8 ≤ 0
      rw [← normalized_table_affine]
      have hnorm : 0 ≤ table (fun i => (R i : ℝ)) (fun j => (P j : ℝ))
          (denseWidth R P d) u g.1 g.2 /
            cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g :=
        div_nonneg (hu g.1 g.2) (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      linarith [show (0 : ℝ) ≤ (d : ℝ) / (d : ℝ) ^ 8 by positivity]
  · exact AffinePenalty.penalty_nonnegative _ _ _ _

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseInteriorVolume
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive volume of the actual dense completion polytope -/

namespace ContingencyTables.DenseAffine

open MeasureTheory
open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def normalizedEntry (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (u : I × J → ℝ) (g : Option I × Option J) : ℝ :=
  table (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (denseWidth R P d) u g.1 g.2 /
    cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g

theorem normalizedEntry_change (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (x y : I × J → ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hxy : ∀ p, |x p - y p| ≤ r) (g : Option I × Option J) :
    |normalizedEntry R P d x g - normalizedEntry R P d y g| ≤
      ((d : ℝ) / (d : ℝ) ^ 8) * r := by
  unfold normalizedEntry
  rw [normalized_table_affine, normalized_table_affine]
  have hb := AffinePenalty.affineValue_change
    (entryOffset (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    (fun p => entryCoeff (denseWidth R P d) g p /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    x y (1 / (d : ℝ) ^ 8) r
    (by positivity) (dense_normalized_coeff_bound R P d hd hR hP hRmax hPmax g) hxy
  have hc : (Fintype.card (I × J) : ℝ) ≤ d := by exact_mod_cast hfree
  calc
    _ ≤ Fintype.card (I × J) * (1 / (d : ℝ) ^ 8) * r := hb
    _ ≤ (d : ℝ) * (1 / (d : ℝ) ^ 8) * r := by gcongr
    _ = _ := by ring

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseLocalGeometry
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Feasible bins and exponent bounds for dense rejection

These bounds use the actual quotient widths and margin-derived penalty.
In particular, every bin containing a feasible point has weight one.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem densePenalty_change (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (x y : I × J → ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hxy : ∀ p, |x p - y p| ≤ r) :
    |densePenalty R P d x - densePenalty R P d y| ≤ ((d : ℝ) / (d : ℝ) ^ 8) * r := by
  have hb := AffinePenalty.penalty_change
    (fun g => entryOffset (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    (fun g p => entryCoeff (denseWidth R P d) g p /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    ((d : ℝ) / (d : ℝ) ^ 8) x y (1 / (d : ℝ) ^ 8) r (by positivity) hr
    (dense_normalized_coeff_bound R P d hd hR hP hRmax hPmax) hxy
  have hc : (Fintype.card (I × J) : ℝ) ≤ d := by exact_mod_cast hfree
  calc
    _ ≤ Fintype.card (I × J) * (1 / (d : ℝ) ^ 8) * r := hb
    _ ≤ (d : ℝ) * (1 / (d : ℝ) ^ 8) * r := by gcongr
    _ = _ := by ring

theorem densePenalty_cube_bound (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (x : I × J → ℝ) (hx : ∀ p, 0 ≤ x p ∧ x p ≤ 4 * (d : ℝ) ^ 8) :
    0 ≤ densePenalty R P d x ∧ densePenalty R P d x ≤ 4 * d := by
  obtain ⟨u, hu, hcube, _⟩ := dense_interior_exists R P d hd hR hP hdimR hdimP htotal
  have hxy (p : I × J) : |x p - u p| ≤ 4 * (d : ℝ) ^ 8 := by
    apply abs_le.mpr
    constructor <;> linarith [(hx p).1, (hx p).2, (hcube p).1, (hcube p).2,
      show (0 : ℝ) ≤ (d : ℝ) ^ 8 by positivity]
  have hb := densePenalty_change R P d hd hR hP hRmax hPmax hfree x u
    (4 * (d : ℝ) ^ 8) (by positivity) hxy
  rw [densePenalty_eq_zero_of_feasible R P d u hu, sub_zero] at hb
  have hd₀ : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have heq : ((d : ℝ) / (d : ℝ) ^ 8) * (4 * (d : ℝ) ^ 8) = 4 * d := by
    field_simp
  exact ⟨AffinePenalty.penalty_nonnegative _ _ _ _, (le_abs_self _).trans (hb.trans_eq heq)⟩

theorem densePenalty_corner_zero (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (v x : I × J → ℝ)
    (hx : Feasible R P d x) (hvx : ∀ p, |v p - x p| ≤ 1) :
    densePenalty R P d v = 0 := by
  apply le_antisymm
  · unfold densePenalty AffinePenalty.penalty
    apply Finset.sup'_le
    intro g _
    cases g with
    | none => exact le_rfl
    | some g =>
      change -AffinePenalty.affineValue _ _ v - (d : ℝ) / (d : ℝ) ^ 8 ≤ 0
      rw [← normalized_table_affine]
      change -normalizedEntry R P d v g - (d : ℝ) / (d : ℝ) ^ 8 ≤ 0
      have hb := normalizedEntry_change R P d hd hR hP hRmax hPmax hfree v x 1
        (by norm_num) hvx g
      have hnonneg : 0 ≤ normalizedEntry R P d x g :=
        div_nonneg (hx g.1 g.2) (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      have hl := (abs_le.mp hb).1
      linarith
  · exact AffinePenalty.penalty_nonnegative _ _ _ _

end

end ContingencyTables.DenseAffine

namespace ContingencyTables.GridBoundary

open scoped BigOperators

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q K : ℕ}

theorem denseBinWeight_eq_one (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (a : Grid (I := Fin q) K) (x : Fin q → ℝ) (hx : ClosedBin (corner a) x)
    (hfeas : DenseAffine.Feasible R P d (fun p => x (e p))) :
    denseBinWeight R P d e a = 1 := by
  have hz := DenseAffine.densePenalty_corner_zero R P d hd hR hP hRmax hPmax hfree
    (fun p => realCorner a (e p)) (fun p => x (e p)) hfeas (fun p => by
      change |(corner a (e p) : ℝ) - x (e p)| ≤ 1
      apply abs_le.mpr
      constructor <;> linarith [(hx (e p)).1, (hx (e p)).2])
  simp only [denseBinWeight, denseGridPenalty, DenseWeights.binWeight, hz, mul_zero,
    Int.floor_zero, Int.cast_zero, neg_zero, Real.rpow_zero]

theorem denseBinWeight_le_one (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) :
    denseBinWeight R P d e a ≤ 1 := by
  have hp : 0 ≤ denseGridPenalty R P d e (realCorner a) :=
    AffinePenalty.penalty_nonnegative _ _ _ _
  have hfloor : (0 : ℤ) ≤ ⌊(d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a)⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg (by positivity) hp)
  unfold denseBinWeight DenseWeights.binWeight
  calc
    _ ≤ (2 : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have hf : (0 : ℝ) ≤ (⌊(d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a)⌋ : ℤ) :=
        by exact_mod_cast hfloor
      linarith)
    _ = 1 := Real.rpow_zero _

theorem denseBinWeight_lower (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    (2 : ℝ) ^ (-(4 * (d : ℝ) ^ 5)) ≤ denseBinWeight R P d e a := by
  have hcube (p : I × J) : 0 ≤ realCorner a (e p) ∧ realCorner a (e p) ≤ 4 * (d : ℝ) ^ 8 := by
    have hlo : (0 : ℤ) ≤ corner a (e p) := (a (e p)).property.1
    have hhi : corner a (e p) ≤ (4 * d ^ 8 : ℕ) - 1 := (a (e p)).property.2
    constructor
    · change (0 : ℝ) ≤ (corner a (e p) : ℝ)
      exact_mod_cast hlo
    · have hupper : corner a (e p) ≤ (4 * d ^ 8 : ℕ) := by
        omega
      change (corner a (e p) : ℝ) ≤ 4 * (d : ℝ) ^ 8
      exact_mod_cast hupper
  have hp := (DenseAffine.densePenalty_cube_bound R P d hd hR hP hRmax hPmax
    hdimR hdimP hfree htotal _ hcube).2
  have hf := Int.floor_le ((d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a))
  have hm := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ (d : ℝ) ^ 4 by positivity)
  change (d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a) ≤ (d : ℝ) ^ 4 * (4 * d) at hm
  unfold denseBinWeight DenseWeights.binWeight
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  change denseGridPenalty R P d e (realCorner a) ≤ 4 * d at hp
  nlinarith [show (d : ℝ) ^ 4 * (4 * d) = 4 * (d : ℝ) ^ 5 by ring]

theorem grid_card (q K : ℕ) : Fintype.card (Grid (I := Fin q) K) = K ^ q := by
  have hc : Fintype.card (Set.Icc (0 : ℤ) ((K : ℤ) - 1)) = K := by
    have h := Int.card_fintype_Icc_of_le 0 ((K : ℤ) - 1)
      (show (0 : ℤ) ≤ (K : ℤ) - 1 + 1 by omega)
    omega
  simp only [Grid, Fintype.card_fun, Fintype.card_fin, hc]

theorem denseBinChain_pi_lower (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    (2 : ℝ) ^ (-(4 * (d : ℝ) ^ 5)) / ((4 * (d : ℝ) ^ 8) ^ q) ≤
      (denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).π a := by
  let : Nonempty (Grid (I := Fin q) (4 * d ^ 8)) := ⟨a⟩
  let w := denseBinWeight R P d e (K := 4 * d ^ 8)
  have hw : ∀ z, 0 < w z := fun z => DenseWeights.binWeight_pos _ _ _
  have hz : 0 < ∑ z, w z := Finset.sum_pos (fun z _ => hw z) Finset.univ_nonempty
  have hsum : (∑ z, w z) ≤ (4 * (d : ℝ) ^ 8) ^ q := by
    calc
      _ ≤ ∑ _z : Grid (I := Fin q) (4 * d ^ 8), (1 : ℝ) :=
        Finset.sum_le_sum (fun z _ => denseBinWeight_le_one R P d e z)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        grid_card, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  change _ ≤ w a / (∑ z, w z)
  exact div_le_div₀ (hw a).le
    (denseBinWeight_lower R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e a) hz hsum

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMixing
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical Poincaré and point mixing for the dense bin sampler -/

namespace ContingencyTables.GridBoundary

open CommonBasesFPRAS
open scoped BigOperators

noncomputable section

theorem denseCutConstant_lower (d : ℕ) (hd : 14 ≤ d) :
    1 / (8192 * (d : ℝ) ^ 10) ≤ denseCutConstant d (4 * d ^ 8) := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  calc
    _ = (1 / (16 * (d : ℝ))) / (128 * (d : ℝ) * (4 * d ^ 8 : ℕ)) := by
      push_cast
      field_simp
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (binProposal_bounds d hd).2.1 (by positivity)

theorem densePoincareConstant_upper (d : ℕ) (hd : 14 ≤ d) :
    2 / (denseCutConstant d (4 * d ^ 8)) ^ 2 ≤ (d : ℝ) ^ 32 := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hk := denseCutConstant_lower d hd
  have hc : (134217728 : ℝ) ≤ (d : ℝ) ^ 12 := by
    exact_mod_cast (show 134217728 ≤ d ^ 12 from
      (by norm_num : 134217728 ≤ 14 ^ 12).trans (Nat.pow_le_pow_left hd 12))
  calc
    _ ≤ 2 / (1 / (8192 * (d : ℝ) ^ 10)) ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact pow_le_pow_left₀ (by positivity) hk 2
    _ = 134217728 * (d : ℝ) ^ 20 := by field_simp; ring
    _ ≤ (d : ℝ) ^ 12 * (d : ℝ) ^ 20 := by gcongr
    _ = _ := by ring

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

theorem denseBinChain_polynomial_poincare (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8))) :
    let hK : 1 ≤ 4 * d ^ 8 := denseGridSize_pos d hd
    ∀ f : Grid (I := Fin q) (4 * d ^ 8) → ℝ,
      (denseBinChain R P d hd hfree e hK).variance f ≤
        (d : ℝ) ^ 32 * (denseBinChain R P d hd hfree e hK).energy f := by
  dsimp only
  intro f
  exact (denseBinChain_poincare R P d hd hR hP hRmax hPmax hfree e _ hPL hCheeger f).trans
    (mul_le_mul_of_nonneg_right (densePoincareConstant_upper d hd) (FiniteChain.energy_nonneg _ f))

theorem denseBinChain_point_mixing (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8)))
    (n : ℕ) (a b : Grid (I := Fin q) (4 * d ^ 8)) :
    let hK : 1 ≤ 4 * d ^ 8 := denseGridSize_pos d hd
    let C := denseBinChain R P d hd hfree e hK
    |C.iterate n (C.pointDensity b) a - 1| ≤
      Real.exp (-(n : ℝ) / (d : ℝ) ^ 32) /
        ((2 : ℝ) ^ (-(4 * (d : ℝ) ^ 5)) / (4 * (d : ℝ) ^ 8) ^ q) := by
  dsimp only
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  apply FiniteChain.point_mixing_exp
  · exact one_le_pow₀ hd₁
  · positivity
  · exact denseBinChain_pi_lower R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e
  · exact denseBinChain_polynomial_poincare R P d hd hR hP hRmax hPmax hfree e hPL hCheeger

theorem denseBinChain_relative_mixing (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8)))
    (h : ℕ) (a b : Grid (I := Fin q) (4 * d ^ 8)) :
    let C := denseBinChain R P d hd hfree e (denseGridSize_pos d hd)
    |C.iterate (d ^ 50 * (h + 1) ^ 2) (C.pointDensity b) a - 1| ≤
      (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
  have hq : q ≤ d := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin] at hc
    omega
  exact (denseBinChain_point_mixing R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal
    e hPL hCheeger _ a b).trans (dense_mixing_time_arithmetic d q h hd hq)

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseRegionVolume
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inner-polytope and penalty-sublevel volume for the actual margins -/

namespace ContingencyTables.DenseAffine

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def normalizedRegion (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (γ : ℝ) : Set (I × J → ℝ) := {x | ∀ g, γ ≤ normalizedEntry R P d x g}

theorem normalizedRegion_eq_affine (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (γ : ℝ) :
    normalizedRegion R P d γ =
      AffinePenalty.region (normalizedOffset R P) (normalizedCoeff R P d) γ := by
  ext x
  simp only [normalizedRegion, AffinePenalty.region, Set.mem_ofPred_eq,
    normalizedEntry, normalized_table_affine, normalizedOffset]
  rfl

theorem normalizedEntry_continuous (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (g : Option I × Option J) : Continuous (fun x => normalizedEntry R P d x g) := by
  have heq : (fun x => normalizedEntry R P d x g) =
      (fun x => AffinePenalty.affineValue (normalizedOffset R P g) (normalizedCoeff R P d g) x) := by
    funext x
    exact normalized_table_affine _ _ _ _ _
  rw [heq]
  exact continuous_const.add (continuous_finsetSum Finset.univ
    (fun p _ => continuous_const.mul (continuous_apply p)))

theorem normalizedRegion_closed (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (γ : ℝ) : IsClosed (normalizedRegion R P d γ) := by
  have heq : normalizedRegion R P d γ =
      ⋂ g, {x | γ ≤ normalizedEntry R P d x g} := by
    ext x
    simp only [normalizedRegion, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter (fun g => isClosed_le continuous_const (normalizedEntry_continuous R P d g))

omit [DecidableEq I] [DecidableEq J] in
theorem normalizedRegion_zero (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j) :
    normalizedRegion R P d 0 = {x | Feasible R P d x} := by
  have hs (g : Option I × Option J) :
      0 < cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g := by
    change 0 < min (R g.1 : ℝ) (P g.2 : ℝ)
    apply lt_min
    · exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < d by omega) _) (hR _))
    · exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < d by omega) _) (hP _))
  ext x
  constructor
  · intro hx i j
    have h := hx (i, j)
    change 0 ≤ _ / cellScale _ _ (i, j) at h
    simpa only [zero_mul] using (le_div_iff₀ (hs (i, j))).mp h
  · intro hx g
    exact div_nonneg (hx g.1 g.2) (hs g).le

theorem dense_feasible_compact (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (htotal : ∑ i, R i = ∑ j, P j) :
    IsCompact {x : I × J → ℝ | Feasible R P d x} := by
  have hclosed : IsClosed {x : I × J → ℝ | Feasible R P d x} := by
    rw [← normalizedRegion_zero R P d hd hR hP]
    exact normalizedRegion_closed R P d 0
  apply isCompact_Icc.of_isClosed_subset hclosed
  intro x hx
  have h := feasible_in_cube R P d hd hR hP htotal x hx
  exact ⟨fun p => (h p).1, fun p => (h p).2⟩

theorem dense_inner_volume (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j) :
    (1 / 2 : ℝ≥0∞) * volume {x : I × J → ℝ | Feasible R P d x} ≤
      volume (normalizedRegion R P d (2 * (d : ℝ) / (d : ℝ) ^ 8)) := by
  obtain ⟨u, _, _, hu⟩ := dense_interior_exists R P d hd hR hP hdimR hdimP htotal
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hα := dense_inner_contraction d hd (Fintype.card (I × J)) hfree
  have hc : u ∈ AffinePenalty.region (normalizedOffset R P) (normalizedCoeff R P d)
      (1 / (2 * (d : ℝ))) := by
    rw [← normalizedRegion_eq_affine]
    exact hu
  have hvol := AffinePenalty.inner_region_volume (normalizedOffset R P) (normalizedCoeff R P d)
    u (1 / (2 * (d : ℝ))) (4 * (d : ℝ) ^ 2 / (d : ℝ) ^ 8) hα.1 hα.2.1 hc
  have heq : (4 * (d : ℝ) ^ 2 / (d : ℝ) ^ 8) * (1 / (2 * (d : ℝ))) =
      2 * (d : ℝ) / (d : ℝ) ^ 8 := by field_simp; ring
  rw [heq, ← normalizedRegion_eq_affine, ← normalizedRegion_eq_affine,
    normalizedRegion_zero R P d hd hR hP] at hvol
  apply le_trans _ hvol
  apply mul_le_mul_left
  have hb := ENNReal.ofReal_le_ofReal hα.2.2
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using hb

theorem dense_relaxed_volume (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    volume (normalizedRegion R P d (-γ)) ≤
      ENNReal.ofReal (Real.exp (2 * (d : ℝ) ^ 2 * γ)) *
        volume {x : I × J → ℝ | Feasible R P d x} := by
  obtain ⟨u, _, _, hu⟩ := dense_interior_exists R P d hd hR hP hdimR hdimP htotal
  have hc : u ∈ AffinePenalty.region (normalizedOffset R P) (normalizedCoeff R P d)
      (1 / (2 * (d : ℝ))) := by
    rw [← normalizedRegion_eq_affine]
    exact hu
  have hvol := AffinePenalty.relaxed_region_volume_exp (normalizedOffset R P) (normalizedCoeff R P d)
    u (d : ℝ) γ (by exact_mod_cast (show 0 < d by omega)) hγ (by exact_mod_cast hfree) hc
  rw [← normalizedRegion_eq_affine, ← normalizedRegion_eq_affine,
    normalizedRegion_zero R P d hd hR hP] at hvol
  exact hvol

theorem dense_sublevel_volume (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (s : ℝ) (hs : 0 ≤ s) :
    volume {x : I × J → ℝ | densePenalty R P d x ≤ s} ≤
      ENNReal.ofReal (Real.exp (2 * (d : ℝ) ^ 2 * ((d : ℝ) / (d : ℝ) ^ 8 + s))) *
        volume {x : I × J → ℝ | Feasible R P d x} := by
  have hsub : {x : I × J → ℝ | densePenalty R P d x ≤ s} ⊆
      normalizedRegion R P d (-((d : ℝ) / (d : ℝ) ^ 8 + s)) := by
    intro x hx g
    change densePenalty R P d x ≤ s at hx
    have hb := AffinePenalty.component_le_penalty (normalizedOffset R P) (normalizedCoeff R P d)
      ((d : ℝ) / (d : ℝ) ^ 8) x (some g)
    change -AffinePenalty.affineValue _ _ x - (d : ℝ) / (d : ℝ) ^ 8 ≤ densePenalty R P d x at hb
    change -((d : ℝ) / (d : ℝ) ^ 8 + s) ≤ normalizedEntry R P d x g
    have heq : normalizedEntry R P d x g =
        AffinePenalty.affineValue (normalizedOffset R P g) (normalizedCoeff R P d g) x :=
      normalized_table_affine _ _ _ _ _
    rw [heq]
    linarith
  exact (measure_mono hsub).trans (dense_relaxed_volume R P d hd hR hP hdimR hdimP hfree
    htotal _ (add_nonneg (by positivity) hs))

end

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DensityLayers
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A finite penalty-layer bound

The actual dense cube has bounded exponent, so a finite layer sum suffices
for its normalizer. This avoids any infinite layer decomposition.
-/

namespace ContingencyTables.DenseWeights

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

theorem density_le_finite_layers {X : Type*} (A : ℝ) (p : X → ℝ) (N : ℕ)
    (x : X) (hx₀ : 0 ≤ A * p x) (hxN : A * p x ≤ N) :
    ENNReal.ofReal (density A p x) ≤
      ∑ j ∈ Finset.range (N + 1),
        (layerSet A p j).indicator (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ)))) x := by
  let j := (⌊A * p x⌋ : ℤ).toNat
  have hf : (0 : ℤ) ≤ ⌊A * p x⌋ := Int.floor_nonneg.mpr hx₀
  have hjcast : (j : ℝ) = (⌊A * p x⌋ : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg hf
  have hj : j ∈ Finset.range (N + 1) := by
    apply Finset.mem_range.mpr
    have hb : (j : ℝ) ≤ N := by
      rw [hjcast]
      exact (Int.floor_le _).trans hxN
    have hn : j ≤ N := by exact_mod_cast hb
    omega
  have hxj : x ∈ layerSet A p j := by
    change A * p x ≤ (j : ℝ) + 1
    rw [hjcast]
    exact (Int.lt_floor_add_one _).le
  have hweight : density A p x ≤ (2 : ℝ) ^ (-(j : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [hjcast]
    linarith [Int.floor_le (A * p x)]
  calc
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ))) := ENNReal.ofReal_le_ofReal hweight
    _ = (layerSet A p j).indicator (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ)))) x := by
      rw [Set.indicator_of_mem hxj]
    _ ≤ _ := Finset.single_le_sum
      (f := fun k : ℕ => (layerSet A p k).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ)))) x) (fun _ _ => bot_le) hj

theorem density_lintegral_le_layers {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : ℝ) (p : X → ℝ) (hp : Measurable p)
    (K : Set X) (hK : MeasurableSet K) (N : ℕ)
    (hbound : ∀ x ∈ K, 0 ≤ A * p x ∧ A * p x ≤ N) :
    (∫⁻ x in K, ENNReal.ofReal (density A p x) ∂μ) ≤
      ∑ j ∈ Finset.range (N + 1),
        ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ))) * μ (K ∩ layerSet A p j) := by
  have hmeas (j : ℕ) : MeasurableSet (layerSet A p j) :=
    measurableSet_le (measurable_const.mul hp) measurable_const
  calc
    _ ≤ ∫⁻ x in K, ∑ j ∈ Finset.range (N + 1),
        (layerSet A p j).indicator (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ)))) x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK] with x hx
      exact density_le_finite_layers A p N x (hbound x hx).1 (hbound x hx).2
    _ = _ := by
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [lintegral_indicator (hmeas j), lintegral_const, Measure.restrict_restrict (hmeas j),
          Measure.restrict_apply_univ, Set.inter_comm]
      · intro j _
        exact (measurable_const : Measurable (fun _ : X =>
          ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ))))).indicator (hmeas j)

end

end ContingencyTables.DenseWeights

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseReindexedVolume
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Volume-preserving free-coordinate indexing for the dense sampler -/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseGridFeasible (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (x : Fin q → ℝ) : Prop :=
  DenseAffine.Feasible R P d (fun p => x (e p))

omit [DecidableEq I] [DecidableEq J] in
theorem denseGridFeasible_volume (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (e : I × J ≃ Fin q) :
    volume {x | denseGridFeasible R P d e x} =
      volume {x : I × J → ℝ | DenseAffine.Feasible R P d x} := by
  exact volume_dense_reindex e {x | DenseAffine.Feasible R P d x}

theorem denseGrid_layer_volume (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (j : ℕ) :
    volume (DenseWeights.layerSet ((d : ℝ) ^ 4) (denseGridPenalty R P d e) j) ≤
      ENNReal.ofReal (Real.exp (2 * (d : ℝ) ^ 2 *
        ((d : ℝ) / (d : ℝ) ^ 8 + ((j : ℝ) + 1) / (d : ℝ) ^ 4))) *
      volume {x | denseGridFeasible R P d e x} := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hset : DenseWeights.layerSet ((d : ℝ) ^ 4) (denseGridPenalty R P d e) j =
      {x | denseGridPenalty R P d e x ≤ ((j : ℝ) + 1) / (d : ℝ) ^ 4} := by
    ext x
    change (d : ℝ) ^ 4 * denseGridPenalty R P d e x ≤ (j : ℝ) + 1 ↔
      denseGridPenalty R P d e x ≤ ((j : ℝ) + 1) / (d : ℝ) ^ 4
    rw [le_div_iff₀ (pow_pos hd₀ 4), mul_comm]
  rw [hset, denseGridFeasible_volume]
  have hv := volume_dense_reindex e {x | DenseAffine.densePenalty R P d x ≤
    ((j : ℝ) + 1) / (d : ℝ) ^ 4}
  change volume {x | denseGridPenalty R P d e x ≤ ((j : ℝ) + 1) / (d : ℝ) ^ 4} = _ at hv
  rw [hv]
  exact DenseAffine.dense_sublevel_volume R P d hd hR hP hdimR hdimP hfree htotal _ (by positivity)

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseNormalizer
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalizer bound for the actual dense bin weights -/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

/-- The finite layer estimate gives the stronger constant 16 in place of
the manuscript's 32. No interpolation or Cheeger input is needed here. -/
theorem denseBin_normalizer_bound (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) :
    ENNReal.ofReal (∑ a : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e a) ≤
      16 * volume {x | denseGridFeasible R P d e x} := by
  let K := 4 * d ^ 8
  let A := (d : ℝ) ^ 4
  let p := denseGridPenalty R P d e
  let ρ := DenseWeights.density A p
  let V := volume {x | denseGridFeasible R P d e x}
  let N := 4 * d ^ 5
  let t (j : ℕ) := (2 : ℝ) ^ (-(j : ℝ)) *
    Real.exp (2 * (d : ℝ) ^ 2 * ((d : ℝ) / (d : ℝ) ^ 8 + ((j : ℝ) + 1) / (d : ℝ) ^ 4))
  have hp : Continuous p := denseGridPenalty_continuous R P d e
  have hρ : Continuous ρ := DenseWeights.density_continuous A p hp
  have hi : IntegrableOn ρ (ambientBox q K) := hρ.integrableOn_Icc
  have hc : MeasurableSet {x : Fin q → ℝ | Cube K x} := (cube_finiteBox (q := q) (K := K)).isOpen.measurableSet
  have hsub : {x : Fin q → ℝ | Cube K x} ⊆ ambientBox q K :=
    fun x hx => ⟨fun j => (hx j).1.le, fun j => (hx j).2.le⟩
  have hbin (a : Grid (I := Fin q) K) : denseBinWeight R P d e a / 4 ≤ ∫ x in binSet a, ρ x := by
    have hb := setIntegral_ge_of_const_le_real (binSet_measurable a)
      (show volume (binSet a) ≠ ⊤ by rw [binSet_volume]; simp)
      (fun x hx => (denseGrid_bin_comparison R P d hd hR hP hRmax hPmax hfree e a x
        (fun j => ⟨(hx j).1.le, (hx j).2.le⟩)).1)
      (hi.mono_set (binSet_subset_ambient a))
    simpa only [Measure.real, binSet_volume, ENNReal.toReal_one, mul_one, denseBinWeight] using hb
  have hmass : (∑ a : Grid (I := Fin q) K, denseBinWeight R P d e a) ≤
      4 * ∫ x in {x | Cube K x}, ρ x := by
    have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hbin a)
    rw [← Finset.sum_div, ← cube_integral_bins ρ hi] at hs
    linarith
  have hZ : ENNReal.ofReal (∑ a : Grid (I := Fin q) K, denseBinWeight R P d e a) ≤
      4 * ∫⁻ x in {x | Cube K x}, ENNReal.ofReal (ρ x) := by
    have h := ENNReal.ofReal_le_ofReal hmass
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ofReal_integral_eq_lintegral_ofReal (hi.mono_set hsub)
        (Filter.Eventually.of_forall (fun x => (DenseWeights.density_pos A p x).le))] at h
    simpa only [ENNReal.ofReal_ofNat] using h
  have hbound (x : Fin q → ℝ) (hx : Cube K x) : 0 ≤ A * p x ∧ A * p x ≤ N := by
    have hcube (z : I × J) : 0 ≤ x (e z) ∧ x (e z) ≤ 4 * (d : ℝ) ^ 8 := by
      refine ⟨(hx (e z)).1.le, ?_⟩
      simpa only [K, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using (hx (e z)).2.le
    have hpen := DenseAffine.densePenalty_cube_bound R P d hd hR hP hRmax hPmax
      hdimR hdimP hfree htotal _ hcube
    have hm := mul_le_mul_of_nonneg_left hpen.2 (show (0 : ℝ) ≤ A by positivity)
    constructor
    · exact mul_nonneg (by positivity) hpen.1
    · change (d : ℝ) ^ 4 * p x ≤ (4 * d ^ 5 : ℕ)
      change (d : ℝ) ^ 4 * p x ≤ (d : ℝ) ^ 4 * (4 * d) at hm
      push_cast
      nlinarith [show (d : ℝ) ^ 4 * (4 * d) = 4 * (d : ℝ) ^ 5 by ring]
  have hL := DenseWeights.density_lintegral_le_layers volume A p hp.measurable
    {x | Cube K x} hc N hbound
  have hL' : (∫⁻ x in {x | Cube K x}, ENNReal.ofReal (ρ x)) ≤
      ENNReal.ofReal (∑ j ∈ Finset.range (N + 1), t j) * V := by
    apply hL.trans
    calc
      _ ≤ ∑ j ∈ Finset.range (N + 1),
          ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ))) *
            (ENNReal.ofReal (Real.exp (2 * (d : ℝ) ^ 2 *
              ((d : ℝ) / (d : ℝ) ^ 8 + ((j : ℝ) + 1) / (d : ℝ) ^ 4))) * V) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_right
        exact (measure_mono Set.inter_subset_right).trans
          (denseGrid_layer_volume R P d hd hR hP hdimR hdimP hfree htotal e j)
      _ = (∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (t j)) * V := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-(j : ℝ)))]
      _ = _ := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => show 0 ≤ t j by positivity)]
  calc
    _ ≤ 4 * ∫⁻ x in {x | Cube K x}, ENNReal.ofReal (ρ x) := hZ
    _ ≤ 4 * (ENNReal.ofReal (∑ j ∈ Finset.range (N + 1), t j) * V) := mul_le_mul_right hL' 4
    _ = ENNReal.ofReal (4 * (∑ j ∈ Finset.range (N + 1), t j)) * V := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat, mul_assoc]
    _ ≤ 16 * V := by
      apply mul_le_mul_left
      have h := ENNReal.ofReal_le_ofReal (DenseAffine.dense_layer_sum d hd (N + 1))
      simpa only [ENNReal.ofReal_ofNat] using h

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseGoodBins
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Wholly feasible bins covering the inner polytope -/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators ENNReal Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q K : ℕ}

def closedBinSet (a : Grid (I := Fin q) K) : Set (Fin q → ℝ) :=
  Set.Icc (realCorner a) (fun j => realCorner a j + 1)

theorem mem_closedBinSet (a : Grid (I := Fin q) K) (x : Fin q → ℝ) :
    x ∈ closedBinSet a ↔ ClosedBin (corner a) x := by
  constructor
  · intro hx j
    exact ⟨hx.1 j, hx.2 j⟩
  · intro hx
    exact ⟨fun j => (hx j).1, fun j => (hx j).2⟩

theorem closedBinSet_volume (a : Grid (I := Fin q) K) : volume (closedBinSet a) = 1 := by
  rw [closedBinSet, Real.volume_Icc_pi]
  simp only [add_sub_cancel_left, ENNReal.ofReal_one, Finset.prod_const_one]

def goodBin (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) : Prop :=
  ∀ x, ClosedBin (corner a) x → denseGridFeasible R P d e x

def goodBins (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) : Finset (Grid (I := Fin q) K) :=
  Finset.univ.filter (goodBin R P d e)

def denseGridInner (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) : Set (Fin q → ℝ) :=
  {x | (fun p => x (e p)) ∈ DenseAffine.normalizedRegion R P d (2 * (d : ℝ) / (d : ℝ) ^ 8)}

theorem inner_bin_good (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (a : Grid (I := Fin q) K) (x : Fin q → ℝ)
    (hx : x ∈ denseGridInner R P d e) (hbin : ClosedBin (corner a) x) :
    goodBin R P d e a := by
  intro y hy
  have hdist (p : I × J) : |y (e p) - x (e p)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [(hy (e p)).1, (hy (e p)).2, (hbin (e p)).1, (hbin (e p)).2]
  have hzero : (fun p => y (e p)) ∈ DenseAffine.normalizedRegion R P d 0 := by
    intro g
    have hb := DenseAffine.normalizedEntry_change R P d hd hR hP hRmax hPmax hfree
      (fun p => y (e p)) (fun p => x (e p)) 1 (by norm_num) hdist g
    have hs := hx g
    have heq : 2 * (d : ℝ) / (d : ℝ) ^ 8 = 2 * ((d : ℝ) / (d : ℝ) ^ 8) := by ring
    rw [heq] at hs
    have hl := (abs_le.mp hb).1
    have hnonneg : (0 : ℝ) ≤ (d : ℝ) / (d : ℝ) ^ 8 := by positivity
    linarith
  rw [DenseAffine.normalizedRegion_zero R P d hd hR hP] at hzero
  exact hzero

theorem goodBin_weight_one (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (a : Grid (I := Fin q) K) (ha : goodBin R P d e a) : denseBinWeight R P d e a = 1 := by
  have hx : ClosedBin (corner a) (realCorner a) := fun _ => ⟨le_rfl, by dsimp [realCorner]; linarith⟩
  exact denseBinWeight_eq_one R P d hd hR hP hRmax hPmax hfree e a (realCorner a) hx (ha _ hx)

theorem dense_inner_covered_by_good_bins (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) :
    denseGridInner R P d e ⊆
      ⋃ a ∈ goodBins R P d e (K := 4 * d ^ 8), closedBinSet a := by
  intro x hx
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hxzero : (fun p => x (e p)) ∈ DenseAffine.normalizedRegion R P d 0 :=
    fun g => (show (0 : ℝ) ≤ 2 * (d : ℝ) / (d : ℝ) ^ 8 by positivity).trans (hx g)
  rw [DenseAffine.normalizedRegion_zero R P d hd hR hP] at hxzero
  have hcube := DenseAffine.feasible_in_cube R P d hd hR hP htotal _ hxzero
  have hcoords (j : Fin q) : 0 ≤ x j ∧ x j < (4 * d ^ 8 : ℕ) := by
    have hj := hcube (e.symm j)
    simp only [Equiv.apply_symm_apply] at hj
    constructor
    · exact hj.1
    · push_cast
      have hb : (0 : ℝ) < (d : ℝ) ^ 8 := pow_pos hd₀ _
      linarith [hj.2]
  have hfloor (j : Fin q) : ⌊x j⌋ ∈ Set.Icc (0 : ℤ) ((4 * d ^ 8 : ℕ) - 1) := by
    refine ⟨Int.floor_nonneg.mpr (hcoords j).1, ?_⟩
    have hlt : ⌊x j⌋ < (4 * d ^ 8 : ℕ) := Int.floor_lt.mpr (by exact_mod_cast (hcoords j).2)
    omega
  let a : Grid (I := Fin q) (4 * d ^ 8) := fun j => ⟨⌊x j⌋, hfloor j⟩
  have hclosed : ClosedBin (corner a) x := fun j => ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
  have hgood := inner_bin_good R P d hd hR hP hRmax hPmax hfree e a x hx hclosed
  refine Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨?_, (mem_closedBinSet a x).mpr hclosed⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood⟩

theorem goodBins_volume_lower (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) :
    (1 / 2 : ℝ≥0∞) * volume {x | denseGridFeasible R P d e x} ≤
      (goodBins R P d e (K := 4 * d ^ 8)).card := by
  have hinner : (1 / 2 : ℝ≥0∞) * volume {x | denseGridFeasible R P d e x} ≤
      volume (denseGridInner R P d e) := by
    rw [denseGridInner, volume_dense_reindex, denseGridFeasible_volume]
    exact DenseAffine.dense_inner_volume R P d hd hR hP hdimR hdimP hfree htotal
  calc
    _ ≤ volume (denseGridInner R P d e) := hinner
    _ ≤ volume (⋃ a ∈ goodBins R P d e (K := 4 * d ^ 8), closedBinSet a) :=
      measure_mono (dense_inner_covered_by_good_bins R P d hd hR hP hRmax hPmax hfree htotal e)
    _ ≤ ∑ a ∈ goodBins R P d e (K := 4 * d ^ 8), volume (closedBinSet a) :=
      measure_biUnion_finset_le _ _
    _ = _ := by simp only [closedBinSet_volume, Finset.sum_const, nsmul_eq_mul, mul_one]

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAcceptance
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constant stationary mass of wholly feasible dense bins -/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators ENNReal Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

/-- Every within-bin offset in these bins is feasible. Their stationary
mass is at least 1/32, and hence at least the paper's claimed 1/64. -/
theorem dense_good_bin_probability (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) :
    (1 / 32 : ℝ) ≤
      (∑ a ∈ goodBins R P d e (K := 4 * d ^ 8), denseBinWeight R P d e a) /
        (∑ a : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e a) := by
  let V := volume {x | denseGridFeasible R P d e x}
  let G := goodBins R P d e (K := 4 * d ^ 8)
  let Z := ∑ a : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e a
  have hV : V ≠ ⊤ := by
    dsimp [V]
    rw [denseGridFeasible_volume]
    exact (DenseAffine.dense_feasible_compact R P d hd hR hP htotal).measure_ne_top
  have hG : V.toReal / 2 ≤ (G.card : ℝ) := by
    have h := ENNReal.toReal_mono (by simp)
      (goodBins_volume_lower R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat, ENNReal.toReal_natCast, one_div_mul_eq_div] using h
  have hZ : Z ≤ 16 * V.toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hV)
      (denseBin_normalizer_bound R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e)
    have hznonneg : 0 ≤ Z := Finset.sum_nonneg
      (fun a _ => (DenseWeights.binWeight_pos _ _ _).le)
    change (ENNReal.ofReal Z).toReal ≤ (16 * V).toReal at h
    simpa only [ENNReal.toReal_ofReal hznonneg, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using h
  have hK := denseGridSize_pos d hd
  let : Nonempty (Grid (I := Fin q) (4 * d ^ 8)) :=
    ⟨fun _ => ⟨0, by constructor <;> omega⟩⟩
  have hZpos : 0 < Z := Finset.sum_pos (fun a _ => DenseWeights.binWeight_pos _ _ _) Finset.univ_nonempty
  have hsum : (∑ a ∈ G, denseBinWeight R P d e a) = G.card := by
    calc
      _ = ∑ _a ∈ G, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact goodBin_weight_one R P d hd hR hP hRmax hPmax hfree e a (Finset.mem_filter.mp ha).2
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  change (1 / 32 : ℝ) ≤ (∑ a ∈ G, denseBinWeight R P d e a) / Z
  rw [hsum]
  apply (le_div_iff₀ hZpos).mpr
  linarith

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseIntegerTable
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integral dense completion formulas

The sampler fills dependent cells by integer sums and differences. The
acceptance test is exactly nonnegativity of these integers; accepted
outputs have the prescribed natural margins.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem scaled_integerTable_cast (R : Option I → ℕ) (P : Option J → ℕ)
    (w : I → J → ℕ) (hw : ∀ i j, 0 < w i j) (z : I × J → ℕ) :
    table (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (fun i j => (w i j : ℝ))
      (fun p => (z p : ℝ) / (w p.1 p.2 : ℝ)) =
        (fun i j => (integerTable R P z i j : ℝ)) := by
  have hfree (i : I) (j : J) : (w i j : ℝ) * ((z (i, j) : ℝ) / (w i j : ℝ)) = z (i, j) :=
    mul_div_cancel₀ _ (by exact_mod_cast ne_of_gt (hw i j))
  funext i j
  rw [integerTable_cast]
  cases i <;> cases j <;> simp only [table, hfree, one_mul]

theorem integerTable_recover (R : Option I → ℕ) (P : Option J → ℕ)
    (X : Option I → Option J → ℕ) (hR : ∀ i, ∑ j, X i j = R i)
    (hP : ∀ j, ∑ i, X i j = P j) :
    integerTable R P (fun p => X (some p.1) (some p.2)) = (fun i j => (X i j : ℤ)) := by
  have hr : ∀ i, ∑ j, (X i j : ℝ) = (R i : ℝ) := by
    intro i
    exact_mod_cast hR i
  have hc : ∀ j, ∑ i, (X i j : ℝ) = (P j : ℝ) := by
    intro j
    exact_mod_cast hP j
  have heq := table_recover (fun i => (R i : ℝ)) (fun j => (P j : ℝ))
    (fun _ _ => 1) (fun _ _ => by norm_num) (fun i j => (X i j : ℝ)) hr hc
  simp only [div_one] at heq
  funext i j
  apply Int.cast_injective (α := ℝ)
  rw [integerTable_cast]
  exact congrFun (congrFun heq i) j

theorem integer_acceptance_iff (R : Option I → ℕ) (P : Option J → ℕ)
    (w : I → J → ℕ) (hw : ∀ i j, 0 < w i j) (z : I × J → ℕ) :
    (∀ i j, 0 ≤ table (fun i => (R i : ℝ)) (fun j => (P j : ℝ))
      (fun i j => (w i j : ℝ)) (fun p => (z p : ℝ) / (w p.1 p.2 : ℝ)) i j) ↔
        ∀ i j, 0 ≤ integerTable R P z i j := by
  rw [scaled_integerTable_cast R P w hw z]
  constructor
  · intro h i j
    have hij := h i j
    change (0 : ℝ) ≤ (integerTable R P z i j : ℝ) at hij
    exact_mod_cast hij
  · intro h i j
    change (0 : ℝ) ≤ (integerTable R P z i j : ℝ)
    exact_mod_cast h i j

theorem naturalTable_free (R : Option I → ℕ) (P : Option J → ℕ) (z : I × J → ℕ) (i : I) (j : J) :
    naturalTable R P z (some i) (some j) = z (i, j) := by
  simp only [naturalTable, integerTable, Int.toNat_natCast]

theorem naturalTable_unique (R : Option I → ℕ) (P : Option J → ℕ) (z : I × J → ℕ)
    (hz : ∀ i j, 0 ≤ integerTable R P z i j)
    (X : Option I → Option J → ℕ) (hR : ∀ i, ∑ j, X i j = R i)
    (hP : ∀ j, ∑ i, X i j = P j) (hX : ∀ i j, X (some i) (some j) = z (i, j)) :
    naturalTable R P z = X := by
  have htotal : ∑ i, R i = ∑ j, P j := by
    simp_rw [← hR, ← hP]
    exact Finset.sum_comm
  have heq : (fun i j => (naturalTable R P z i j : ℝ)) = (fun i j => (X i j : ℝ)) := by
    apply table_unique
    · intro i
      have ha := naturalTable_rows R P z hz i
      exact_mod_cast ha.trans (hR i).symm
    · intro j
      have ha := naturalTable_columns R P z hz htotal j
      exact_mod_cast ha.trans (hP j).symm
    · intro i j
      rw [naturalTable_free, hX]
  funext i j
  exact Nat.cast_injective (congrFun (congrFun heq i) j)

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseOffsets
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique bin and offset encoding of free integer entries -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]
variable {q : ℕ}

def trialBoxEquiv (e : I × J ≃ Fin q) (w : I × J → ℕ) (K : ℕ) :
    Grid (I := Fin q) K × Offset w ≃ FreeBox w K where
  toFun t p := finProdFinEquiv (gridCoordinateFin K (t.1 (e p)), t.2 p)
  invFun z :=
    (fun j => (gridCoordinateFin K).symm
      (((finProdFinEquiv : Fin K × Fin (w (e.symm j)) ≃ Fin (K * w (e.symm j))).symm
        (z (e.symm j))).1),
     fun p => ((finProdFinEquiv : Fin K × Fin (w p) ≃ Fin (K * w p)).symm (z p)).2)
  left_inv t := by
    rcases t with ⟨a, o⟩
    apply Prod.ext
    · funext j
      simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    · funext p
      simp only [Equiv.symm_apply_apply]
  right_inv z := by
    funext p
    simp only [Equiv.apply_symm_apply]
    have hb : ((finProdFinEquiv : Fin K × Fin (w (e.symm (e p))) ≃
        Fin (K * w (e.symm (e p)))).symm (z (e.symm (e p)))).1 =
        ((finProdFinEquiv : Fin K × Fin (w p) ≃ Fin (K * w p)).symm (z p)).1 := by
      apply Fin.ext
      change (z (e.symm (e p))).val / w (e.symm (e p)) = (z p).val / w p
      rw [Equiv.symm_apply_apply]
    rw [hb]
    exact finProdFinEquiv.apply_symm_apply (z p)

omit [Fintype I] [Fintype J] in
theorem trialBoxEquiv_val (e : I × J ≃ Fin q) (w : I × J → ℕ) (K : ℕ)
    (a : Grid (I := Fin q) K) (o : Offset w) (p : I × J) :
    (trialBoxEquiv e w K (a, o) p).val = (o p).val + w p * (corner a (e p)).toNat := rfl

def tableFreeBox (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (X : Table R P) : FreeBox (integerWidth R P d) (4 * d ^ 8) := fun p =>
  ⟨X.val (some p.1) (some p.2), free_entry_lt_box R P d hd hR hP p _ (by
    apply le_min
    · exact entry_le_row X.property _ _
    · rw [← X.property.2 (some p.2)]
      exact Finset.single_le_sum (f := fun i : Option I => X.val i (some p.2))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some p.1)))⟩

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrial
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accepted dense trials are in bijection with the actual tables -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]
variable {q : ℕ}

abbrev DenseTrial (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) (q : ℕ) :=
  Grid (I := Fin q) (4 * d ^ 8) × Offset (integerWidth R P d)

def trialFree (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) (e : I × J ≃ Fin q)
    (t : DenseTrial R P d q) : I × J → ℕ :=
  fun p => (trialBoxEquiv e (integerWidth R P d) (4 * d ^ 8) t p).val

def TrialAccepted (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) (e : I × J ≃ Fin q)
    (t : DenseTrial R P d q) : Prop := ∀ i j, 0 ≤ DenseAffine.integerTable R P (trialFree R P d e t) i j

def trialTable (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) (e : I × J ≃ Fin q)
    (htotal : ∑ i, R i = ∑ j, P j) (t : DenseTrial R P d q) (ht : TrialAccepted R P d e t) :
    Table R P := ⟨DenseAffine.naturalTable R P (trialFree R P d e t),
      DenseAffine.naturalTable_rows R P _ ht, DenseAffine.naturalTable_columns R P _ ht htotal⟩

def tableTrial (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (X : Table R P) : DenseTrial R P d q :=
  (trialBoxEquiv e (integerWidth R P d) (4 * d ^ 8)).symm (tableFreeBox R P d hd hR hP X)

theorem trialFree_tableTrial (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (X : Table R P) (p : I × J) :
    trialFree R P d e (tableTrial R P d hd hR hP e X) p = X.val (some p.1) (some p.2) := by
  exact congrArg Fin.val (congrFun
    ((trialBoxEquiv e (integerWidth R P d) (4 * d ^ 8)).apply_symm_apply
      (tableFreeBox R P d hd hR hP X)) p)

theorem tableTrial_accepted (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (X : Table R P) :
    TrialAccepted R P d e (tableTrial R P d hd hR hP e X) := by
  have hf : trialFree R P d e (tableTrial R P d hd hR hP e X) =
      (fun p => X.val (some p.1) (some p.2)) := funext (trialFree_tableTrial R P d hd hR hP e X)
  intro i j
  rw [hf, DenseAffine.integerTable_recover R P X.val X.property.1 X.property.2]
  exact Int.natCast_nonneg _

theorem trialTable_tableTrial (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j) (X : Table R P) :
    trialTable R P d e htotal (tableTrial R P d hd hR hP e X)
      (tableTrial_accepted R P d hd hR hP e X) = X := by
  apply Subtype.ext
  exact DenseAffine.naturalTable_unique R P _ (tableTrial_accepted R P d hd hR hP e X)
    X.val X.property.1 X.property.2 (fun i j => (trialFree_tableTrial R P d hd hR hP e X (i, j)).symm)

theorem tableTrial_trialTable (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j)
    (t : DenseTrial R P d q) (ht : TrialAccepted R P d e t) :
    tableTrial R P d hd hR hP e (trialTable R P d e htotal t ht) = t := by
  apply (trialBoxEquiv e (integerWidth R P d) (4 * d ^ 8)).injective
  rw [tableTrial, Equiv.apply_symm_apply]
  funext p
  apply Fin.ext
  exact DenseAffine.naturalTable_free R P (trialFree R P d e t) p.1 p.2

def acceptedTrialEquiv (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j) :
    {t : DenseTrial R P d q // TrialAccepted R P d e t} ≃ Table R P where
  toFun t := trialTable R P d e htotal t.val t.property
  invFun X := ⟨tableTrial R P d hd hR hP e X, tableTrial_accepted R P d hd hR hP e X⟩
  left_inv t := Subtype.ext (tableTrial_trialTable R P d hd hR hP e htotal t.val t.property)
  right_inv X := trialTable_tableTrial R P d hd hR hP e htotal X

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialWeights
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equal weight of all accepted dense trials

The bin is sampled with its stationary weight, and the integral offset
uniformly. The unique trial producing any given table lies in a bin of
weight one. Conditioning this finite law on acceptance is therefore
exactly uniform on the actual tables.
-/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]
variable {q : ℕ}

def trialReal (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) : Fin q → ℝ :=
  fun j => (trialFree R P d e t (e.symm j) : ℝ) / (integerWidth R P d (e.symm j) : ℝ)

omit [Fintype I] [Fintype J] in
theorem trialReal_closed (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) :
    ClosedBin (corner t.1) (trialReal R P d e t) := by
  intro j
  have hw : (0 : ℝ) < integerWidth R P d (e.symm j) := by
    exact_mod_cast integerWidth_pos R P d hd hR hP (e.symm j)
  have ho : (0 : ℝ) ≤ (t.2 (e.symm j)).val := Nat.cast_nonneg _
  have ho' : ((t.2 (e.symm j)).val : ℝ) < integerWidth R P d (e.symm j) := by
    exact_mod_cast (t.2 (e.symm j)).isLt
  have hc : (((corner t.1 j).toNat : ℕ) : ℝ) = (corner t.1 j : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (t.1 j).property.1
  have hz : (trialFree R P d e t (e.symm j) : ℝ) =
      (t.2 (e.symm j)).val + (integerWidth R P d (e.symm j) : ℝ) * (corner t.1 j : ℝ) := by
    change ((trialBoxEquiv e (integerWidth R P d) (4 * d ^ 8) (t.1, t.2) (e.symm j)).val : ℝ) = _
    rw [trialBoxEquiv_val, Equiv.apply_symm_apply, Nat.cast_add, Nat.cast_mul, hc]
  change (corner t.1 j : ℝ) ≤ _ / _ ∧ _ / _ ≤ (corner t.1 j : ℝ) + 1
  constructor
  · apply (le_div_iff₀ hw).mpr
    rw [hz]
    nlinarith
  · apply (div_le_iff₀ hw).mpr
    rw [hz]
    nlinarith

theorem trialReal_feasible_iff (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) :
    denseGridFeasible R P d e (trialReal R P d e t) ↔ TrialAccepted R P d e t := by
  have h := DenseAffine.integer_acceptance_iff R P
    (fun i j => integerWidth R P d (i, j))
    (fun i j => integerWidth_pos R P d hd hR hP (i, j)) (trialFree R P d e t)
  change (∀ i j, 0 ≤ DenseAffine.table (fun i => (R i : ℝ)) (fun j => (P j : ℝ))
    (fun i j => (integerWidth R P d (i, j) : ℝ))
      (fun p => trialReal R P d e t (e p)) i j) ↔ _
  simpa only [trialReal, Equiv.symm_apply_apply, TrialAccepted] using h

variable [DecidableEq I] [DecidableEq J]

theorem acceptedTrial_binWeight_one (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (t : DenseTrial R P d q) (ht : TrialAccepted R P d e t) :
    denseBinWeight R P d e t.1 = 1 :=
  denseBinWeight_eq_one R P d hd hR hP hRmax hPmax hfree e t.1
    (trialReal R P d e t) (trialReal_closed R P d hd hR hP e t)
    ((trialReal_feasible_iff R P d hd hR hP e t).mpr ht)

def denseTrialMass (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) : ℝ :=
  denseBinWeight R P d e t.1 /
    (∑ a : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e a) /
      Fintype.card (Offset (integerWidth R P d))

theorem denseTrialMass_pos (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) :
    0 < denseTrialMass R P d e t := by
  let : Nonempty (Grid (I := Fin q) (4 * d ^ 8)) := ⟨t.1⟩
  let : Nonempty (Offset (integerWidth R P d)) :=
    ⟨fun p => ⟨0, integerWidth_pos R P d hd hR hP p⟩⟩
  have hZ : 0 < ∑ a : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e a :=
    Finset.sum_pos (fun _ _ => DenseWeights.binWeight_pos _ _ _) Finset.univ_nonempty
  have hO : (0 : ℝ) < Fintype.card (Offset (integerWidth R P d)) := by
    exact_mod_cast Fintype.card_pos (α := Offset (integerWidth R P d))
  exact div_pos (div_pos (DenseWeights.binWeight_pos _ _ _) hZ) hO

theorem denseTrialMass_sum (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) :
    ∑ t : DenseTrial R P d q, denseTrialMass R P d e t = 1 := by
  let : Nonempty (Grid (I := Fin q) (4 * d ^ 8)) :=
    ⟨fun _ => ⟨0, by have h := denseGridSize_pos d hd; constructor <;> omega⟩⟩
  let : Nonempty (Offset (integerWidth R P d)) :=
    ⟨fun p => ⟨0, integerWidth_pos R P d hd hR hP p⟩⟩
  have hZ : (∑ a : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e a) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun _ _ => DenseWeights.binWeight_pos _ _ _) Finset.univ_nonempty)
  have hO : (Fintype.card (Offset (integerWidth R P d)) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Fintype.card_pos (α := Offset (integerWidth R P d)))
  rw [Fintype.sum_prod_type]
  simp only [denseTrialMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp_rw [mul_div_cancel₀ _ hO]
  rw [← Finset.sum_div, div_self hZ]

/-- Conditioning the actual stationary-bin/uniform-offset trial law on
acceptance assigns each table exactly the reciprocal of the table count. -/
theorem denseTrial_conditional_uniform (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q) (X : Table R P) :
    denseTrialMass R P d e (tableTrial R P d hd hR hP e X) /
      (∑ Y : Table R P, denseTrialMass R P d e (tableTrial R P d hd hR hP e Y)) =
        1 / Fintype.card (Table R P) := by
  have heq (Y : Table R P) : denseTrialMass R P d e (tableTrial R P d hd hR hP e Y) =
      1 / (∑ a : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e a) /
        Fintype.card (Offset (integerWidth R P d)) := by
    unfold denseTrialMass
    rw [acceptedTrial_binWeight_one R P d hd hR hP hRmax hPmax hfree e _
      (tableTrial_accepted R P d hd hR hP e Y)]
  have ha := denseTrialMass_pos R P d hd hR hP e (tableTrial R P d hd hR hP e X)
  rw [heq X] at ha
  simp_rw [heq]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_comm (Fintype.card (Table R P) : ℝ)]
  simpa only [one_div] using div_mul_cancel_left₀ (ne_of_gt ha) (Fintype.card (Table R P) : ℝ)

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialAcceptance
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Acceptance probability of the actual ideal dense trial -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseAcceptanceMass (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) : ℝ :=
  ∑ t : DenseTrial R P d q, if TrialAccepted R P d e t then denseTrialMass R P d e t else 0

omit [DecidableEq I] [DecidableEq J] in
theorem goodBin_trialAccepted (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) (ht : goodBin R P d e t.1) :
    TrialAccepted R P d e t :=
  (trialReal_feasible_iff R P d hd hR hP e t).mp
    (ht (trialReal R P d e t) (trialReal_closed R P d hd hR hP e t))

theorem denseAcceptanceMass_le_one (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) : denseAcceptanceMass R P d e ≤ 1 := by
  rw [← denseTrialMass_sum R P d hd hR hP e]
  apply Finset.sum_le_sum
  intro t _
  split_ifs
  · exact le_rfl
  · exact (denseTrialMass_pos R P d hd hR hP e t).le

/-- Wholly feasible bins accept every integral offset, so their proved
stationary mass is a lower bound on the actual trial acceptance mass. -/
theorem denseAcceptanceMass_lower (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) : (1 / 32 : ℝ) ≤ denseAcceptanceMass R P d e := by
  let : Nonempty (Offset (integerWidth R P d)) :=
    ⟨fun p => ⟨0, integerWidth_pos R P d hd hR hP p⟩⟩
  have hO : (Fintype.card (Offset (integerWidth R P d)) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Fintype.card_pos (α := Offset (integerWidth R P d)))
  have hgood := dense_good_bin_probability R P d hd hR hP hRmax hPmax
    hdimR hdimP hfree htotal e
  have hle :
      (∑ t : DenseTrial R P d q,
        if goodBin R P d e t.1 then denseTrialMass R P d e t else 0) ≤
      denseAcceptanceMass R P d e := by
    apply Finset.sum_le_sum
    intro t _
    by_cases hg : goodBin R P d e t.1
    · rw [ite_eq_left hg, ite_eq_left (goodBin_trialAccepted R P d hd hR hP e t hg)]
    · rw [ite_eq_right hg]
      split_ifs
      · exact (denseTrialMass_pos R P d hd hR hP e t).le
      · exact le_rfl
  apply hgood.trans
  convert hle using 1
  all_goals try with_reducible_and_instances rfl
  rw [Fintype.sum_prod_type]
  change _ = ∑ a : Grid (I := Fin q) (4 * d ^ 8),
    ∑ _o : Offset (integerWidth R P d), if goodBin R P d e a then
      (denseBinWeight R P d e a /
        (∑ b : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e b)) /
          (Fintype.card (Offset (integerWidth R P d)) : ℝ) else 0
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_ite, mul_zero]
  simp_rw [mul_div_cancel₀ _ hO]
  rw [goodBins, Finset.sum_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseRational
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational evaluation of the dense bin exponent

Only integer completion, rational comparison and division are needed to
compute a bin's weight exponent. The real penalty used in the geometric
proof is exactly the cast of this finite rational maximum.
-/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]
variable {q K : ℕ}

def cornerFree (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) : I × J → ℕ :=
  fun p => integerWidth R P d p * (corner a (e p)).toNat

omit [Fintype I] [Fintype J] in
theorem cornerFree_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) (p : I × J) :
    (cornerFree R P d e a p : ℝ) =
      DenseAffine.denseWidth R P d p.1 p.2 * realCorner a (e p) := by
  have hc : (((corner a (e p)).toNat : ℕ) : ℝ) = (corner a (e p) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (a (e p)).property.1
  simp only [cornerFree, Nat.cast_mul, hc]
  rfl

theorem corner_integerTable_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) (i : Option I) (j : Option J) :
    (DenseAffine.integerTable R P (cornerFree R P d e a) i j : ℝ) =
      DenseAffine.table (fun i => (R i : ℝ)) (fun j => (P j : ℝ))
        (DenseAffine.denseWidth R P d) (fun p => realCorner a (e p)) i j := by
  rw [DenseAffine.integerTable_cast]
  cases i <;> cases j <;>
    simp only [DenseAffine.table, one_mul, cornerFree_cast]

def rationalComponent (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) :
    Option (Option I × Option J) → ℚ
  | none => 0
  | some g => -(DenseAffine.integerTable R P (cornerFree R P d e a) g.1 g.2 : ℚ) /
      ((min (R g.1) (P g.2) : ℕ) : ℚ) - (d : ℚ) / (d : ℚ) ^ 8

def rationalPenalty (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (rationalComponent R P d e a)

theorem rationalPenalty_nonnegative (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) : 0 ≤ rationalPenalty R P d e a :=
  Finset.le_sup' (rationalComponent R P d e a) (Finset.mem_univ none)

variable [DecidableEq I] [DecidableEq J]

theorem rationalComponent_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) (g : Option (Option I × Option J)) :
    (rationalComponent R P d e a g : ℝ) =
      AffinePenalty.component
        (fun g => DenseAffine.entryOffset (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g /
          DenseAffine.cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
        (fun g p => DenseAffine.entryCoeff (DenseAffine.denseWidth R P d) g p /
          DenseAffine.cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
        ((d : ℝ) / (d : ℝ) ^ 8) g (fun p => realCorner a (e p)) := by
  cases g with
  | none => simp only [rationalComponent, Rat.cast_zero, AffinePenalty.component]
  | some g =>
    simp only [rationalComponent, Rat.cast_sub, Rat.cast_div, Rat.cast_neg,
      Rat.cast_intCast, Rat.cast_natCast, Rat.cast_pow, AffinePenalty.component,
      Nat.cast_min, Rat.cast_min, neg_div]
    rw [corner_integerTable_cast]
    change -(_ / DenseAffine.cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g) - _ = _
    rw [DenseAffine.normalized_table_affine]

theorem rationalPenalty_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) :
    (rationalPenalty R P d e a : ℝ) = denseGridPenalty R P d e (realCorner a) := by
  unfold rationalPenalty denseGridPenalty DenseAffine.densePenalty AffinePenalty.penalty
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun x : ℚ => (x : ℝ))
    (fun x y => Rat.cast_max x y)]
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro g _
  exact rationalComponent_cast R P d e a g

def denseExponent (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) : ℕ :=
  ⌊(d : ℚ) ^ 4 * rationalPenalty R P d e a⌋₊

theorem denseExponent_eq_floor (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) :
    (denseExponent R P d e a : ℤ) =
      ⌊(d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a)⌋ := by
  have hp := rationalPenalty_nonnegative R P d e a
  rw [denseExponent, Int.natCast_floor_eq_floor (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hp)]
  have hcast : (((d : ℚ) ^ 4 * rationalPenalty R P d e a : ℚ) : ℝ) =
      (d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a) := by
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, rationalPenalty_cast]
  rw [← hcast, Rat.floor_cast]

theorem denseBinWeight_eq_dyadic (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) :
    denseBinWeight R P d e a = 1 / (2 : ℝ) ^ denseExponent R P d e a := by
  unfold denseBinWeight DenseWeights.binWeight
  rw [← denseExponent_eq_floor]
  simp only [Int.cast_natCast, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_natCast, one_div]

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_DyadicAcceptance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-bit Metropolis acceptance

A uniform integer encoded by the allotted fair bits is compared with a
power of two. Extra bits are padding; their number does not change the
acceptance probability.
-/

namespace ContingencyTables.GridBoundary

open scoped Classical

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q K : ℕ}

theorem dense_acceptance_dyadic (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a b : Grid (I := Fin q) K) :
    min (1 : ℝ) (denseBinWeight R P d e b / denseBinWeight R P d e a) =
      1 / (2 : ℝ) ^ (denseExponent R P d e b - denseExponent R P d e a) := by
  simp only [denseBinWeight_eq_dyadic]
  exact FairBits.dyadic_ratio_min _ _

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteMetropolis
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite proposal-and-acceptance experiments -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [Nonempty β] [Nonempty γ]

def finiteAcceptLaw (a : α) (proposal : β → Option α) (accept : α → γ → Prop) : RationalLaw α :=
  mapLaw (productLaw (uniformLaw (α := β)) (uniformLaw (α := γ)))
    (finiteAcceptStep a proposal accept)

/-- The off-diagonal mass is the exact product of the proposal-code and
acceptance-coin frequencies. Both experiments use bounded finite samples. -/
theorem finiteAcceptLaw_off_diagonal (a b : α) (proposal : β → Option α)
    (accept : α → γ → Prop) (hab : a ≠ b) :
    (finiteAcceptLaw a proposal accept).mass b =
      ((Finset.univ.filter (fun z => proposal z = some b)).card / (Fintype.card β : ℚ)) *
      ((Finset.univ.filter (accept b)).card / (Fintype.card γ : ℚ)) := by
  change (∑ z : β × γ, if finiteAcceptStep a proposal accept z = b then
    uniformMass (α := β) * uniformMass (α := γ) else 0) = _
  simp_rw [finiteAcceptStep_eq_iff a b proposal accept _ hab]
  rw [Fintype.sum_prod_type]
  have hs : (∑ x : β, ∑ y : γ, if proposal x = some b ∧ accept b y then
      uniformMass (α := β) * uniformMass (α := γ) else 0) =
      (∑ x : β, if proposal x = some b then uniformMass (α := β) else 0) *
      (∑ y : γ, if accept b y then uniformMass (α := γ) else 0) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hx : proposal x = some b <;> by_cases hy : accept b y <;> simp [hx, hy]
  rw [hs, ← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, uniformMass]
  ring

omit [Fintype β] [Fintype γ] [Nonempty β] [Nonempty γ] in
/-- Two finite probability laws agreeing off a fixed state agree there
as well. This recovers the rejection/stay probability from normalization. -/
theorem RationalLaw.eq_of_off_diagonal (p q : RationalLaw α) (a : α)
    (h : ∀ b, b ≠ a → p.mass b = q.mass b) : p = q := by
  apply RationalLaw.ext
  funext b
  by_cases hb : b = a
  · subst b
    have hp := Finset.sum_erase_add (Finset.univ : Finset α) p.mass (Finset.mem_univ a)
    have hq := Finset.sum_erase_add (Finset.univ : Finset α) q.mass (Finset.mem_univ a)
    have he : (∑ b ∈ Finset.univ.erase a, p.mass b) = ∑ b ∈ Finset.univ.erase a, q.mass b := by
      apply Finset.sum_congr rfl
      intro b hb
      exact h b (Finset.mem_erase.mp hb).1
    rw [p.total] at hp
    rw [q.total] at hq
    rw [he] at hp
    linarith
  · exact h b hb

end

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordPadding
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reserving a common word length for adaptive bounded draws -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture FairBits

noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]

lemma mapLaw_product_fst (p : RationalLaw A) (q : RationalLaw B) :
    mapLaw (productLaw p q) Prod.fst=p := by
  apply RationalLaw.ext
  funext x
  simp only [mapLaw, productLaw, Fintype.sum_prod_type]
  change (∑ a,∑ b,if a=x then p.mass a*q.mass b else 0)=p.mass x
  have hs (a : A) : (∑ b,if a=x then p.mass a*q.mass b else 0)=if a=x then p.mass a else 0 := by
    by_cases ha : a=x
    · simp only [ha,ite_true, if_true,←Finset.mul_sum,q.total,mul_one]
    · simp only [ha,ite_false,Finset.sum_const_zero]
  simp_rw [hs]
  simp

def paddingWordEquiv {k N : ℕ} (hk : k ≤ N) :
    (Fin N → Bool) ≃ ((Fin k → Bool) × (Fin (N-k) → Bool)) :=
  (Equiv.arrowCongr (finCongr (Nat.add_sub_of_le hk)).symm (Equiv.refl Bool)).trans
    (splitWordEquiv k (N-k))

lemma paddingWordEquiv_fst {k N : ℕ} (hk : k ≤ N) (bits : Fin N → Bool) :
    (paddingWordEquiv hk bits).1=prefixWord hk bits := by
  funext i
  change bits _=bits _
  apply congrArg bits
  apply Fin.ext
  rfl

/-- Taking the needed prefix of a larger uniform word preserves the exact
law, so unused bits can be reserved even after the current state is known. -/
theorem prefixWord_uniform {k N : ℕ} (hk : k ≤ N) :
    mapLaw (uniformLaw (α := Fin N → Bool)) (prefixWord hk)=uniformLaw (α := Fin k → Bool) := by
  have hf : prefixWord hk=fun bits => (paddingWordEquiv hk bits).1 := by
    funext bits
    exact (paddingWordEquiv_fst hk bits).symm
  rw [hf,←map_equiv (paddingWordEquiv hk),uniform_equiv,←uniform_product,mapLaw_product_fst]

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- An arbitrary finite draw keeps its law when padded to the common
bound; this applies separately at every state of an adaptive walk. -/
theorem padded_draw_law {k N : ℕ} (hk : k ≤ N) (draw : (Fin k → Bool) → Y) :
    mapLaw (uniformLaw (α := Fin N → Bool)) (fun bits => draw (prefixWord hk bits))=
      mapLaw (uniformLaw (α := Fin k → Bool)) draw := by
  rw [←mapLaw_comp,prefixWord_uniform]

end
end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRationalUpdates
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational multiplier updates of the outer annealing run -/

namespace ContingencyTables.CompanionRationalUpdates

open CompanionFactorialApplication
open CommonBasesFPRAS TwoLiftStates
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def plainCount (A : Instance I J) (l : List (Set (Labels A×Bool))) : ℕ :=
  l.countP (fun S => decide (PlainState pairs S))

def defectCount (A : Instance I J) (l : List (Set (Labels A×Bool))) (p q : Pair A) : ℕ :=
  l.countP (fun S => decide (DefectState pairs p q S))

/-- Every decision to divide is preceded by the literal positive-count
check used in the source algorithm. -/
def CountsPositive (A : Instance I J) (l : List (Set (Labels A×Bool))) : Prop :=
  0 < plainCount A l ∧ ∀ p∈pairs,∀ q∈pairs,p≠q → 0 < defectCount A l p q

def checkedUpdate (A : Instance I J) (w : Pair A → Pair A → ℚ)
    (l : List (Set (Labels A×Bool))) : Option (Pair A → Pair A → ℚ) :=
  if CountsPositive A l then some (rationalLearn pairs w l) else none

end

end ContingencyTables.CompanionRationalUpdates

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerLeafEnergy
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual leaf energy as a finite sum of complete displays -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open FactorialSignatures BalancedFamily BalancedEnumeration IntegerMarginal

universe u

def IntegerExchangeAdjacent {C : Type*} [DecidableEq C] (X Y : C → ℕ) : Prop :=
  ∃ (D : C → ℕ) (i j : C), i ≠ j ∧ 0 < D i ∧ 0 < D j ∧
    X=removeOne D i ∧ Y=removeOne D j

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteExchangeDegree
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A literal finite list of all unit-exchange neighbors -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped Classical
open FactorialSignatures

variable {C : Type*} [DecidableEq C]

lemma adjacent_eq_exchangeTarget {X Y : C → ℕ} (h : IntegerExchangeAdjacent X Y) :
    ∃ i j,i≠j ∧ Y=exchangeTarget X i j := by
  obtain ⟨D,i,j,hij,hi,hj,rfl,rfl⟩ := h
  refine ⟨i,j,hij,?_⟩
  funext a
  unfold exchangeTarget removeOne
  by_cases hai : a=i
  · subst a
    simp only [hij,ite_true, if_true,ite_false,Nat.sub_zero]
    omega
  · by_cases haj : a=j
    · subst a
      simp only [hai,ite_true, if_true,ite_false,Nat.sub_zero,Nat.add_zero]
    · simp only [hai,haj,ite_false,Nat.sub_zero,Nat.add_zero]

lemma adjacent_mem_candidates [Fintype C] {X Y : C → ℕ} (h : IntegerExchangeAdjacent X Y) :
    Y ∈ exchangeCandidates X := by
  obtain ⟨i,j,_,rfl⟩ := adjacent_eq_exchangeTarget h
  exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_ArithmeticSize
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackComposition
open Turing MachineCost

variable {K Λ P σ : Type*} {Γ : K → Type*} [DecidableEq K]
omit [DecidableEq K] in
lemma mapCfg_none (f : Λ → P) (h : Option P) (v : σ) (S : ∀ k,List (Γ k)) :
    mapCfg f h ⟨none,v,S⟩=⟨h,v,S⟩ := rfl

open Turing MachineCost

end MatchingFPRAS.StackComposition

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeFraction
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def repr (q : ℚ) : Fraction := (q.num.natAbs,q.den)

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_Repair
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Repair of a defect with its large completion

The two full matrices give the row and column views, agreeing at all
large cells. Moving one unit from the positive cell to the crossing cell
and resetting the column view preserves the enlarged margins. This is the
joint-object injection underlying the repair in paper 200-01.
-/

namespace ContingencyTables

open Finset

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [Fintype J] in
theorem transferInt_nonnegative (X : I → J → ℕ) (source receiver : I × J)
    (hsource : 0 < X source.1 source.2) (i : I) (j : J) :
    0 ≤ transferInt X source receiver i j := by
  by_cases h : i = source.1 ∧ j = source.2
  · obtain ⟨rfl, rfl⟩ := h
    simp only [transferInt, and_self, ite_true, if_true]
    split_ifs <;> omega
  · simp only [transferInt, h, ite_false, sub_zero]
    split_ifs <;> omega

omit [Fintype I] in
theorem transferInt_row (X : I → J → ℕ) (source receiver : I × J) (i : I) :
    ∑ j, transferInt X source receiver i j = (∑ j, (X i j : ℤ)) -
      (if i = source.1 then 1 else 0) + (if i = receiver.1 then 1 else 0) := by
  simp only [transferInt, sum_add_distrib, sum_sub_distrib, ite_and]
  simp

omit [Fintype J] in
theorem transferInt_column (X : I → J → ℕ) (source receiver : I × J) (j : J) :
    ∑ i, transferInt X source receiver i j = (∑ i, (X i j : ℤ)) -
      (if j = source.2 then 1 else 0) + (if j = receiver.2 then 1 else 0) := by
  have h (i : I) (p : I × J) : (i = p.1 ∧ j = p.2) ↔ (j = p.2 ∧ i = p.1) := and_comm
  simp only [transferInt, sum_add_distrib, sum_sub_distrib, h, ite_and]
  simp

omit [Fintype I] [Fintype J] in
theorem IsDefect.positive_entry {x q : I → J → ℕ} {s t : I × J}
    (h : IsDefect x q s t) : 0 < x t.1 t.2 := by
  have hst : ¬(t.1 = s.1 ∧ t.2 = s.2) := by
    rintro ⟨h₁, h₂⟩
    exact h.1 (Prod.ext h₁.symm h₂.symm)
  have heq := h.2 t.1 t.2
  simp only [transferInt, and_self, ite_true, if_true, hst, ite_false, add_zero] at heq
  omega

/-- The crossing receiver `(i',j)` in the manuscript. -/
def repairMatrix (x : I → J → ℕ) (s t : I × J) : I → J → ℕ :=
  fun i j => (transferInt x t (t.1, s.2) i j).toNat

omit [Fintype I] [Fintype J] in
theorem repairMatrix_cast {x q : I → J → ℕ} {s t : I × J}
    (h : IsDefect x q s t) (i : I) (j : J) :
    (repairMatrix x s t i j : ℤ) = transferInt x t (t.1, s.2) i j :=
  Int.toNat_of_nonneg (transferInt_nonnegative x t (t.1, s.2) h.positive_entry i j)

/-- The repaired matrix has the old row totals and old column-view totals.
The crossing cell may be large, and either of its coordinates may coincide
with those of the original defect cells. -/
theorem repairMatrix_margins {x q : I → J → ℕ} {s t : I × J}
    (h : IsDefect x q s t) (r : I → ℕ) (c : J → ℕ)
    (hr : ∀ i, ∑ j, x i j = r i) (hc : ∀ j, ∑ i, q i j = c j) :
    HasMargins (repairMatrix x s t) r c := by
  constructor
  · intro i
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [repairMatrix_cast h]
    rw [transferInt_row]
    simp only [sub_add_cancel, ← Nat.cast_sum, hr]
  · intro j
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [repairMatrix_cast h]
    rw [transferInt_column]
    have hcol : (∑ i, (q i j : ℤ)) = ∑ i, transferInt x t s i j := by
      apply sum_congr rfl
      intro i _
      exact h.2 i j
    rw [transferInt_column, ← Nat.cast_sum, hc] at hcol
    exact hcol.symm

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RepairResiduals
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original residual bounds are preserved by the literal repair

Only a small source entry is lowered. Every large entry is unchanged or
increased. Since full row and column-view totals are preserved, the
small row/column sums cannot increase.
-/

namespace ContingencyTables

open scoped BigOperators Classical
open PaddedCompletions CompletionCounts

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
lemma row_small_large (small : I → J → Bool) (X : I → J → ℕ) (i : I) :
    smallRow small X i+largeRow small X i=∑ j, X i j := by
  unfold smallRow largeRow
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases small i j <;> simp

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma column_small_large (small : I → J → Bool) (Q : I → J → ℕ) (j : J) :
    smallColumnView small Q j+largeColumnView small Q j=∑ i, Q i j := by
  unfold smallColumnView largeColumnView
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases small i j <;> simp

omit [Fintype I] [Fintype J] in
lemma repairMatrix_large {small : I → J → Bool} {x q : I → J → ℕ} {s t : I×J}
    (h : IsDefect x q s t) (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (i : I) (j : J) (hij : small i j=false) :
    q i j=x i j ∧ x i j ≤ repairMatrix x s t i j := by
  have hne (w : I×J) (hw : small w.1 w.2=true) : ¬(i=w.1 ∧ j=w.2) := by
    rintro ⟨rfl,rfl⟩
    rw [hw] at hij
    contradiction
  have hst := hne s hs
  have htt := hne t ht
  constructor
  · apply Int.natCast_inj.mp
    rw [h.2]
    simp only [transferInt,hst,htt,↓reduceIte,sub_zero,add_zero]
  · have he := repairMatrix_cast h i j
    simp only [transferInt,htt,↓reduceIte,sub_zero] at he
    split_ifs at he <;> omega

/-- This covers small and large receivers and the two possible receiver
coincidences without a special case in the residual calculation. -/
theorem repairMatrix_small_sums {small : I → J → Bool} {x q : I → J → ℕ} {s t : I×J}
    (h : IsDefect x q s t) (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) :
    (∀ i, smallRow small (repairMatrix x s t) i ≤ smallRow small x i) ∧
      (∀ j, smallColumnView small (repairMatrix x s t) j ≤ smallColumnView small q j) := by
  have hm := repairMatrix_margins h (fun i => ∑ j, x i j) (fun j => ∑ i, q i j)
    (fun _ => rfl) (fun _ => rfl)
  constructor
  · intro i
    have hlarge : largeRow small x i ≤ largeRow small (repairMatrix x s t) i := by
      apply Finset.sum_le_sum
      intro j _
      cases hij : small i j
      · exact (repairMatrix_large h hs ht i j hij).2
      · exact le_rfl
    have h0 := row_small_large small x i
    have h1 := row_small_large small (repairMatrix x s t) i
    rw [hm.1] at h1
    dsimp only at h1
    omega
  · intro j
    have hlarge : largeColumnView small q j ≤ largeColumnView small (repairMatrix x s t) j := by
      apply Finset.sum_le_sum
      intro i _
      cases hij : small i j
      · obtain ⟨he,hge⟩ := repairMatrix_large h hs ht i j hij
        simpa [he] using hge
      · exact le_rfl
    have h0 := column_small_large small q j
    have h1 := column_small_large small (repairMatrix x s t) j
    rw [hm.2] at h1
    dsimp only at h1
    omega

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
lemma entry_le_smallRow (small : I → J → Bool) (X : I → J → ℕ) (i : I) (j : J)
    (hij : small i j=true) : X i j ≤ smallRow small X i := by
  have h := Finset.single_le_sum (fun k _ => Nat.zero_le (if small i k then X i k else 0))
    (Finset.mem_univ j)
  simpa only [smallRow,smallColumnView,hij,↓reduceIte] using h

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma entry_le_smallColumn (small : I → J → Bool) (Q : I → J → ℕ) (i : I) (j : J)
    (hij : small i j=true) : Q i j ≤ smallColumnView small Q j := by
  have h := Finset.single_le_sum (fun k _ => Nat.zero_le (if small k j then Q k j else 0))
    (Finset.mem_univ i)
  simpa only [smallRow,smallColumnView,hij,↓reduceIte] using h

/-- Every repaired small cell respects the manuscript's actual U box,
because one of its original incident margins is strictly below U. -/
theorem repairMatrix_small_capacity {x q : I → J → ℕ} {s t : I×J}
    (r : I → ℕ) (c : J → ℕ) (U : ℕ) (h : IsDefect x q s t)
    (hs : firstPaperSmall r c U s.1 s.2=true) (ht : firstPaperSmall r c U t.1 t.2=true)
    (hr : ∀ i, smallRow (firstPaperSmall r c U) x i ≤ r i)
    (hc : ∀ j, smallColumnView (firstPaperSmall r c U) q j ≤ c j)
    (i : I) (j : J) (hij : firstPaperSmall r c U i j=true) :
    repairMatrix x s t i j < U := by
  obtain ⟨hrow,hcol⟩ := repairMatrix_small_sums h hs ht
  have h1 := (entry_le_smallRow _ (repairMatrix x s t) i j hij).trans ((hrow i).trans (hr i))
  have h2 := (entry_le_smallColumn _ (repairMatrix x s t) i j hij).trans ((hcol j).trans (hc j))
  have hinc : r i<U ∨ c j<U := by simpa only [firstPaperSmall,decide_eq_true_eq] using hij
  rcases hinc with hinc|hinc
  · exact h1.trans_lt hinc
  · exact h2.trans_lt hinc

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RepairFibres
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint state-completion repair injections, including fixed contexts

Full row and column views retain the large completion explicitly. Their
finite fibre cardinalities therefore count states with the correct
completion multiplicity. The target repair is a balanced full table.
-/

namespace ContingencyTables

open scoped BigOperators Classical
open PaddedCompletions

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

instance rowColumnPairFinite (r : I → ℕ) (c : J → ℕ) : Finite (RowColumnPair r c) := by
  let encode : RowColumnPair r c → ((i : I) → J → Fin (r i+1)) × ((j : J) → I → Fin (c j+1)) :=
    fun Z => (fun i j => ⟨Z.val.1 i j,Nat.lt_succ_of_le (by
      rw [←Z.property.1 i]
      exact Finset.single_le_sum (f := fun k => Z.val.1 i k)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))⟩,
      fun j i => ⟨Z.val.2 i j,Nat.lt_succ_of_le (by
        rw [←Z.property.2 j]
        exact Finset.single_le_sum (f := fun k => Z.val.2 k j)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))⟩)
  apply Finite.of_injective encode
  intro X Y he
  apply Subtype.ext
  apply Prod.ext
  · funext i j
    exact congrArg Fin.val (congrFun (congrFun (congrArg Prod.fst he) i) j)
  · funext i j
    exact congrArg Fin.val (congrFun (congrFun (congrArg Prod.snd he) j) i)

noncomputable instance rowColumnPairFintype (r : I → ℕ) (c : J → ℕ) : Fintype (RowColumnPair r c) :=
  Fintype.ofFinite _

def ResidualTables (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) :=
  {T : Table rbar cbar // (∀ i, smallRow small T.val i ≤ r i) ∧
    (∀ j, smallColumnView small T.val j ≤ c j)}

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallContextCount
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal contextual mass domination by repair

Finite sums of the actual hard completion weights, including all large
completions, are compared by the concrete repair injection.
-/

namespace ContingencyTables.SmallContextFibres

open scoped BigOperators Classical
open PaddedCompletions CompletionCounts
open FirstPaperPhysicalMarginal

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [LinearOrder I] [LinearOrder J]

omit [DecidableEq I] [DecidableEq J] [LinearOrder I] [LinearOrder J] in
/-- The manuscript's actual capacity excludes no residual table. -/
theorem paper_residual_capacity (r : I → ℕ) (c : J → ℕ) (d L U : ℕ)
    (hd : Fintype.card I*Fintype.card J ≤ d)
    (T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L)) (i : I) (j : J) :
    T.val.val i j ≤ paperCapacity (firstPaperSmall r c U) r d L U i j := by
  let small := firstPaperSmall r c U
  change T.val.val i j ≤ paperCapacity small r d L U i j
  cases hs : small i j
  · have he := entry_le_total T.val.property i j
    have hcount := (large_count_le_dimension small).trans hd
    have heq : (∑ k, (r k+rowLargeCount small k*L))=
        (∑ k, r k)+(∑ k, rowLargeCount small k)*L := by
      rw [Finset.sum_add_distrib,Finset.sum_mul]
    rw [heq] at he
    have hb := Nat.mul_le_mul_right L hcount
    simp only [paperCapacity,hs,Bool.false_eq_true,↓reduceIte]
    omega
  · have hr := (entry_le_smallRow small T.val.val i j hs).trans (T.property.1 i)
    have hc := (entry_le_smallColumn small T.val.val i j hs).trans (T.property.2 j)
    have hinc : r i<U ∨ c j<U := by simpa only [small,firstPaperSmall,decide_eq_true_eq] using hs
    simp only [paperCapacity,hs,↓reduceIte]
    rcases hinc with hinc|hinc <;> omega

end ContingencyTables.SmallContextFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileRepair
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal small-profile repair and its typewise inverse -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma repairMatrix_pointwise (x y : I → J → ℕ) (s t : I×J) (i : I) (j : J)
    (h : x i j=y i j) : repairMatrix x s t i j=repairMatrix y s t i j := by
  simp only [repairMatrix,transferInt,h]

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallCellCatalogProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating the actual small cells from binary margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def smallCellCatalog (z : CellCatalogInput) : List (ℕ×ℕ) :=
  (cellPairs z.1).filter (fun a => smallCellTest (z,a))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Sampling_TreeCategorical
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def cumulativeFraction (x : List Fraction×ℕ) : Fraction := sum (x.1.take x.2)

end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableChoice
open TreeTyped TreeFraction

def predicate (x : (List Fraction×Fraction)×ℕ) : Bool :=
  TreeFraction.less (x.1.2,cumulativeFraction (x.1.1,x.2+1))

def choose (x : List Fraction×Fraction) : ℕ :=
  listMin ((List.range x.1.length).filter (fun i=>predicate (x,i)),x.1.length)

end MatchingFPRAS.ExecutableChoice

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseRationalTrial
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational ideal dense rejection law -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def rationalBinWeight (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) : ℚ :=
  1 / (2 : ℚ) ^ denseExponent R P d e a

theorem rationalBinWeight_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    (rationalBinWeight R P d e a : ℝ) = denseBinWeight R P d e a := by
  rw [denseBinWeight_eq_dyadic]
  simp only [rationalBinWeight, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]

def rationalTrialMass (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) : ℚ :=
  rationalBinWeight R P d e t.1 /
    (∑ a : Grid (I := Fin q) (4 * d ^ 8), rationalBinWeight R P d e a) /
      Fintype.card (Offset (integerWidth R P d))

theorem rationalTrialMass_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) :
    (rationalTrialMass R P d e t : ℝ) = denseTrialMass R P d e t := by
  simp only [rationalTrialMass, denseTrialMass, Rat.cast_div, Rat.cast_sum,
    Rat.cast_natCast, rationalBinWeight_cast]

def rationalTrialLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) : RationalLaw (DenseTrial R P d q) where
  mass := rationalTrialMass R P d e
  nonnegative := fun t => by
    have h := (denseTrialMass_pos R P d hd hR hP e t).le
    rw [← rationalTrialMass_cast] at h
    exact_mod_cast h
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum, rationalTrialMass_cast, Rat.cast_one]
    exact denseTrialMass_sum R P d hd hR hP e

def rationalTableMass (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (X : Table R P) : ℚ :=
  rationalTrialMass R P d e (tableTrial R P d hd hR hP e X)

theorem rationalTableMass_total (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j) :
    ((∑ X : Table R P, rationalTableMass R P d hd hR hP e X) : ℝ) =
      denseAcceptanceMass R P d e := by
  rw [denseAcceptanceMass, ← Finset.sum_filter]
  have hs : (∑ t : {t : DenseTrial R P d q // TrialAccepted R P d e t},
      denseTrialMass R P d e t.val) =
      ∑ t ∈ Finset.univ.filter (TrialAccepted R P d e), denseTrialMass R P d e t := by
    exact (Finset.sum_subtype (p := TrialAccepted R P d e)
      (Finset.univ.filter (TrialAccepted R P d e)) (fun _ => by simp)
      (denseTrialMass R P d e)).symm
  rw [← hs]
  symm
  apply Fintype.sum_equiv (acceptedTrialEquiv R P d hd hR hP e htotal)
  intro t
  simp only [rationalTableMass, rationalTrialMass_cast]
  congr 1
  exact (tableTrial_trialTable R P d hd hR hP e htotal t.val t.property).symm

theorem rationalTableMass_uniform (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q) (X : Table R P) :
    rationalTableMass R P d hd hR hP e X /
      (∑ Y : Table R P, rationalTableMass R P d hd hR hP e Y) =
        1 / Fintype.card (Table R P) := by
  apply Rat.cast_injective (α := ℝ)
  simp only [Rat.cast_div, Rat.cast_sum, Rat.cast_one, Rat.cast_natCast,
    rationalTableMass, rationalTrialMass_cast]
  exact denseTrial_conditional_uniform R P d hd hR hP hRmax hPmax hfree e X

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseRationalKernel
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational transition and walk laws for the actual dense bin chain -/

namespace ContingencyTables.GridBoundary

open CommonBasesFPRAS ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def rationalMove (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a b : Grid (I := Fin q) (4 * d ^ 8)) : ℚ :=
  if Neighbor a b then rationalProposal d * min 1 (rationalBinWeight R P d e b / rationalBinWeight R P d e a)
    else 0

def rationalTransition (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a b : Grid (I := Fin q) (4 * d ^ 8)) : ℚ :=
  rationalMove R P d e a b + if a = b then 1 - ∑ c, rationalMove R P d e a c else 0

theorem rationalMove_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a b : Grid (I := Fin q) (4 * d ^ 8)) :
    (rationalMove R P d e a b : ℝ) =
      MetropolisChain.move (denseBinWeight R P d e) Neighbor (binProposal d) a b := by
  unfold rationalMove MetropolisChain.move
  split_ifs
  · simp only [Rat.cast_mul, Rat.cast_min, Rat.cast_one, Rat.cast_div,
      rationalBinWeight_cast, rationalProposal, binProposal, Rat.cast_pow, Rat.cast_ofNat]
  · exact Rat.cast_zero

theorem rationalTransition_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (a b : Grid (I := Fin q) (4 * d ^ 8)) :
    (rationalTransition R P d e a b : ℝ) =
      (denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).P a b := by
  unfold rationalTransition
  dsimp only [denseBinChain, gridChain, MetropolisChain.chain, FiniteChain.ofMoves]
  by_cases hab : a = b <;>
    simp only [hab, ite_true, if_true, ite_false, Rat.cast_add, Rat.cast_sub, Rat.cast_sum,
      Rat.cast_one, Rat.cast_zero, rationalMove_cast]

def rationalTransitionLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (a : Grid (I := Fin q) (4 * d ^ 8)) : RationalLaw (Grid (I := Fin q) (4 * d ^ 8)) where
  mass := rationalTransition R P d e a
  nonnegative := fun b => by
    have h := (denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).nonnegative a b
    rw [← rationalTransition_cast R P d hd hfree e] at h
    exact_mod_cast h
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum, rationalTransition_cast R P d hd hfree e, Rat.cast_one]
    exact (denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).stochastic a

def rationalWalk (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) : ℕ → Grid (I := Fin q) (4 * d ^ 8) → Grid (I := Fin q) (4 * d ^ 8) → ℚ
  | 0, a, b => if a = b then 1 else 0
  | n + 1, a, b => ∑ c, rationalWalk R P d e n a c * rationalTransition R P d e c b

theorem rationalWalk_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (n : ℕ) (a b : Grid (I := Fin q) (4 * d ^ 8)) :
    (rationalWalk R P d e n a b : ℝ) =
      ((denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).kernel.power n).P a b := by
  induction n generalizing a b with
  | zero => simp only [rationalWalk, FiniteKernel.power, FiniteKernel.identity]
            split_ifs <;> norm_num
  | succ n ih =>
    simp only [rationalWalk, Rat.cast_sum, Rat.cast_mul, ih, rationalTransition_cast R P d hd hfree e,
      FiniteKernel.power, FiniteKernel.comp, FiniteChain.kernel]

def rationalWalkLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (n : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8)) : RationalLaw (Grid (I := Fin q) (4 * d ^ 8)) where
  mass := rationalWalk R P d e n a
  nonnegative := fun b => by
    have h := ((denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).kernel.power n).nonnegative a b
    rw [← rationalWalk_cast R P d hd hfree e] at h
    exact_mod_cast h
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum, rationalWalk_cast R P d hd hfree e, Rat.cast_one]
    exact (denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).kernel_power_stochastic n a

def rationalStationaryLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (e : I × J ≃ Fin q) : RationalLaw (Grid (I := Fin q) (4 * d ^ 8)) := by
  let : Nonempty (Grid (I := Fin q) (4 * d ^ 8)) :=
    ⟨fun _ => ⟨0, by have h := denseGridSize_pos d hd; constructor <;> omega⟩⟩
  let w := rationalBinWeight R P d e
  have hw : ∀ a : Grid (I := Fin q) (4 * d ^ 8), 0 < w a := fun a => by
    unfold w rationalBinWeight
    positivity
  have hZ : 0 < ∑ a, w a := Finset.sum_pos (fun a _ => hw a) Finset.univ_nonempty
  exact ⟨fun a => w a / ∑ b, w b, fun a => (div_pos (hw a) hZ).le,
    by rw [← Finset.sum_div]; exact div_self (ne_of_gt hZ)⟩

theorem rationalStationaryLaw_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (a : Grid (I := Fin q) (4 * d ^ 8)) :
    ((rationalStationaryLaw R P d hd e).mass a : ℝ) =
      (denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).π a := by
  change ((rationalBinWeight R P d e a / ∑ b, rationalBinWeight R P d e b : ℚ) : ℝ) = _
  simp only [Rat.cast_div, Rat.cast_sum, rationalBinWeight_cast]
  rfl

/-- The exact rational finite-walk law satisfies the dense sampler's mixing
bound. The hypotheses are precisely the two published geometric inputs. -/
theorem rationalWalkLaw_variation (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8)))
    (h : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    (variation (rationalWalkLaw R P d hd hfree e (d ^ 50 * (h + 1) ^ 2) a)
      (rationalStationaryLaw R P d hd e) : ℝ) ≤
        (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
  let C := denseBinChain R P d hd hfree e (denseGridSize_pos d hd)
  let δ := (2 : ℝ) ^ (-(4 * ((h : ℝ) + d)))
  let n := d ^ 50 * (h + 1) ^ 2
  have hpoint (b : Grid (I := Fin q) (4 * d ^ 8)) :
      |(C.kernel.power n).P a b - C.π b| ≤ C.π b * δ := by
    have hm := denseBinChain_relative_mixing R P d hd hR hP hRmax hPmax
      hdimR hdimP hfree htotal e hPL hCheeger h a b
    change |C.iterate n (C.pointDensity b) a - 1| ≤ δ at hm
    rw [← C.kernel_power_density] at hm
    calc
      _ = C.π b * |(C.kernel.power n).P a b / C.π b - 1| := by
        calc
          _ = |C.π b * ((C.kernel.power n).P a b / C.π b - 1)| := by
            congr 1
            field_simp [ne_of_gt (C.positive b)]
          _ = _ := by rw [abs_mul, abs_of_pos (C.positive b)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (C.positive b).le
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpoint b)
  rw [← Finset.sum_mul, C.normalized, one_mul] at hsum
  unfold variation
  simp only [Rat.cast_div, Rat.cast_sum, Rat.cast_abs, Rat.cast_sub, Rat.cast_ofNat,
    rationalWalkLaw, rationalWalk_cast R P d hd hfree e, rationalStationaryLaw_cast R P d hd hfree e]
  change (∑ b, |(C.kernel.power n).P a b - C.π b|) / 2 ≤ δ
  have hδ : 0 ≤ δ := (Real.rpow_pos_of_pos (by norm_num) _).le
  linarith

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBoundedTrial
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite dense trial with bounded independent offset draws -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def boundedOffsetLaw (e : I × J ≃ Fin q) (w : I × J → ℕ)
    (hw : ∀ p, 0 < w p) (h d : ℕ) : RationalLaw (Offset w) :=
  equivLaw (offsetCoordinateEquiv e w)
    (piLaw (fun j => scaledLaw (w (e.symm j)) (offsetBitLength (w (e.symm j)) h d) (hw _)))

def uniformOffsetLaw (e : I × J ≃ Fin q) (w : I × J → ℕ)
    (hw : ∀ p, 0 < w p) : RationalLaw (Offset w) :=
  equivLaw (offsetCoordinateEquiv e w) (piLaw (fun j => uniformIntLaw (w (e.symm j)) (hw _)))

theorem uniformOffsetLaw_mass (e : I × J ≃ Fin q) (w : I × J → ℕ)
    (hw : ∀ p, 0 < w p) (o : Offset w) :
    (uniformOffsetLaw e w hw).mass o = 1 / Fintype.card (Offset w) := by
  have hc := Fintype.card_congr (offsetCoordinateEquiv e w)
  simp only [Fintype.card_pi, Fintype.card_fin] at hc
  change (∏ j : Fin q, (1 : ℚ) / w (e.symm j)) = _
  rw [Finset.prod_div_distrib, Finset.prod_const_one, ← Nat.cast_prod, hc]
  simp [Offset]

theorem boundedOffsetLaw_variation (e : I × J ≃ Fin q) (w : I × J → ℕ)
    (hw : ∀ p, 0 < w p) (h d : ℕ) (hq : q ≤ d) :
    variation (boundedOffsetLaw e w hw h d) (uniformOffsetLaw e w hw) ≤
      (d : ℚ) / (2 : ℚ) ^ (4 * (h + d)) := by
  rw [boundedOffsetLaw, uniformOffsetLaw, variation_equiv]
  exact dense_offset_product_variation q h d (fun j => w (e.symm j)) (fun j => hw _) hq

def boundedTrialLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q) (h : ℕ)
    (a : Grid (I := Fin q) (4 * d ^ 8)) : RationalLaw (DenseTrial R P d q) :=
  productLaw (rationalWalkLaw R P d hd hfree e (d ^ 50 * (h + 1) ^ 2) a)
    (boundedOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d)

theorem stationaryTrialLaw_eq (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) :
    productLaw (rationalStationaryLaw R P d hd e)
      (uniformOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP)) =
        rationalTrialLaw R P d hd hR hP e := by
  apply RationalLaw.ext
  funext t
  change (rationalStationaryLaw R P d hd e).mass t.1 *
    (uniformOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP)).mass t.2 = _
  rw [uniformOffsetLaw_mass]
  change (rationalBinWeight R P d e t.1 / ∑ b, rationalBinWeight R P d e b) *
    (1 / Fintype.card (Offset (integerWidth R P d))) = rationalTrialMass R P d e t
  unfold rationalTrialMass
  ring

/-- A complete finite dense trial has bin-mixing error plus the bounded
offset error, with the manuscript's actual walk and offset schedules. -/
theorem boundedTrialLaw_variation (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8)))
    (h : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    (variation (boundedTrialLaw R P d hd hR hP hfree e h a)
      (rationalTrialLaw R P d hd hR hP e) : ℝ) ≤
        (1 + (d : ℝ)) * (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
  have hq : q ≤ d := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin] at hc
    omega
  have ho := boundedOffsetLaw_variation e (integerWidth R P d)
    (integerWidth_pos R P d hd hR hP) h d hq
  have hoc : (variation (boundedOffsetLaw e (integerWidth R P d)
      (integerWidth_pos R P d hd hR hP) h d)
      (uniformOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP)) : ℝ) ≤
        ((d : ℚ) / (2 : ℚ) ^ (4 * (h + d)) : ℚ) := by exact_mod_cast ho
  have he : (((d : ℚ) / (2 : ℚ) ^ (4 * (h + d)) : ℚ) : ℝ) =
      (d : ℝ) * (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
    rw [div_eq_mul_one_div, Rat.cast_mul, Rat.cast_natCast, inverse_two_pow_cast]
    congr 2
    push_cast
    ring
  rw [he] at hoc
  rw [← stationaryTrialLaw_eq R P d hd hR hP e]
  unfold boundedTrialLaw
  have hv := variation_product (rationalWalkLaw R P d hd hfree e (d ^ 50 * (h + 1) ^ 2) a)
    (rationalStationaryLaw R P d hd e)
    (boundedOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d)
    (uniformOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP))
  have hvc : (variation
      (productLaw (rationalWalkLaw R P d hd hfree e (d ^ 50 * (h + 1) ^ 2) a)
        (boundedOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d))
      (productLaw (rationalStationaryLaw R P d hd e)
        (uniformOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP))) : ℝ) ≤
      (variation (rationalWalkLaw R P d hd hfree e (d ^ 50 * (h + 1) ^ 2) a)
        (rationalStationaryLaw R P d hd e) : ℝ) +
      (variation (boundedOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d)
        (uniformOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP)) : ℝ) := by
    exact_mod_cast hv
  have hm := rationalWalkLaw_variation R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal
    e hPL hCheeger h a
  exact hvc.trans (by nlinarith)

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBooleanOffsets
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent actual Boolean offset draws realize the bounded offset law -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {q : ℕ}

abbrev OffsetWords (e : I × J ≃ Fin q) (w : I × J → ℕ) (h d : ℕ) :=
  ∀ j : Fin q, Fin (offsetBitLength (w (e.symm j)) h d) → Bool

def drawOffsetWords (e : I × J ≃ Fin q) (w : I × J → ℕ)
    (hw : ∀ p, 0 < w p) (h d : ℕ) (bits : OffsetWords e w h d) : Offset w :=
  offsetCoordinateEquiv e w (fun j =>
    scaledBitInteger (w (e.symm j)) (offsetBitLength (w (e.symm j)) h d) (hw _) (bits j))

/-- Every coordinate uses its declared independent bounded Boolean word;
the resulting offset vector has the bounded quotient-offset law. -/
theorem drawOffsetWordsLaw_eq (e : I × J ≃ Fin q) (w : I × J → ℕ)
    [DecidableEq (Offset w)]
    (hw : ∀ p, 0 < w p) (h d : ℕ) :
    mapLaw (uniformLaw (α := OffsetWords e w h d)) (drawOffsetWords e w hw h d) =
      boundedOffsetLaw e w hw h d := by
  unfold drawOffsetWords boundedOffsetLaw
  refine (mapLaw_equiv_output (offsetCoordinateEquiv e w)
    (uniformLaw (α := OffsetWords e w h d)) (fun bits j =>
      scaledBitInteger (w (e.symm j)) (offsetBitLength (w (e.symm j)) h d) (hw _)
        (bits j))).trans ?_
  congr 1
  rw [← pi_uniformLaw, pi_mapLaw]
  congr 1
  funext j
  exact scaledBitIntegerLaw_eq (w (e.symm j)) (offsetBitLength (w (e.symm j)) h d) (hw _)

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseExponentBound
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded bit allowance for every dense Metropolis decision -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

theorem denseExponent_upper (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    denseExponent R P d e a ≤ 4 * d ^ 5 := by
  have hcube (p : I × J) : 0 ≤ realCorner a (e p) ∧ realCorner a (e p) ≤ 4 * (d : ℝ) ^ 8 := by
    have hlo : (0 : ℤ) ≤ corner a (e p) := (a (e p)).property.1
    have hhi : corner a (e p) ≤ (4 * d ^ 8 : ℕ) := by
      have h : corner a (e p) ≤ (4 * d ^ 8 : ℕ) - 1 := (a (e p)).property.2
      omega
    constructor
    · change (0 : ℝ) ≤ (corner a (e p) : ℝ)
      exact_mod_cast hlo
    · change (corner a (e p) : ℝ) ≤ 4 * (d : ℝ) ^ 8
      exact_mod_cast hhi
  have hp := (DenseAffine.densePenalty_cube_bound R P d hd hR hP hRmax hPmax
    hdimR hdimP hfree htotal _ hcube).2
  have he : (denseExponent R P d e a : ℝ) =
      (⌊(d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a)⌋ : ℤ) := by
    exact_mod_cast denseExponent_eq_floor R P d e a
  have hf := Int.floor_le ((d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a))
  have hmul := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ (d : ℝ) ^ 4 by positivity)
  change (d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a) ≤ (d : ℝ) ^ 4 * (4 * d) at hmul
  have hbound : (denseExponent R P d e a : ℝ) ≤ 4 * (d : ℝ) ^ 5 := by
    rw [he]
    nlinarith
  exact_mod_cast hbound

/-- The paper's fixed allowance implements every possible acceptance
probability exactly, including a proposed move whose probability is one. -/
theorem denseMetropolis_finite_coin (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a b : Grid (I := Fin q) (4 * d ^ 8)) :
    ((Finset.univ.filter (FairBits.acceptDyadic
      (denseExponent R P d e b - denseExponent R P d e a) (8 * d ^ 5))).card : ℝ) /
        (2 : ℝ) ^ (8 * d ^ 5) =
      min 1 (denseBinWeight R P d e b / denseBinWeight R P d e a) := by
  rw [FairBits.acceptDyadic_probability]
  · exact (dense_acceptance_dyadic R P d e a b).symm
  · exact (Nat.sub_le _ _).trans ((denseExponent_upper R P d hd hR hP hRmax hPmax
      hdimR hdimP hfree htotal e b).trans (by omega))

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseFiniteTransition
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded finite fair-bit experiment implements the dense transition -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CommonBasesFPRAS

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def finiteDenseStepLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    RationalLaw (Grid (I := Fin q) (4 * d ^ 8)) :=
  finiteAcceptLaw a
    (fun z : Fin (2 ^ Nat.clog 2 (8 * d)) => axisCodeStep a z)
    (fun b => FairBits.acceptDyadic
      (denseExponent R P d e b - denseExponent R P d e a) (8 * d ^ 5))

/-- A proposal integer followed by the fixed acceptance allowance realizes
the entire dense transition law, including unused codes and rejected moves. -/
theorem finiteDenseStepLaw_eq (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    finiteDenseStepLaw R P d e a = rationalTransitionLaw R P d hd hfree e a := by
  have hq : q ≤ d := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin] at hc
    omega
  apply RationalLaw.eq_of_off_diagonal _ _ a
  intro b hba
  apply Rat.cast_injective (α := ℝ)
  change ((finiteAcceptLaw a
    (fun z : Fin (2 ^ Nat.clog 2 (8 * d)) => axisCodeStep a z)
    (fun b => FairBits.acceptDyadic
      (denseExponent R P d e b - denseExponent R P d e a) (8 * d ^ 5))).mass b : ℝ) =
      (rationalTransition R P d e a b : ℝ)
  rw [finiteAcceptLaw_off_diagonal a b _ _ hba.symm,
    axisCodeStep_count (dense_proposal_code_bound d q hq)]
  simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat]
  push_cast
  rw [Finset.filter_congr_decidable (Finset.univ : Finset (Fin (2 ^ (8 * d ^ 5))))
    (FairBits.acceptDyadic (denseExponent R P d e b - denseExponent R P d e a) (8 * d ^ 5))
    (fun z => Classical.propDecidable _)]
  rw [denseMetropolis_finite_coin R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e a b]
  unfold rationalTransition
  rw [ite_eq_right hba.symm, add_zero, rationalMove_cast]
  unfold MetropolisChain.move binProposal
  by_cases hab : Neighbor a b <;> simp [hab]

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBooleanStep
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed Boolean word realizes each exact dense transition -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseBitStep (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8))
    (bits : Fin (denseStepBits d) → Bool) : Grid (I := Fin q) (4 * d ^ 8) :=
  let z := pairWordEquiv (Nat.clog 2 (8 * d)) (8 * d ^ 5) bits
  match axisCodeStep a z.1 with
  | none => a
  | some b => if z.2.val < 2 ^ (8 * d ^ 5 - (denseExponent R P d e b - denseExponent R P d e a))
      then b else a

def denseBitStepLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    RationalLaw (Grid (I := Fin q) (4 * d ^ 8)) :=
  mapLaw (uniformLaw (α := Fin (denseStepBits d) → Bool)) (denseBitStep R P d e a)

omit [DecidableEq I] [DecidableEq J] in
theorem denseBitStepLaw_eq_finite (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    denseBitStepLaw R P d e a = finiteDenseStepLaw R P d e a := by
  let E := pairWordEquiv (Nat.clog 2 (8 * d)) (8 * d ^ 5)
  let f := finiteAcceptStep a
    (fun z : Fin (2 ^ Nat.clog 2 (8 * d)) => axisCodeStep a z)
    (fun b => FairBits.acceptDyadic
      (denseExponent R P d e b - denseExponent R P d e a) (8 * d ^ 5))
  have hf : denseBitStep R P d e a = fun bits => f (E bits) := by
    funext bits
    dsimp [denseBitStep, f, E, finiteAcceptStep]
    simp only [FairBits.acceptDyadic]
    cases axisCodeStep a ((pairWordEquiv (Nat.clog 2 (8 * d)) (8 * d ^ 5)) bits).1 with
    | none => rfl
    | some b => dsimp only; split_ifs <;> rfl
  unfold denseBitStepLaw
  rw [hf]
  change mapLaw (uniformLaw (α := Fin (Nat.clog 2 (8 * d) + 8 * d ^ 5) → Bool))
    (fun bits => f (E bits)) = _
  rw [← map_equiv E, uniform_equiv]
  rw [← uniform_product]
  rfl

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseFiniteWalk
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent bounded dense transitions realize the mixed bin law -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def finiteDenseWalkLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) (n : ℕ) :
    RationalLaw (Grid (I := Fin q) (4 * d ^ 8)) :=
  walkLaw (finiteDenseStepLaw R P d e) a n

theorem finiteDenseWalkLaw_eq (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) (n : ℕ) :
    finiteDenseWalkLaw R P d e a n = rationalWalkLaw R P d hd hfree e n a := by
  induction n with
  | zero =>
    apply RationalLaw.ext
    funext b
    change (if b = a then (1 : ℚ) else 0) = if a = b then 1 else 0
    simp [eq_comm]
  | succ n ih =>
    apply RationalLaw.ext
    funext b
    change (∑ c, (finiteDenseWalkLaw R P d e a n).mass c * (finiteDenseStepLaw R P d e c).mass b) =
      ∑ c, rationalWalk R P d e n a c * rationalTransition R P d e c b
    rw [ih]
    apply Finset.sum_congr rfl
    intro c _
    rw [finiteDenseStepLaw_eq R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e c]
    rfl

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBooleanWalk
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The dense bin draw as one bounded unbiased Boolean word -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseBooleanWalk (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) (n : ℕ)
    (bits : Fin (n * denseStepBits d) → Bool) : Grid (I := Fin q) (4 * d ^ 8) :=
  wordWalk (denseBitStep R P d e) a n (gridWordEquiv n (denseStepBits d) bits)

def denseBooleanWalkLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) (n : ℕ) :
    RationalLaw (Grid (I := Fin q) (4 * d ^ 8)) :=
  mapLaw (uniformLaw (α := Fin (n * denseStepBits d) → Bool)) (denseBooleanWalk R P d e a n)

/-- Exactly n*(q_bin+8d^5) unbiased bits give the rational n-step law. -/
theorem denseBooleanWalkLaw_eq (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) (n : ℕ) :
    denseBooleanWalkLaw R P d e a n = rationalWalkLaw R P d hd hfree e n a := by
  have hk : (fun s => mapLaw (uniformLaw (α := Fin (denseStepBits d) → Bool)) (denseBitStep R P d e s)) =
      finiteDenseStepLaw R P d e := funext (denseBitStepLaw_eq_finite R P d e)
  unfold denseBooleanWalkLaw denseBooleanWalk
  rw [← map_equiv (gridWordEquiv n (denseStepBits d)), uniform_equiv]
  change wordWalkLaw (denseBitStep R P d e) a n = _
  rw [wordWalkLaw_eq, hk]
  exact finiteDenseWalkLaw_eq R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e a n

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBooleanTrial
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full dense trial as one bounded unbiased Boolean word -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseTrialBits (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (h : ℕ) : ℕ :=
  (d ^ 50 * (h + 1) ^ 2) * denseStepBits d +
    ∑ j : Fin q, offsetBitLength (integerWidth R P d (e.symm j)) h d

def trialWordEquiv (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (h : ℕ) : (Fin (denseTrialBits R P d e h) → Bool) ≃
    ((Fin ((d ^ 50 * (h + 1) ^ 2) * denseStepBits d) → Bool) ×
      OffsetWords e (integerWidth R P d) h d) :=
  (splitWordEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
    (dependentWordEquiv (fun j => offsetBitLength (integerWidth R P d (e.symm j)) h d)))

def denseBooleanTrial (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (h : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8))
    (bits : Fin (denseTrialBits R P d e h) → Bool) : DenseTrial R P d q :=
  let z := trialWordEquiv R P d e h bits
  (denseBooleanWalk R P d e a (d ^ 50 * (h + 1) ^ 2) z.1,
    drawOffsetWords e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d z.2)

/-- This is the exact law of the full declared Boolean trial, including
all independent quotient offsets, before its integer acceptance test. -/
theorem denseBooleanTrialLaw_eq (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (h : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    mapLaw (uniformLaw (α := Fin (denseTrialBits R P d e h) → Bool))
      (denseBooleanTrial R P d hd hR hP e h a) = boundedTrialLaw R P d hd hR hP hfree e h a := by
  unfold denseBooleanTrial
  rw [← map_equiv (trialWordEquiv R P d e h)
    (uniformLaw (α := Fin (denseTrialBits R P d e h) → Bool))
    (fun z => (denseBooleanWalk R P d e a (d ^ 50 * (h+1)^2) z.1,
      drawOffsetWords e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d z.2)),
    uniform_equiv, ← uniform_product, mapLaw_product]
  rw [show mapLaw (uniformLaw (α := Fin ((d ^ 50 * (h + 1) ^ 2) * denseStepBits d) → Bool))
      (denseBooleanWalk R P d e a (d ^ 50 * (h + 1) ^ 2)) =
      rationalWalkLaw R P d hd hfree e (d ^ 50 * (h + 1) ^ 2) a from
    denseBooleanWalkLaw_eq R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e a _]
  unfold boundedTrialLaw
  congr 1
  exact drawOffsetWordsLaw_eq e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RowMajorEnumeration
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Increasing enumeration of the actual finite small cells -/

namespace ContingencyTables.RowMajorEnumeration

open scoped Classical
open SmallContextCoordinates

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def lexCellEquiv (small : I → J → Bool) : LexCells small ≃ Cells small where
  toFun a := ⟨ofLex a.val,a.property⟩
  invFun a := ⟨toLex a.val,a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def enumeration (small : I → J → Bool) : Fin (Fintype.card (Cells small)) ≃ Cells small :=
  (monoEquivOfFin (LexCells small) (Fintype.card_congr (lexCellEquiv small))).toEquiv.trans
    (lexCellEquiv small)

end ContingencyTables.RowMajorEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RowMajorPrefixFibres
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Row-major word prefixes are the literal physical exposure contexts -/

namespace ContingencyTables.RowMajorEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres
open LargePairEnumeration BalancedFamily
open ExcessContextProfiles SmallGraphProfiles FiniteExposureVariance IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def wordChoices (small : I → J → Bool) (U : ℕ) :
    (Fin (Fintype.card (Cells small)) → Fin (U+1)) ≃ (Cells small → Fin (U+1)) where
  toFun a := a ∘ (enumeration small).symm
  invFun a := a ∘ enumeration small
  left_inv a := by funext i; exact congrArg a ((enumeration small).symm_apply_apply i)
  right_inv a := by funext i; exact congrArg a ((enumeration small).apply_symm_apply i)

end ContingencyTables.RowMajorEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TranslatedCompletionChain
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ideal chain draws an actual uniform completion then translates it -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical
open CommonBasesFPRAS

variable {X I J : Type*} [Fintype X] [Nonempty X] [Fintype I] [Fintype J]

omit [Nonempty X] in
lemma completionMove_reversible (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (hsym : ∀ x y,Adj x y ↔ Adj y x) (β : ℝ) (x y : X) :
    ((blockCount R P x:ℝ)/MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)))*
      completionMove R P Adj β x y=
    ((blockCount R P y:ℝ)/MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)))*
      completionMove R P Adj β y x := by
  have hx : (blockCount R P x:ℝ)≠0 := ne_of_gt (by exact_mod_cast blockCount_pos R P htotal x)
  have hy : (blockCount R P y:ℝ)≠0 := ne_of_gt (by exact_mod_cast blockCount_pos R P htotal y)
  unfold completionMove
  by_cases ha : Adj x y
  · rw [ite_eq_left ha,ite_eq_left ((hsym x y).mp ha),acceptedCount_symmetric R P htotal x y]
    exact (div_mul_div_cancel₀' hx _ _).trans (div_mul_div_cancel₀' hy _ _).symm
  · rw [ite_eq_right ha,ite_eq_right ((hsym x y).not.mp ha)]
    simp only [mul_zero]

noncomputable def completionChain (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (hsym : ∀ x y,Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x,(Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D:ℝ)*β ≤ 1/2) : FiniteChain X :=
  FiniteChain.ofMoves
    (fun x => (blockCount R P x:ℝ)/MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)))
    (completionMove R P Adj β)
    (fun x => div_pos (by exact_mod_cast blockCount_pos R P htotal x)
      (MetropolisChain.normalizer_pos _ (fun z => by exact_mod_cast blockCount_pos R P htotal z)))
    (by rw [← Finset.sum_div]; exact div_self (ne_of_gt
      (MetropolisChain.normalizer_pos _ (fun z => by exact_mod_cast blockCount_pos R P htotal z))))
    (completionMove_nonnegative R P Adj β hβ)
    (completionMove_row R P htotal Adj β hβ D hdegree hproposal)
    (completionMove_reversible R P htotal Adj hsym β)

end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CompletionChainFlow
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact edge flow of the completion-translation chain -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical
open CommonBasesFPRAS

variable {X I J : Type*} [Fintype X] [Nonempty X] [Fintype I] [Fintype J]

/-- The flow formula includes the holding terms: those contribute zero
energy. The numerator counts literal acceptable completion translations. -/
theorem completionChain_energy (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (hsym : ∀ x y,Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x,(Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D:ℝ)*β ≤ 1/2) (H : X → ℝ) :
    (completionChain R P htotal Adj hsym β hβ D hdegree hproposal).energy H=
      (∑ x,∑ y,if Adj x y then
        β*(acceptedCount R P x y:ℝ)*(H x-H y)^2 else 0)/
          (2*MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ))) := by
  unfold completionChain
  rw [FiniteChain.ofMoves_energy]
  simp_rw [completionMove_flow R P htotal Adj β]
  have hterm (x y : X) :
      (if Adj x y then β*(acceptedCount R P x y:ℝ)/
        MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)) else 0)*(H x-H y)^2 =
      (if Adj x y then β*(acceptedCount R P x y:ℝ)*(H x-H y)^2 else 0)/
        MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)) := by
    split_ifs <;> ring
  simp_rw [hterm,← Finset.sum_div]
  ring

end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CompletionEnergyComparison
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From literal acceptance counts to weighted graph energy -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical
open CommonBasesFPRAS

variable {X I J : Type*} [Fintype X] [Nonempty X] [Fintype I] [Fintype J]

/-- This is the actual chain energy comparison. The half-acceptance
premise is supplied by the proved reference-star small-entry estimate. -/
theorem completionChain_energy_lower
    (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (hsym : ∀ x y,Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x,(Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D:ℝ)*β ≤ 1/2)
    (haccept : ∀ x y,Adj x y → (blockCount R P x:ℝ)/2 ≤ acceptedCount R P x y)
    (H : X → ℝ) :
    β/(2*MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)))*
      ((∑ x,∑ y,if Adj x y then min (blockCount R P x:ℝ) (blockCount R P y:ℝ)*
        (H x-H y)^2 else 0)/2) ≤
      (completionChain R P htotal Adj hsym β hβ D hdegree hproposal).energy H := by
  let Z := MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ))
  have hZ : 0 < Z := MetropolisChain.normalizer_pos _
    (fun z => by exact_mod_cast blockCount_pos R P htotal z)
  have hterm (x y : X) :
      β/2*(if Adj x y then min (blockCount R P x:ℝ) (blockCount R P y:ℝ)*(H x-H y)^2 else 0) ≤
      if Adj x y then β*(acceptedCount R P x y:ℝ)*(H x-H y)^2 else 0 := by
    by_cases hxy : Adj x y
    · rw [ite_eq_left hxy,ite_eq_left hxy]
      have hm : min (blockCount R P x:ℝ) (blockCount R P y:ℝ)/2 ≤ acceptedCount R P x y :=
        (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans (haccept x y hxy)
      have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hβ) (sq_nonneg (H x-H y))
      convert hs using 1
      all_goals try with_reducible_and_instances rfl
      all_goals ring
    · rw [ite_eq_right hxy,ite_eq_right hxy,mul_zero]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) =>
    Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset X)) => hterm x y))
  simp_rw [← Finset.mul_sum] at hsum
  rw [completionChain_energy]
  have hb := div_le_div_of_nonneg_right hsum (show 0 ≤ 2*Z by positivity)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  all_goals
    dsimp only [Z]
    ring

end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallCompletionAcceptance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Half acceptance at the paper's actual padding scale -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Only the literal reference row and column are union bounded. -/
theorem reference_acceptance_half
    (R : Option I → ℕ) (P : Option J → ℕ) (D : Option I → Option J → ℤ)
    (htotal : (∑ i,R i)=∑ j,P j)
    (hzero : ∀ i j,D (some i) (some j)=0)
    (d : ℕ) (hd : 14 ≤ d)
    (hrows : Fintype.card (Option I) ≤ d) (hcols : Fintype.card (Option J) ≤ d)
    (hcross : Fintype.card I+Fintype.card J+1 ≤ d)
    (hrow : ∀ i,d^12 ≤ R i) (hcol : ∀ j,d^12 ≤ P j)
    (hbound : ∀ i j,|D i j| ≤ (10*d:ℕ)) :
    (Fintype.card (Table R P):ℝ)/2 ≤ Fintype.card (Accepted R P D) := by
  have hpad := padding_ge_twenty_dimension d hd
  have ht : 2*(10*d) ≤ d^12 := by omega
  have hfour : 4*d ≤ d^12 := by omega
  have hfrac := reference_acceptance R P D htotal hzero (d^12) d (10*d)
    (by omega) hrows hcols hrow hcol hfour ht hbound
  have hcrossR : (Fintype.card I+Fintype.card J+1:ℕ) ≤ (d:ℝ) := by exact_mod_cast hcross
  have hu : ((Fintype.card I+Fintype.card J+1:ℕ):ℝ)*
      (4*(10*d:ℕ)*(d:ℝ)^3/(d^12:ℕ)) ≤ 40*(d:ℝ)^5/(d^12:ℕ) := by
    calc
      _ ≤ (d:ℝ)*(4*(10*d:ℕ)*(d:ℝ)^3/(d^12:ℕ)) :=
        mul_le_mul_of_nonneg_right hcrossR (by positivity)
      _ = _ := by push_cast; ring
  have he := completion_rejection_lt_half d hd
  have hc : (0:ℝ) < Fintype.card (Table R P) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (table_nonempty R P htotal)
  have hh : (1/2:ℝ) ≤ (Fintype.card (Accepted R P D):ℝ)/Fintype.card (Table R P) := by linarith
  have hm := (le_div_iff₀ hc).mp hh
  linarith

end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSmallChain
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal first-paper completion chain has the stated Poincare bound -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CommonBasesFPRAS FirstPaperPhysicalMarginal CompletionCounts
open CompletionTranslation FiniteExposureVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [LinearOrder I] [LinearOrder J] in
lemma stateCapacity_small (r : I → ℕ) (c : J → ℕ) (i : I) (j : J)
    (h : paperSmall r c i j=true) :
    stateCapacity r c i j=(dimensionAllowance (I := I) (J := J))^20 := by
  simp only [stateCapacity,paperCapacity,h,ite_true, if_true]

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSmallMixing
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Minimum mass and mixing of the actual small chain -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CommonBasesFPRAS FirstPaperPhysicalMarginal CompletionCounts
open SmallContextFibres

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def stateBound (r : I → ℕ) (_c : J → ℕ) : ℕ :=
  (∑ i,r i)+(dimensionAllowance (I := I) (J := J))*
    ((dimensionAllowance (I := I) (J := J))^12)+
    (dimensionAllowance (I := I) (J := J))^20+2

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSuccessRatio
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The stationary successful-pair ratio of the first sampler -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def paperLarge (r : I → ℕ) (c : J → ℕ) : Finset (I×J) :=
  Finset.univ.filter (fun p => paperSmall r c p.1 p.2=false)

lemma large_padding_rows (small : I → J → Bool) (r : I → ℕ) (L : ℕ) :
    paddedRows r (largePadding (Finset.univ.filter (fun p : I×J => small p.1 p.2=false)) L)=
      (fun i => r i+rowLargeCount small i*L) := by
  funext i
  unfold paddedRows rowLargeCount
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  cases hs : small i j <;> simp [largePadding,hs]

lemma large_padding_columns (small : I → J → Bool) (c : J → ℕ) (L : ℕ) :
    paddedColumns c (largePadding (Finset.univ.filter (fun p : I×J => small p.1 p.2=false)) L)=
      (fun j => c j+columnLargeCount small j*L) := by
  funext j
  unfold paddedColumns columnLargeCount
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hs : small i j <;> simp [largePadding,hs]


end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedJointConstruction
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recover the unique balanced joint object from its full padded table -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open FirstPaperPhysicalMarginal
open SmallContextFibres SmallContextCoordinates RowMajorEnumeration
open PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def tableWord (small : I → J → Bool) (U : ℕ) (Y : I → J → ℕ)
    (hY : ∀ i j,small i j=true → Y i j ≤ U) :
    Fin (Fintype.card (Cells small)) → Fin (U+1) :=
  (wordChoices small U).symm (fun a => ⟨Y a.val.1 a.val.2,Nat.lt_succ_of_le (hY _ _ a.property)⟩)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalBalancedJoint
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every original table supplies its literal balanced padded joint object -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open FirstPaperPhysicalMarginal
open SmallContextFibres SmallContextCoordinates RowMajorEnumeration
open PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def paddedOriginal (small : I → J → Bool) (L : ℕ)
    {r : I → ℕ} {c : J → ℕ} (X : Table r c) :
    Table (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L) :=
  ⟨fun i j => X.val i j+if small i j then 0 else L,by
    constructor
    · intro i
      rw [Finset.sum_add_distrib,X.property.1]
      dsimp only
      unfold rowLargeCount
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      cases small i j <;> simp
    · intro j
      rw [Finset.sum_add_distrib,X.property.2]
      dsimp only
      unfold columnLargeCount
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      cases small i j <;> simp⟩

omit [LinearOrder I] [LinearOrder J] in
lemma paddedOriginal_small_rows (small : I → J → Bool) (L : ℕ)
    {r : I → ℕ} {c : J → ℕ} (X : Table r c) (i : I) :
    smallRow small (paddedOriginal small L X).val i ≤ r i := by
  calc
    _ = ∑ j,if small i j then X.val i j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      cases hs : small i j <;> simp [paddedOriginal,hs]
    _ ≤ ∑ j,X.val i j := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
    _ = _ := X.property.1 i

omit [LinearOrder I] [LinearOrder J] in
lemma paddedOriginal_small_columns (small : I → J → Bool) (L : ℕ)
    {r : I → ℕ} {c : J → ℕ} (X : Table r c) (j : J) :
    smallColumnView small (paddedOriginal small L X).val j ≤ c j := by
  calc
    _ = ∑ i,if small i j then X.val i j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases hs : small i j <;> simp [paddedOriginal,hs]
    _ ≤ ∑ i,X.val i j := Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
    _ = _ := X.property.2 j

omit [LinearOrder I] [LinearOrder J] in
lemma original_small_entry_le (r : I → ℕ) (c : J → ℕ) (U : ℕ) (X : Table r c)
    (i : I) (j : J) (hs : firstPaperSmall r c U i j=true) : X.val i j ≤ U := by
  have hh : r i<U ∨ c j<U := by simpa only [firstPaperSmall,decide_eq_true_eq] using hs
  rcases hh with hr|hc
  · exact (entry_le_row X.property i j).trans (Nat.le_of_lt hr)
  · have hcol : X.val i j ≤ c j := by
      rw [← X.property.2 j]
      exact Finset.single_le_sum (f := fun i => X.val i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact hcol.trans (Nat.le_of_lt hc)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBitBudget
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial bounds for the manuscript's bounded dense random-bit budget -/

namespace ContingencyTables.GridBoundary

theorem denseStepBits_upper (d : ℕ) : denseStepBits d ≤ 16 * d ^ 5 := by
  have hl : Nat.clog 2 (8 * d) ≤ 8 * d :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  have hd : d ≤ d ^ 5 := Nat.le_self_pow (by decide) d
  unfold denseStepBits
  omega

theorem denseOffsetBits_upper (w C b h d : ℕ) (hw : w ≤ C)
    (hb : Nat.clog 2 (C + 2) ≤ b) :
    FairBits.offsetBitLength w h d ≤ b + 1 + 4 * (h + d) := by
  have hl := (Nat.clog_mono_right 2 (by omega : w + 1 ≤ C + 2)).trans hb
  unfold FairBits.offsetBitLength
  omega

def denseRandomBitBudget (d b h : ℕ) : ℕ :=
  (d ^ 4 * (h + 1)) *
    ((d ^ 50 * (h + 1) ^ 2) * denseStepBits d + d * (b + 1 + 4 * (h + d)))

/-- The fixed declared number of dense random bits is polynomial in the
dimension parameter, binary margin length, and requested precision. -/
theorem denseRandomBitBudget_polynomial (d b h : ℕ) :
    denseRandomBitBudget d b h ≤ 25 * (d + b + h + 1) ^ 62 := by
  let S := d + b + h + 1
  have hd : d ≤ S := by omega
  have hh : h + 1 ≤ S := by omega
  have hS : 1 ≤ S := by omega
  have hQ : denseStepBits d ≤ 16 * S ^ 5 :=
    (denseStepBits_upper d).trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hd 5))
  have hH : d ^ 50 * (h + 1) ^ 2 ≤ S ^ 52 := by
    calc
      _ ≤ S ^ 50 * S ^ 2 := Nat.mul_le_mul (Nat.pow_le_pow_left hd 50) (Nat.pow_le_pow_left hh 2)
      _ = _ := (pow_add S 50 2).symm
  have hwalk : (d ^ 50 * (h + 1) ^ 2) * denseStepBits d ≤ 16 * S ^ 57 := by
    calc
      _ ≤ S ^ 52 * (16 * S ^ 5) := Nat.mul_le_mul hH hQ
      _ = _ := by rw [mul_left_comm, ← pow_add]
  have hr : b + 1 + 4 * (h + d) ≤ 9 * S := by omega
  have hoffset : d * (b + 1 + 4 * (h + d)) ≤ 9 * S ^ 57 := by
    calc
      _ ≤ S * (9 * S) := Nat.mul_le_mul hd hr
      _ = 9 * S ^ 2 := by rw [mul_left_comm, pow_two]
      _ ≤ _ := Nat.mul_le_mul_left 9 (Nat.pow_le_pow_right hS (by decide : 2 ≤ 57))
  have hJ : d ^ 4 * (h + 1) ≤ S ^ 5 := by
    calc
      _ ≤ S ^ 4 * S := Nat.mul_le_mul (Nat.pow_le_pow_left hd 4) hh
      _ = _ := (pow_succ S 4).symm
  unfold denseRandomBitBudget
  calc
    _ ≤ S ^ 5 * (25 * S ^ 57) := Nat.mul_le_mul hJ (by omega)
    _ = _ := by rw [mul_left_comm, ← pow_add]

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseIdealRejection
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded rejection of independent actual ideal dense trials -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

/-- The finite first-success law uses the actual per-table trial masses.
The sole bias after ideal trials comes from the feasible fallback. -/
theorem dense_ideal_rejection_variation (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (J₀ : ℕ) (fallback : Table R P) :
    let g := rationalTableMass R P d hd hR hP e
    (((∑ X : Table R P,
      |outputMass g (1 - ∑ Y, g Y) J₀ fallback X - uniformMass (α := Table R P)|) / 2 : ℚ) : ℝ) ≤
        (63 / 64 : ℝ) ^ J₀ := by
  let : Nonempty (Table R P) := ⟨fallback⟩
  let g := rationalTableMass R P d hd hR hP e
  let s : ℚ := ∑ X, g X
  have hcast : (s : ℝ) = denseAcceptanceMass R P d e := by
    dsimp [s, g]
    rw [Rat.cast_sum]
    exact rationalTableMass_total R P d hd hR hP e htotal
  have hs : (1 / 32 : ℚ) ≤ s := by
    have h := denseAcceptanceMass_lower R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e
    rw [← hcast] at h
    have hc : ((1 / 32 : ℚ) : ℝ) ≤ (s : ℝ) := by norm_num; exact h
    exact_mod_cast hc
  have hs1 : s ≤ 1 := by
    have h := denseAcceptanceMass_le_one R P d hd hR hP e
    rw [← hcast] at h
    exact_mod_cast h
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hg : g = fun _ => s * uniformMass (α := Table R P) := by
    funext X
    have h := rationalTableMass_uniform R P d hd hR hP hRmax hPmax hfree e X
    change g X / s = uniformMass (α := Table R P) at h
    simpa only [mul_comm] using (div_eq_iff (ne_of_gt hs0)).mp h
  have hv := stationary_variation s hs0.le hs1 J₀ fallback
  rw [← hg] at hv
  have hv' : (((∑ X : Table R P,
      |outputMass g (1 - s) J₀ fallback X - uniformMass (α := Table R P)|) / 2 : ℚ) : ℝ) ≤
        ((1 - s : ℚ) : ℝ) ^ J₀ := by exact_mod_cast hv
  apply hv'.trans
  apply pow_le_pow_left₀
  · exact_mod_cast sub_nonneg.mpr hs1
  · have h : (1 - s : ℚ) ≤ 63 / 64 := by linarith
    have hc : ((1 - s : ℚ) : ℝ) ≤ ((63 / 64 : ℚ) : ℝ) := by exact_mod_cast h
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBoundedRejection
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded dense sampler's actual finite output law -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def trialSuccess (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j)
    (t : DenseTrial R P d q) : Option (Table R P) :=
  if ht : TrialAccepted R P d e t then some (trialTable R P d e htotal t ht) else none

omit [DecidableEq I] [DecidableEq J] in
theorem trialSuccess_some_iff (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j)
    (t : DenseTrial R P d q) (X : Table R P) :
    trialSuccess R P d e htotal t = some X ↔ t = tableTrial R P d hd hR hP e X := by
  constructor
  · intro h
    unfold trialSuccess at h
    split_ifs at h with ht
    · have he := Option.some.inj h
      rw [← he, tableTrial_trialTable]
  · rintro rfl
    simp only [trialSuccess, dite_eq_left (tableTrial_accepted R P d hd hR hP e X),
      trialTable_tableTrial]

theorem trialSuccess_ideal_mass (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j) (X : Table R P) :
    successMass (rationalTrialLaw R P d hd hR hP e) (trialSuccess R P d e htotal) X =
      rationalTableMass R P d hd hR hP e X := by
  unfold successMass
  simp_rw [trialSuccess_some_iff R P d hd hR hP e htotal]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rfl

theorem trialSuccess_ideal_failure (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j) :
    failureMass (rationalTrialLaw R P d hd hR hP e) (trialSuccess R P d e htotal) =
      1 - ∑ X, rationalTableMass R P d hd hR hP e X := by
  have h := success_failure_total (rationalTrialLaw R P d hd hR hP e) (trialSuccess R P d e htotal)
  simp_rw [trialSuccess_ideal_mass R P d hd hR hP e htotal] at h
  linarith

def denseBoundedLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (htotal : ∑ i, R i = ∑ j, P j) (h : ℕ)
    (a : Grid (I := Fin q) (4 * d ^ 8)) (fallback : Table R P) : RationalLaw (Table R P) :=
  retryLaw (boundedTrialLaw R P d hd hR hP hfree e h a)
    (trialSuccess R P d e htotal) fallback (d ^ 4 * (h + 1))

/-- The finite sampler always returns an actual table and is within the
requested error of uniform, assuming finite-box interpolation and finite
Cheeger inequalities. -/
theorem denseBoundedLaw_variation (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8)))
    (h : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8)) (fallback : Table R P) :
    let _ : Nonempty (Table R P) := ⟨fallback⟩
    (variation (denseBoundedLaw R P d hd hR hP hfree e htotal h a fallback)
      (uniformLaw (α := Table R P)) : ℝ) ≤ (2 : ℝ) ^ (-(h : ℝ)) := by
  let : Nonempty (Table R P) := ⟨fallback⟩
  let p := boundedTrialLaw R P d hd hR hP hfree e h a
  let q₀ := rationalTrialLaw R P d hd hR hP e
  let f := trialSuccess R P d e htotal
  let n := d ^ 4 * (h + 1)
  have hg : successMass q₀ f = rationalTableMass R P d hd hR hP e :=
    funext (trialSuccess_ideal_mass R P d hd hR hP e htotal)
  have hf : failureMass q₀ f = 1 - ∑ X, rationalTableMass R P d hd hR hP e X :=
    trialSuccess_ideal_failure R P d hd hR hP e htotal
  have hi : (variation (retryLaw q₀ f fallback n) (uniformLaw (α := Table R P)) : ℝ) ≤
      (63 / 64 : ℝ) ^ n := by
    have hi₀ := dense_ideal_rejection_variation R P d hd hR hP hRmax hPmax hdimR hdimP
      hfree htotal e n fallback
    unfold variation
    change (((∑ X : Table R P,
      |(retryLaw q₀ f fallback n).mass X - uniformMass|) / 2 : ℚ) : ℝ) ≤ _
    simp_rw [retryLaw_mass]
    rw [hg, hf]
    exact hi₀
  have hv := retryLaw_variation p q₀ f fallback n
  have hvc : (variation (retryLaw p f fallback n) (retryLaw q₀ f fallback n) : ℝ) ≤
      (n : ℝ) * (variation p q₀ : ℝ) := by exact_mod_cast hv
  have ht := boundedTrialLaw_variation R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal
    e hPL hCheeger h a
  have hm := mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ n by positivity)
  have htri := variation_triangle (retryLaw p f fallback n) (retryLaw q₀ f fallback n)
    (uniformLaw (α := Table R P))
  have htric : (variation (retryLaw p f fallback n) (uniformLaw (α := Table R P)) : ℝ) ≤
      (variation (retryLaw p f fallback n) (retryLaw q₀ f fallback n) : ℝ) +
      (variation (retryLaw q₀ f fallback n) (uniformLaw (α := Table R P)) : ℝ) := by exact_mod_cast htri
  change (variation (retryLaw p f fallback n) (uniformLaw (α := Table R P)) : ℝ) ≤ _
  apply (htric.trans (add_le_add (hvc.trans hm) hi)).trans
  have he : (n : ℝ) * ((1 + (d : ℝ)) * (2 : ℝ) ^ (-(4 * ((h : ℝ) + d)))) =
      ((d ^ 4 * (h + 1) * (1 + d) : ℕ) : ℝ) * (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
    dsimp [n]
    push_cast
    ring
  rw [he, add_comm]
  exact dense_total_error_budget d h hd

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordRejection
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated rejection implemented by one finite independent Boolean array -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture FairBits

noncomputable section

theorem retryLaw_map {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C]
    (p : RationalLaw A) (draw : A → B) (f : B → Option C) (fallback : C) (n : ℕ) :
    retryLaw (mapLaw p draw) f fallback n = retryLaw p (fun x => f (draw x)) fallback n := by
  have hm := mapLaw_comp p draw f
  have hg : successMass (mapLaw p draw) f = successMass p (fun x => f (draw x)) := by
    funext z
    exact congrArg (fun q : RationalLaw (Option C) => q.mass (some z)) hm
  have hf : failureMass (mapLaw p draw) f = failureMass p (fun x => f (draw x)) :=
    congrArg (fun q : RationalLaw (Option C) => q.mass none) hm
  apply RationalLaw.ext
  funext z
  simp only [retryLaw_mass, hg, hf]

variable {α : Type*} [Fintype α] [DecidableEq α]

def wordRetryLaw {k : ℕ} (f : (Fin k → Bool) → Option α) (fallback : α) (n : ℕ) : RationalLaw α :=
  mapLaw (uniformLaw (α := Fin n → Fin k → Bool)) (wordRetry f fallback n)

/-- The first successful output is computed from an actual fixed Boolean
array; unused suffix words do not change its distribution. -/
theorem wordRetryLaw_eq {k : ℕ} (f : (Fin k → Bool) → Option α) (fallback : α) (n : ℕ) :
    wordRetryLaw f fallback n = retryLaw (uniformLaw (α := Fin k → Bool)) f fallback n := by
  induction n with
  | zero =>
    apply RationalLaw.ext
    funext z
    simp [wordRetryLaw, wordRetry, retryLaw, pointLaw, mapLaw, uniformLaw, uniformMass, eq_comm]
  | succ n ih =>
    let E : ((Fin k → Bool) × (Fin n → Fin k → Bool)) ≃ (Fin (n + 1) → Fin k → Bool) :=
      Fin.consEquiv (fun _ => Fin k → Bool)
    have hc : (fun z => wordRetry f fallback (n + 1) (E z)) =
        fun z => (f z.1).getD (wordRetry f fallback n z.2) := by
      funext z
      rcases z with ⟨head, tail⟩
      change (f ((Fin.cons (α := fun _ : Fin (n+1) => Fin k → Bool) head tail) 0)).getD
        (wordRetry f fallback n (Fin.tail (Fin.cons (α := fun _ : Fin (n+1) => Fin k → Bool) head tail))) = _
      simp only [Fin.cons_zero, Fin.tail_cons]
    unfold wordRetryLaw
    rw [← uniform_equiv E, map_equiv E, hc, ← uniform_product]
    have hcomp := mapLaw_comp
      (productLaw (uniformLaw (α := Fin k → Bool)) (uniformLaw (α := Fin n → Fin k → Bool)))
      (fun z => (id z.1, wordRetry f fallback n z.2)) (fun z => (f z.1).getD z.2)
    dsimp only [id_eq, Prod.fst, Prod.snd] at hcomp
    rw [← hcomp]
    have hp := mapLaw_product (uniformLaw (α := Fin k → Bool))
      (uniformLaw (α := Fin n → Fin k → Bool)) id (wordRetry f fallback n)
    dsimp only [id_eq] at hp
    rw [hp, mapLaw_id]
    change retryStep (uniformLaw (α := Fin k → Bool)) f (wordRetryLaw f fallback n) = _
    rw [ih]
    rfl

end

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBooleanDraw
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded unbiased Boolean-word dense table draw -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseDrawBits (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (h : ℕ) : ℕ :=
  (d ^ 4 * (h + 1)) * denseTrialBits R P d e h

def denseBooleanDraw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j) (h : ℕ)
    (a : Grid (I := Fin q) (4 * d ^ 8)) (fallback : Table R P)
    (bits : Fin (denseDrawBits R P d e h) → Bool) : Table R P :=
  wordRetry (fun word => trialSuccess R P d e htotal (denseBooleanTrial R P d hd hR hP e h a word))
    fallback (d ^ 4 * (h + 1)) (gridWordEquiv (d ^ 4 * (h + 1)) (denseTrialBits R P d e h) bits)

def denseBooleanDrawLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j) (h : ℕ)
    (a : Grid (I := Fin q) (4 * d ^ 8)) (fallback : Table R P) : RationalLaw (Table R P) :=
  mapLaw (uniformLaw (α := Fin (denseDrawBits R P d e h) → Bool))
    (denseBooleanDraw R P d hd hR hP e htotal h a fallback)

theorem denseBooleanDrawLaw_eq (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (h : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8)) (fallback : Table R P) :
    denseBooleanDrawLaw R P d hd hR hP e htotal h a fallback =
      denseBoundedLaw R P d hd hR hP hfree e htotal h a fallback := by
  unfold denseBooleanDrawLaw denseBooleanDraw
  change mapLaw (uniformLaw (α := Fin ((d^4*(h+1))*denseTrialBits R P d e h) → Bool))
    (fun bits => wordRetry
      (fun word => trialSuccess R P d e htotal (denseBooleanTrial R P d hd hR hP e h a word))
      fallback (d^4*(h+1)) (gridWordEquiv (d^4*(h+1)) (denseTrialBits R P d e h) bits)) = _
  rw [← map_equiv (gridWordEquiv (d ^ 4 * (h + 1)) (denseTrialBits R P d e h)), uniform_equiv]
  change wordRetryLaw
    (fun word => trialSuccess R P d e htotal (denseBooleanTrial R P d hd hR hP e h a word))
    fallback (d ^ 4 * (h + 1)) = _
  rw [wordRetryLaw_eq, ← retryLaw_map,
    denseBooleanTrialLaw_eq R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e h a]
  rfl

/-- The actual finite Boolean draw always has codomain the feasible tables
and its law satisfies the desired dense approximation guarantee. -/
theorem denseBooleanDraw_variation (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8)))
    (h : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8)) (fallback : Table R P) :
    let _ : Nonempty (Table R P) := ⟨fallback⟩
    (variation (denseBooleanDrawLaw R P d hd hR hP e htotal h a fallback)
      (uniformLaw (α := Table R P)) : ℝ) ≤ (2 : ℝ) ^ (-(h : ℝ)) := by
  let : Nonempty (Table R P) := ⟨fallback⟩
  rw [denseBooleanDrawLaw_eq R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e h a fallback]
  exact denseBoundedLaw_variation R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal
    e hPL hCheeger h a fallback

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- The full Boolean source has polynomial length in the declared dense
parameters. -/
theorem denseDrawBits_polynomial (R : Option I → ℕ) (P : Option J → ℕ)
    (d C b h : ℕ) (e : I × J ≃ Fin q) (hq : q ≤ d)
    (hwidth : ∀ p, integerWidth R P d p ≤ C) (hb : Nat.clog 2 (C + 2) ≤ b) :
    denseDrawBits R P d e h ≤ 25 * (d + b + h + 1) ^ 62 := by
  have hoff : (∑ j : Fin q, offsetBitLength (integerWidth R P d (e.symm j)) h d) ≤
      d * (b + 1 + 4 * (h + d)) := by
    calc
      _ ≤ ∑ _j : Fin q, (b + 1 + 4 * (h + d)) :=
        Finset.sum_le_sum (fun j _ => denseOffsetBits_upper _ C b h d (hwidth _) hb)
      _ = q * (b + 1 + 4 * (h + d)) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hq
  apply (show denseDrawBits R P d e h ≤ denseRandomBitBudget d b h from ?_).trans
    (denseRandomBitBudget_polynomial d b h)
  unfold denseDrawBits denseTrialBits denseRandomBitBudget
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hoff _)

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ReferenceDrawBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform size bounds for the state-dependent dense completion call -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [LinearOrder I] [LinearOrder J] in
lemma reference_dimension_fourteen (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) :
    14 ≤ dimensionAllowance (I := I) (J := J) := by
  have hr : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i₀.val⟩
  have hc : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨j₀.val⟩
  unfold dimensionAllowance
  nlinarith

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileFlatCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flattening the two stored views for coordinate exchanges -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates ProfilePrograms
open IntegerWeightedTransport

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

def sumViewEquiv : (Fin q⊕Fin q) ≃ Cells small×Bool where
  toFun
    | .inl i => (e i,false)
    | .inr i => (e i,true)
  invFun a := if a.2 then .inr (e.symm a.1) else .inl (e.symm a.1)
  left_inv a := by cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true, if_true,Equiv.symm_apply_apply]
  right_inv a := by rcases a with ⟨a,b⟩; cases b <;> simp only [Bool.false_eq_true,ite_false,
    ite_true, if_true,Equiv.apply_symm_apply]

def flatViewEquiv : Fin (q+q) ≃ Cells small×Bool :=
  finSumFinEquiv.symm.trans (sumViewEquiv small e)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperBooleanProposal
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Boolean realization of the small graph proposal law -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts FairBits

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

local notation "d" => dimensionAllowance (I := I) (J := J)

abbrev smallProposalBits : ℕ := Nat.clog 2 (32*d^2)


end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPreparedProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the complete proposal input from binary margin lists -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def marginCatalog (z : List ℕ×List ℕ) : List (ℕ×ℕ) :=
  smallCellCatalog (z,marginThreshold z)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseExponentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of one dense exponent component -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ContingencyTables.ProfilePrograms

def componentValue (z : ComponentData) : ℕ :=
  GridBoundary.componentExponent z.1.1 z.1.2 z.2.1 z.2.2

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseExponentListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing all dense exponent components and their maximum -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ContingencyTables.ProfilePrograms Polynomial
open scoped BigOperators

lemma listMaximum_le (xs : List ℕ) (a M : ℕ) :
    listMaximum (xs,a)≤M ↔ a≤M ∧ ∀ b∈xs,b≤M := by
  induction xs generalizing a with
  | nil => simp [listMaximum]
  | cons b bs ih =>
    simp only [listMaximum,List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [max_le_iff,List.mem_cons]
    constructor
    · rintro ⟨⟨hb,ha⟩,hbs⟩
      refine ⟨ha,?_⟩
      intro c hc
      rcases hc with rfl|hc
      · exact hb
      · exact hbs c hc
    · rintro ⟨ha,hxs⟩
      exact ⟨⟨hxs b (Or.inl rfl),ha⟩,fun c hc => hxs c (Or.inr hc)⟩

lemma le_listMaximum_member (xs : List ℕ) (a b : ℕ) (hb : b∈xs) :
    b≤listMaximum (xs,a) := ((listMaximum_le xs a _).mp le_rfl).2 b hb

def exponentCell (z : ExponentData×(ℕ×ℕ)) : ℕ := componentValue (exponentCellData z)

def exponentCells (z : ExponentData) : List (ℕ×ℕ) := cellPairs z.1.1

def exponentValues (z : ExponentData) : List ℕ :=
  (exponentCells z).map (fun ij => exponentCell (z,ij))

def fullExponent (z : ExponentData) : ℕ := listMaximum (exponentValues z,0)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseExponentListSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The binary list exponent equals the geometric dense exponent -/

namespace ContingencyTables.DensePrograms
open scoped BigOperators Classical
open GridBoundary ProfilePrograms

variable {m n : ℕ}

def exponentDataCode (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (z : Fin m → Fin n → ℕ) : ExponentData :=
  (((marginCode R,marginCode P),matrixCode z),d)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseScaleCellProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary conversion from a grid coordinate to a free integer entry -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open GridBoundary

def gridCellValue (z : ExponentData×(ℕ×ℕ)) : ℕ :=
  gridCellWidth z*matrixEntry (z.1.1.2,z.2)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseScaleMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scaling a binary grid matrix to its integer bin corner -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial GridBoundary

def scaleRows (z : ExponentData) : List ℕ := List.range z.1.1.1.tail.length
def scaleColumns (z : ExponentData) : List ℕ := List.range z.1.1.2.tail.length

def scaleRowEntry (z : (ExponentData×ℕ)×ℕ) : ℕ :=
  gridCellValue (z.1.1,(z.1.2,z.2))

def scaleRow (z : ExponentData×ℕ) : List ℕ :=
  (scaleColumns z.1).map (fun j => scaleRowEntry (z,j))

def scaleMatrix (z : ExponentData) : MatrixCode :=
  (scaleRows z).map (fun i => scaleRow (z,i))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseGridExponentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the dense exponent directly from a binary grid matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary

def scaledData (z : ExponentData) : ExponentData := ((z.1.1,scaleMatrix z),z.2)

def gridExponent (z : ExponentData) : ℕ := fullExponent (scaledData z)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseFlatExponentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluating the dense exponent on the flat coordinate encoding -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary

def flatExponent (z : FlatExponentData) : ℕ := gridExponent (flatToGridData z)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMetropolisProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for a full dense Metropolis step -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev FlatStepData := FlatExponentData×(List Bool×List Bool)

def replaceFlat (z : FlatExponentData×List ℕ) : FlatExponentData :=
  ((z.1.1.1,z.2),z.1.2)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting the actual dense transition word in polynomial time -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

def proposalWidth (z : FlatExponentData×List Bool) : ℕ := Nat.clog 2 (8*z.1.2)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DependentWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting a binary word at input-dependent coordinate widths -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def dependentChunks (z : List ℕ×List Bool) : List (List Bool) :=
  (chunkIndices z).map (fun i => dependentChunk (z,i))

open scoped BigOperators

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionComputedInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initialization from the computed small-cell catalog

The proof-level equivalence follows the actual catalog program. It is
used only to identify the output of the binary list initializer with a
paired transversal and to transfer its distributional error bound.
-/

namespace ContingencyTables.CompanionComputedInitial

open MatchingFPRAS.TreeTyped CompanionFactorialApplication
open InitialTransversals InitialFactorialBits CompanionInitialDraw
open FirstSuccess ResidualMixture TwoLiftStates CommonBasesFPRAS
open CompanionArithmeticProposal
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

def initialDraw (B : ℕ) (bits : Fin (wordLength A B) → Bool) :
    PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool))) :=
  indexEquiv A (transversalDraw (fun s : SmallCell A => A.b s.val.1 s.val.2)
    (cellOrder A) B bits)

end
end ContingencyTables.CompanionComputedInitial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_DegreeCompletion
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Positive completion of a single valid degree

A fixed-degree weight is extended by the constant weight one on every
other degree. All off-degree signatures are proved, and all coefficient
sums at the original degree are unchanged. This lets the existing general
nonnegative-derivative theorem retain contracted coordinates without
assuming positivity or signatures of the original weight at other degrees.
-/

namespace ContingencyTables.DegreeCompletion

open scoped BigOperators Classical Topology
open CommonBasesFPRAS BinaryContraction

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

omit [Fintype Γ] [DecidableEq Γ] in
lemma completeDegree_positive (f : Set Γ → ℝ) (k : ℕ) (hf : DegreePositive f k) :
    ∀ A, 0 < completeDegree f k A := by
  intro A
  unfold completeDegree
  split_ifs with h
  · exact hf A h
  · norm_num

end ContingencyTables.DegreeCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTraceWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Capped trace returns from the actual companion Boolean walk

The return search scans the recorded path after its initial state. Its
reference expectation is the finite Green sum defining the capped trace;
the Boolean walk contributes its path error.
-/

namespace ContingencyTables.CompanionTraceWords

open CommonBasesFPRAS CompanionFactorialApplication CompanionBooleanPhase
open CompanionPhaseTrajectory CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary FirstSuccess ResidualMixture
open scoped BigOperators Classical

noncomputable section

variable {X : Type*}

def firstHit (B : X → Prop) : List X → Option (FiniteChain.Inside B)
  | [] => none
  | x::xs => if hx : B x then some ⟨x,hx⟩ else firstHit B xs

def returnValue (B : X → Prop) (phi : FiniteChain.Inside B → ℝ) (xs : List X) : ℝ :=
  DrawTree.optionValue phi (firstHit B xs.tail)

end
end ContingencyTables.CompanionTraceWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseFinishSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact semantics of the stored phase update -/
namespace ContingencyTables.CompanionPhaseFinishProgram
open MatchingFPRAS CompanionFactorialApplication CompanionTraceProgram CompanionPhaseCounts
open CompanionMultiplierMatrixProgram CompanionMultiplierProgram CompanionOrderedProposal
open CompanionArithmeticProposal CompanionRationalUpdates CommonBasesFPRAS TwoLiftStates
open scoped BigOperators Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p q N : ℕ} (g : Fin p ≃ Labels A) (e : (Labels A×Bool) ≃ Fin q)

/-- The phase result as a function of just the rational query values. -/
def rationalResult (states : Fin N→Set (Labels A×Bool)) (old : CompanionPhaseWords.Stored A)
    (values : List (ℚ×ℚ)) : Option ((Fin p→Fin p→ℚ)×ℚ) :=
  if CountsPositive A (List.ofFn states) then
    some ((fun i j => rationalLearn pairs old.multiplier (List.ofFn states) (pair (g i)) (pair (g j))),
      old.estimate*((∑ i : Fin N,if PlainState pairs (states i) then
        (values.getD i.val (0,0)).2/(values.getD i.val (0,0)).1 else 0)/
          (plainCount A (List.ofFn states):ℚ)))
  else none

end
end ContingencyTables.CompanionPhaseFinishProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCappedReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Total bounded trace steps

If a capped return search misses its target, the finite-word experiment
keeps its starting plain state. Its error against the exact trace is the
cap loss plus the error of the recorded Boolean walk.
-/

namespace ContingencyTables.CompanionCappedReturn

open CommonBasesFPRAS CompanionTraceWords CompanionPhaseTrajectory
open CompanionFactorialApplication CompanionBooleanPhase CompanionOracleDensity
open CompanionWeightOracle CompanionRationalUpdates TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {X : Type*}

def returnDefault (B : X → Prop) (x : FiniteChain.Inside B) (xs : List X) :
    FiniteChain.Inside B := (firstHit B xs.tail).getD x

end
end ContingencyTables.CompanionCappedReturn

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhysicalNormalizer
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual companion normalizer equals the full physical balanced mass -/

namespace ContingencyTables.CompanionPhysicalNormalizer

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication TwoLiftStates
open BalancedCellFibres PhysicalLargeProfiles LargePairEnumeration TreeMarginalSignature
open ForestPenaltyApplication

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def smallProfilesEquiv (A : Instance I J) :
    SmallProfiles (fun a : I×J => A.small a.1 a.2) (cellWidth A) ≃
      TransversalCount.Profile (fun s : SmallCell A => A.b s.val.1 s.val.2) :=
  Equiv.piCongrRight (smallInterval A)

end ContingencyTables.CompanionPhysicalNormalizer

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_TreeFeasibleMass
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every feasible table contributes one unit to its actual cell fibre -/

namespace ContingencyTables.TreeMarginalSignature

open scoped BigOperators Classical
open CompanionFactorialApplication ForestPenaltyApplication ForestLiteralCount
open BalancedCellFibres EqualitySoftening

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def tableAssignment (A : Instance I J) (Y : I → J → ℤ)
    (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j) : Profiles (cellWidth A) := fun a =>
  ⟨(Y a.1 a.2-lower A.T A.d A.b a.1 a.2).toNat,by
    have hlo := lower_nonpositive A a.1 a.2
    have hup := upper_ge_capacity A a.1 a.2
    have hz : 0 ≤ Y a.1 a.2-lower A.T A.d A.b a.1 a.2 := by linarith [(hY a.1 a.2).1]
    have hb : Y a.1 a.2-lower A.T A.d A.b a.1 a.2 ≤ cellWidth A a := by
      dsimp only [cellWidth]
      linarith [(hY a.1 a.2).2]
    have hn : (Y a.1 a.2-lower A.T A.d A.b a.1 a.2).toNat ≤ cellWidth A a := by
      exact_mod_cast (show ((Y a.1 a.2-lower A.T A.d A.b a.1 a.2).toNat:ℤ) ≤ cellWidth A a by
        rw [Int.toNat_of_nonneg hz]
        exact hb)
    omega⟩

end ContingencyTables.TreeMarginalSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhysicalTables
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Feasible physical balanced profiles are exactly bounded contingency tables -/

namespace ContingencyTables.CompanionPhysicalTables

open scoped BigOperators Classical
open CompanionFactorialApplication TreeMarginalSignature BalancedCellFibres

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def physicalTable (A : Instance I J) (a : Profiles (cellWidth A)) : I → J → ℤ :=
  fun i j => ForestLiteralCount.lower A.T A.d A.b i j+(a (i,j)).val

def Feasible (A : Instance I J) (a : Profiles (cellWidth A)) : Prop :=
  (∀ i j,0 ≤ physicalTable A a i j ∧ physicalTable A a i j ≤ A.b i j) ∧
    (∀ i,(∑ j,physicalTable A a i j)=A.r i) ∧
    (∀ j,(∑ i,physicalTable A a i j)=A.c j)

abbrev PhysicalTables (A : Instance I J) := {a : Profiles (cellWidth A) // Feasible A a}

lemma physicalTable_assignment (A : Instance I J) (Y : I → J → ℤ)
    (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j) :
    physicalTable A (tableAssignment A Y hY)=Y := by
  funext i j
  have hz : 0 ≤ Y i j-ForestLiteralCount.lower A.T A.d A.b i j := by
    linarith [(hY i j).1,lower_nonpositive A i j]
  simp only [physicalTable,tableAssignment,Int.toNat_of_nonneg hz]
  ring

noncomputable def toBounded (A : Instance I J) (a : PhysicalTables A) :
    BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b := by
  let Y : I → J → ℕ := fun i j => (physicalTable A a.val i j).toNat
  have hy (i : I) (j : J) : (Y i j:ℤ)=physicalTable A a.val i j :=
    Int.toNat_of_nonneg (a.property.1 i j).1
  refine ⟨⟨Y,⟨?_,?_⟩⟩,?_⟩
  · intro i
    have hh : (∑ j,(Y i j:ℤ))=((A.r i).toNat:ℤ) := by
      simp_rw [hy]
      rw [a.property.2.1 i,Int.toNat_of_nonneg (row_nonnegative A i)]
    exact_mod_cast hh
  · intro j
    have hh : (∑ i,(Y i j:ℤ))=((A.c j).toNat:ℤ) := by
      simp_rw [hy]
      rw [a.property.2.2 j,Int.toNat_of_nonneg (column_nonnegative A j)]
    exact_mod_cast hh
  · intro i j
    have hh : (Y i j:ℤ) ≤ A.b i j := by rw [hy]; exact (a.property.1 i j).2
    exact_mod_cast hh

noncomputable def fromBounded (A : Instance I J)
    (X : BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b) : PhysicalTables A := by
  let Y : I → J → ℤ := fun i j => X.val.val i j
  have hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j := by
    intro i j
    dsimp only [Y]
    exact ⟨Nat.cast_nonneg _,by exact_mod_cast X.property i j⟩
  refine ⟨tableAssignment A Y hY,?_⟩
  unfold Feasible
  rw [physicalTable_assignment]
  refine ⟨hY,?_,?_⟩
  · intro i
    have hh : (∑ j,Y i j)=((A.r i).toNat:ℤ) := by
      dsimp only [Y]
      exact_mod_cast X.val.property.1 i
    rwa [Int.toNat_of_nonneg (row_nonnegative A i)] at hh
  · intro j
    have hh : (∑ i,Y i j)=((A.c j).toNat:ℤ) := by
      dsimp only [Y]
      exact_mod_cast X.val.property.2 j
    rwa [Int.toNat_of_nonneg (column_nonnegative A j)] at hh

lemma toBounded_integer (A : Instance I J) (a : PhysicalTables A) (i : I) (j : J) :
    ((toBounded A a).val.val i j:ℤ)=physicalTable A a.val i j := by
  change ((physicalTable A a.val i j).toNat:ℤ)=physicalTable A a.val i j
  exact Int.toNat_of_nonneg (a.property.1 i j).1

lemma fromBounded_table (A : Instance I J)
    (X : BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b) :
    physicalTable A (fromBounded A X).val=fun i j => (X.val.val i j:ℤ) := by
  unfold fromBounded
  exact physicalTable_assignment _ _ _

lemma physicalTable_injective (A : Instance I J) : Function.Injective (physicalTable A) := by
  intro a a' hh
  funext t
  apply Fin.ext
  have he := congrFun (congrFun hh t.1) t.2
  simp only [physicalTable] at he
  exact_mod_cast (add_left_cancel he)

/-- The terminal feasible-profile count is the original bounded-table
count, with the instance's necessarily nonnegative margins. -/
noncomputable def tablesEquiv (A : Instance I J) :
    PhysicalTables A ≃ BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b where
  toFun := toBounded A
  invFun := fromBounded A
  left_inv a := by
    apply Subtype.ext
    apply physicalTable_injective A
    funext i j
    rw [fromBounded_table]
    exact toBounded_integer A a i j
  right_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    have hh := toBounded_integer A (fromBounded A X) i j
    rw [fromBounded_table] at hh
    dsimp only at hh
    exact_mod_cast hh

end ContingencyTables.CompanionPhysicalTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTerminalRegions
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal infeasible physical profiles lie in the terminal far or near regions -/

namespace ContingencyTables.CompanionTerminalRegions

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionPhysicalTables
open CompanionNearMass ForestPenaltyApplication TreeMarginalSignature BalancedCellFibres
open EqualitySoftening

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def integerDeviation (A : Instance I J) (a : Profiles (cellWidth A)) : I⊕J → ℤ :=
  Sum.elim (fun i => (∑ j,physicalTable A a i j)-A.r i)
    (fun j => (∑ i,physicalTable A a i j)-A.c j)

end ContingencyTables.CompanionTerminalRegions

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCanonicalHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical multiplier entries determine the projected phase history

The extension uses only the first label of a raw coordinate pair. Its values
away from canonical pairs need not match the original multiplier.
-/
namespace ContingencyTables.CompanionCanonicalHistory
open CompanionFactorialApplication CompanionRationalUpdates CompanionMultiplierAgreement
open CommonBasesFPRAS TwoLiftStates GridBoundary
open CompanionPhaseWords (Stored )
open scoped Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)

def project (s : Stored A) : Canonical (p := p) :=
  CompanionPhaseFinishProgram.storedView A g s

def extend (s : Canonical (p := p)) : Stored A :=
  ⟨(fun a b => s.1 (g.symm a.1.1) (g.symm b.1.1)),s.2⟩

@[simp] theorem project_extend (s : Canonical (p := p)) :
    project A g (extend A g s)=s := by
  apply Prod.ext
  · funext i j
    simp only [project,extend,CompanionPhaseFinishProgram.storedView,pair,Equiv.symm_apply_apply]
  · rfl

end
end ContingencyTables.CompanionCanonicalHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCanonicalHistoryLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete source estimator factors through canonical stored entries -/
namespace ContingencyTables.CompanionCanonicalHistory
open CompanionFactorialApplication CommonBasesFPRAS GridBoundary FiniteObservableTransport
open CompanionPhaseWords (Stored)
open scoped Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)

def canonicalLookup (history : List (Canonical (p := p))) : ℕ→Canonical (p := p)
  | 0 => project A g (RootedStoredEstimate.initialStored A)
  | i+1 => history.getD i (project A g (RootedStoredEstimate.initialStored A))

end
end ContingencyTables.CompanionCanonicalHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the initial canonical multiplier matrix -/

namespace ContingencyTables.CompanionInitialMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped CompanionMultiplierMatrixProgram

def denominatorRealizer : Realizer denominator :=
  composition (f := fun z : Metadata × Metadata => (z.2.2,2))
    (g := fun p : ℕ × ℕ => p.1+p.2)
    (pair (composition second second) (constant 2)) add
end ContingencyTables.CompanionInitialMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseOffsetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary quotient offsets and the resulting free matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary

abbrev OffsetData := ExponentData×List (List Bool)

def offsetBits (z : OffsetData×(ℕ×ℕ)) : List Bool :=
  z.1.2.getD (z.2.1*z.1.1.1.1.2.tail.length+z.2.2) []

def offsetFreeEntry (z : OffsetData×(ℕ×ℕ)) : ℕ :=
  gridCellValue (z.1.1,z.2)+scaledWordValue (gridCellWidth (z.1.1,z.2),offsetBits z)

def offsetRowEntry (z : (OffsetData×ℕ)×ℕ) : ℕ :=
  offsetFreeEntry (z.1.1,(z.1.2,z.2))

def offsetRow (z : OffsetData×ℕ) : List ℕ :=
  (scaleColumns z.1.1).map (fun j => offsetRowEntry (z,j))

def offsetMatrix (z : OffsetData) : MatrixCode :=
  (scaleRows z.1).map (fun i => offsetRow (z,i))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit scalar schedules for the adaptive counting phases

Every precision and sample length below is a rational or natural arithmetic
expression. In particular the dyadic exponents use a polynomial reciprocal
allowance, so no real logarithm is evaluated by the algorithm.
-/

namespace ContingencyTables.CountingPhaseSchedule

open scoped BigOperators

def observations (p W H : ℕ) (eta : ℚ) : ℕ :=
  ⌈(1024:ℚ)*(H+1)*observationCoefficient p W/eta^2⌉₊+1

end ContingencyTables.CountingPhaseSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCountingSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit constant-confidence schedule for the actual counting words -/

namespace ContingencyTables.RootedCountingSchedule

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedPhaseHistory
open CompanionTargetMixing (restartTime)
open CompanionTerminalMass (Endpoints tableCount)
open CompanionTerminalApplication (finalPhase)
open CountingPhaseSchedule GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

/-- Only natural/rational arithmetic selects the phase precision and
all finite loops. The supplied grid point is the evaluator's fixed start. -/
def settings (A : Instance I J) (C K H L : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (epsilon : ℚ)
    (v : Grid (I := Fin (dimension A)) K) : Settings A :=
  let p := Fintype.card (Labels A)
  let tau := restartTime A H L
  let eta := tolerance H epsilon
  let N := observations p A.W H eta
  let n := returnCap p H tau
  let k := precision H tau N n eta
  ⟨C,K,H,L,k,n,N,initialPrecision H,hK,hW,noise H tau N n eta,v⟩

end
end ContingencyTables.RootedCountingSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingTerminalSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the terminal coefficient without real logarithms

The source's ceiling of log₂(1/epsilon) is exactly the natural ceiling
logarithm of ceil(1/epsilon). All terminal metadata can therefore be
computed with natural and rational arithmetic.
-/

namespace ContingencyTables.CountingTerminalSchedule

open CompanionFactorialApplication CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

/-- The full product allowance is computed from the input capacities'
binary lengths, rather than supplied as a counting hypothesis. -/
def capacityBits (A : Instance I J) : ℕ :=
  ∑ a : I×J,(A.b a.1 a.2+1).size

end
end ContingencyTables.CountingTerminalSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OffsetCountProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact binary tabulation of the bounded offset law -/

namespace ContingencyTables.OffsetCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma ceilQuotient_eq (n d : ℕ) (hd : 0<d) :
    ceilQuotient (n,d)=⌈(n:ℚ)/d⌉₊ := by
  change n ⌈/⌉ d=⌈(n:ℚ)/d⌉₊
  have hdq : (0:ℚ)<d := by exact_mod_cast hd
  apply le_antisymm
  · rw [ceilDiv_le_iff_le_mul hd]
    have hh:=Nat.le_ceil ((n:ℚ)/d)
    have hn : n≤⌈(n:ℚ)/d⌉₊*d := by exact_mod_cast (div_le_iff₀ hdq).mp hh
    simpa only [Nat.mul_comm] using hn
  · rw [Nat.ceil_le,div_le_iff₀ hdq]
    have hn : n≤d*(n ⌈/⌉ d) := by
      simpa only [smul_eq_mul] using (le_smul_ceilDiv (b := n) hd)
    have hn' : n≤(n ⌈/⌉ d)*d := by simpa only [Nat.mul_comm] using hn
    exact_mod_cast hn'

def endpoint (z : Input) : ℕ := ceilQuotient (z.2*z.1.2,z.1.1)

def offsetCount (z : Input) : ℕ := endpoint (z.1,z.2+1)-endpoint z

lemma endpoint_eq (M Q β : ℕ) (hM : 0<M) :
    endpoint ((M,Q),β)=FairBits.endpoint M Q β := by
  rw [endpoint,ceilQuotient_eq _ _ hM]
  simp only [FairBits.endpoint,Nat.cast_mul]

/-- Only two ceiling divisions are required, regardless of the number of
random words whose probability is being counted. -/
theorem offsetCount_eq (M Q β : ℕ) (hM : 0<M) (hQ : 0<Q) (hβ : β<M) :
    offsetCount ((M,Q),β)=(FairBits.fiber M Q β).card := by
  rw [FairBits.fiber_card hM hQ hβ,offsetCount,endpoint_eq _ _ _ hM,endpoint_eq _ _ _ hM]

theorem scaledLaw_mass (M k : ℕ) (hM : 0<M) (β : Fin M) :
    (FairBits.scaledLaw M k hM).mass β=
      (offsetCount ((M,2^k),β.val):ℚ)/(2:ℚ)^k := by
  rw [offsetCount_eq _ _ _ hM (by positivity) β.isLt]
  simp only [FairBits.scaledLaw,FairBits.outputMass,Nat.cast_pow,Nat.cast_ofNat]

end ContingencyTables.OffsetCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingOracleScheduleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary arithmetic for the counting oracle sample schedule -/

namespace ContingencyTables.CountingOracleScheduleProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

def naturalRealizer : Realizer natural := pair identity (constant 1)
def offsetBaseRealizer : Realizer offsetBase :=
  composition (f := fun z : OffsetInput => 4096*z.1) (g := natural)
    (composition (f := fun z : OffsetInput => (4096,z.1)) (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair (constant 4096) first) multiply) naturalRealizer
def timeBaseRealizer : Realizer timeBase :=
  composition (f := fun z : TimeInput => z.1.1*z.1.2) (g := natural)
    (composition first multiply) naturalRealizer
def timeNumeratorRealizer : Realizer timeNumerator :=
  composition (f := fun z : TimeInput => 16*z.1.1) (g := natural)
    (composition (f := fun z : TimeInput => (16,z.1.1)) (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair (constant 16) (composition first first)) multiply) naturalRealizer

end ContingencyTables.CountingOracleScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScalarScheduleProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed arithmetic circuits for the scalar counting schedules

These circuits only read a fixed finite list and perform binary addition
and multiplication. Their syntax describes the fixed program, not a
numeric loop selected by the input.
-/

namespace ContingencyTables.ScalarScheduleProgram
open MatchingFPRAS.TreeTyped

def vector (es : List Expr) (xs : List ℕ) : List ℕ := es.map (fun e => e.eval xs)


end ContingencyTables.ScalarScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseScalarProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed arithmetic circuits for the phase scalar controls -/

namespace ContingencyTables.CountingPhaseScalarProgram
open ScalarScheduleProgram
open MatchingFPRAS.TreeTyped

def capacityBits : Expr := .input 6

def restartTime : Expr := 4*observable*(h+p+capacityBits+5)
def returnCap : Expr := 65536*(h+1)^2*(tau+1)*(p^2+1)

end ContingencyTables.CountingPhaseScalarProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedDemandProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing the oracle demand by the current encoded paired state

Only the retained-cell catalog and the supplied state are scanned. The
large cells receive zero in each sparse view and hence retain their full
capacity in the complemented column demand.
-/

namespace ContingencyTables.PairedDemandProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def sideEntryRealizer : Realizer sideEntry :=
  choose first (composition second second) (composition second first)
end ContingencyTables.PairedDemandProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerPropagation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer propagation tabulates adaptive finite laws without random tapes -/

namespace ContingencyTables.IntegerPropagation
open ResidualMixture FirstSuccess
open scoped BigOperators Classical

variable {A : Type*} [Fintype A] [DecidableEq A]
variable (B : A → A → ℕ) (Q : ℕ)

lemma numerators_total (hrow : ∀ x,∑ y,B x y=Q) (start : A) (n : ℕ) :
    ∑ y,numerators B start n y=Q^n := by
  induction n with
  | zero => simp [numerators]
  | succ n ih =>
    simp only [numerators]
    rw [Finset.sum_comm]
    simp_rw [←Finset.mul_sum,hrow]
    rw [←Finset.sum_mul,ih,pow_succ]

/-- One row of a dyadic transition table, viewed as an exact rational law. -/
def kernel (hQ : 0<Q) (hrow : ∀ x,∑ y,B x y=Q) (x : A) : RationalLaw A where
  mass y := (B x y:ℚ)/Q
  nonnegative y := by positivity
  total := by
    rw [←Finset.sum_div,←Nat.cast_sum,hrow]
    exact div_self (by exact_mod_cast hQ.ne')

/-- Matrix/vector propagation accounts for all adaptive paths with one
integer per state; its denominator exponent grows only with the steps. -/
theorem numerators_walkLaw (hQ : 0<Q) (hrow : ∀ x,∑ y,B x y=Q)
    (start : A) (n : ℕ) (y : A) :
    (numerators B start n y:ℚ)/(Q:ℚ)^n=(walkLaw (kernel B Q hQ hrow) start n).mass y := by
  induction n generalizing y with
  | zero => simp [numerators,walkLaw,pointLaw]
  | succ n ih =>
    simp only [numerators,Nat.cast_sum,Nat.cast_mul,walkLaw,bindLaw,kernel,pow_succ]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    rw [←ih x]
    exact (div_mul_div_comm _ _ _ _).symm

end ContingencyTables.IntegerPropagation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_DyadicRootBisection
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer implementation of the correction-root bisection

The two interval endpoints share one dyadic denominator. Every comparison
is an inequality between natural powers and products. This is the literal
integer algorithm to which the rational correction analysis is applied.
-/

namespace ContingencyTables.DyadicRootBisection

open MatchingFPRAS

def value (z : State) : ℚ×ℚ := ((z.1.1:ℚ)/z.2,(z.1.2:ℚ)/z.2)

def advance (c : TreeFraction.Fraction) (s : ℕ) (z : State) : State :=
  if (z.1.1+z.1.2)^s*c.2 ≤ c.1*(2*z.2)^s
  then ((z.1.1+z.1.2,2*z.1.2),2*z.2)
  else ((2*z.1.1,z.1.1+z.1.2),2*z.2)

def run (c : TreeFraction.Fraction) (s : ℕ) : ℕ→State
  | 0=>((0,8),1)
  | n+1=>advance c s (run c s n)

def output (c : TreeFraction.Fraction) (s n : ℕ) : TreeFraction.Fraction :=
  let z:=run c s n
  TreeFraction.normalize (z.1.1+z.1.2,2*z.2)

end ContingencyTables.DyadicRootBisection

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DyadicRootProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the rational correction bisection

The root degree is the length of a supplied allowance list. One fixed
depth list controls the outer loop. Thus both natural-power evaluation
and the bisection loop have polynomial cost in the supplied binary data
and the two explicit allowances.
-/

namespace ContingencyTables.DyadicRootProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def height (z : DyadicRootBisection.State) : ℕ := max (max z.1.1.size z.1.2.size) z.2.size

end ContingencyTables.DyadicRootProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingLabelCountProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the actual number of factorial labels

Only retained capacities are summed; the program does not expand any
capacity into a list of labels to obtain the phase controls.
-/

namespace ContingencyTables.CountingLabelCountProgram
open MatchingFPRAS.TreeTyped

abbrev Input := RootedForestCatalog.Data

def catalogInput (z : Input) : CompanionCellCatalog.Input := ((z.1.2,z.2),z.1.1.2)

def capacities (z : Input) : List ℕ := CompanionCellCatalog.capacities (catalogInput z)

def count (z : Input) : ℕ := (capacities z).sum

open CompanionFactorialApplication
open scoped BigOperators Classical

end ContingencyTables.CountingLabelCountProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TableTightening
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous tightening and translation by attained cell minima

The hypotheses here are exactly the extremum properties proved for the
executed searches. The maps preserve all tables, with explicit inverse
addition and with both endpoints of every translated interval attained.
-/

namespace ContingencyTables.TableTightening

open scoped BigOperators

variable {m n : ℕ}

lemma add_subtract (X l : Fin m→Fin n→ℕ) (hl : ∀ i j,l i j≤X i j) :
    add (subtract X l) l=X := by
  funext i j
  exact Nat.sub_add_cancel (hl i j)

lemma subtract_add (Y l : Fin m→Fin n→ℕ) : subtract (add Y l) l=Y := by
  funext i j
  exact Nat.add_sub_cancel _ _

lemma add_margins (Y l : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (hr : ∀ i,(∑ j,l i j) ≤ r i) (hc : ∀ j,(∑ i,l i j) ≤ c j)
    (hm : HasMargins Y (rows r l) (columns c l)) : HasMargins (add Y l) r c := by
  constructor
  · intro i
    simpa only [add,Finset.sum_add_distrib,hm.1 i,rows] using Nat.sub_add_cancel (hr i)
  · intro j
    simpa only [add,Finset.sum_add_distrib,hm.2 j,columns] using Nat.sub_add_cancel (hc j)

variable (r : Fin m→ℕ) (c : Fin n→ℕ) (b l u : Fin m→Fin n→ℕ)

theorem add_feasible (hne : ∃ X,Feasible r c b X)
    (hl : ∀ X,Feasible r c b X→∀ i j,l i j≤X i j)
    (hu : ∀ i j,u i j≤b i j)
    {Y : Fin m→Fin n→ℕ} (hY : TightFeasible r c l u Y) :
    Feasible r c b (add Y l) := by
  obtain ⟨X,hX⟩ := hne
  have hs := lower_sums X l r c hX.1 (hl X hX)
  refine ⟨add_margins Y l r c hs.1 hs.2 hY.1,?_⟩
  intro i j
  have hlo := (hl X hX i j).trans (hX.2 i j)
  have hbound := hY.2 i j
  change Y i j≤u i j-l i j at hbound
  change Y i j+l i j≤b i j
  have hup := hu i j
  omega

end ContingencyTables.TableTightening

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_WeightedArgmaxProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary scan selecting a greatest weighted edge

The accumulator is either empty or one stored edge. Its binary size is
bounded by the input list size even when capacities are numerically large.
-/

namespace ContingencyTables.WeightedArgmaxProgram

open MatchingFPRAS.TreeTyped Polynomial

def compareInput (z : Edge×Edge) : ℕ×ℕ := (z.2.2,z.1.2)
def compareRealizer : Realizer compareInput :=
  pair (composition second second) (composition first second)

end ContingencyTables.WeightedArgmaxProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingCoefficientProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The terminal coefficient computed with binary natural arithmetic -/

namespace ContingencyTables.CountingCoefficientProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial
open OffsetCountPrograms DensePrograms

abbrev Input := (ℕ×ℕ)×Fraction

def precision (e : Fraction) : ℕ := Nat.clog 2 (ceilQuotient (e.2,e.1))

def allowance (z : Input) : ℕ := 20*(z.1.1+z.1.2+precision z.2+1)

def numerator (z : Input) : ℕ := 2048*z.1.2*(allowance z)^2*z.2.2

def coefficient (z : Input) : ℕ := ceilQuotient (numerator z,z.2.1)

end ContingencyTables.CountingCoefficientProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBaseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the capacity-bit and dimension inputs to the counting schedule -/

namespace ContingencyTables.CountingBaseProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
open NetworkVertexCode

abbrev Input := NetworkVertexCode.Input × TreeFraction.Fraction

def dimension (z : NetworkVertexCode.Input) : ℕ := 1+z.1.1.length*z.1.2.length

def half (e : TreeFraction.Fraction) : TreeFraction.Fraction := (e.1,2*e.2)
def halfRealizer : Realizer half :=
  pair first (composition (f := fun e : TreeFraction.Fraction => (2,e.2))
    (g := fun p : ℕ×ℕ => p.1*p.2) (pair (constant 2) second) multiply)

end ContingencyTables.CountingBaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingTerminalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed terminal grid width, cutoff and phase count -/

namespace ContingencyTables.CountingTerminalProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Input := CountingBaseProgram.Input

end ContingencyTables.CountingTerminalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingComputedSettings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every scalar control from the original bounded table -/

namespace ContingencyTables.CountingComputedSettings
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CountingPhaseScalarProgram

abbrev Input := CountingBaseProgram.Input
abbrev Parameters := CountingPhaseParametersProgram.Input

def fullReturnCap : Expr := 65536*(h+1)^2*(restartTime+1)*(p^2+1)
def controlExpressions : List Expr := [p,w,h,restartTime,0,fullReturnCap,capacityBits]

def fillObservations (z : Parameters) : Parameters :=
  (z.1.take 4++(CountingPhaseParametersProgram.observations z::z.1.drop 5),z.2)

open CompanionFactorialApplication
open scoped Classical

end ContingencyTables.CountingComputedSettings

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPreparedState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the immutable rooted state from the public bounded input -/

namespace ContingencyTables.CountingPreparedState
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
abbrev Input := CountingBaseProgram.Input

open CompanionFactorialApplication ForestAssignmentSplit
open scoped Classical

end ContingencyTables.CountingPreparedState

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionRepetitionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the confidence repetition count on a rational input -/
namespace ContingencyTables.FractionRepetitionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

def count (x : TreeFraction.Fraction) : ℕ := 64*((TreeFraction.normalize x).2.bits.length+1)
end ContingencyTables.FractionRepetitionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAdaptiveInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-input preparation for a positive-label counting run -/
namespace ContingencyTables.CountingAdaptiveInputProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Input := CountingBaseProgram.Input×List Bool
abbrev Prepared := CompanionRestartInitializer.Prepared
abbrev Stored := CompanionPhaseFinishProgram.Stored
abbrev Output := Prepared×Stored

end ContingencyTables.CountingAdaptiveInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Codec
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralCodec
open TreeTyped TreeData TreeFunction

def ratWord (x : TreeFraction.Fraction) : List Symbol := 4::natWord x.1++natWord x.2
end MatchingFPRAS.LiteralCodec

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingInputParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the public cell-bounded counting input

Dimensions only delimit bounded list slices. The matrix layout uses the
lengths of the parsed margin lists, so malformed headers do not create
unbounded numeric loops. Positive rational parameters use their natural
numerator and denominator, exactly as in the public tape encoding.
-/

namespace ContingencyTables.CountingInputParser
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralParse
open MatchingFPRAS.TreeFraction DensePrograms

abbrev Input := NetworkVertexCode.Input × (Fraction × Fraction)

def capacityFrame (ns : List ℕ) : GridFlatData :=
  ((0::(GreedyFeasibleTable.marginLists ns).1,0::(GreedyFeasibleTable.marginLists ns).2),
    (rest ns).take (cells ns))

def fractionPair (ns : List ℕ) : Fraction × Fraction :=
  ((ns.headD 0,ns.tail.headD 1),(ns.tail.tail.headD 0,ns.tail.tail.tail.headD 1))

def decode (ns : List ℕ) : Input :=
  ((GreedyFeasibleTable.marginLists ns,unflattenGrid (capacityFrame ns)),fractionPair (parameters ns))

def parseInput (as : List Symbol) : Input := decode (parse as)

end ContingencyTables.CountingInputParser

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionOutputProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical nonnegative rational output on the public tape -/

namespace ContingencyTables.FractionOutputProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralCodec

def output (x : TreeFraction.Fraction) : List Symbol := ratWord (TreeFraction.normalize x)

end ContingencyTables.FractionOutputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingScheduleSizes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial numeric bounds for the explicit counting schedules -/

namespace ContingencyTables.CountingPhaseSchedule

def observationBound (p W H E : ℕ) : ℕ :=
  1024*(H+1)*observationCoefficient p W*(800*(H+1)*E)^2+2

end ContingencyTables.CountingPhaseSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScalarScheduleBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numeric bounds for the fixed arithmetic circuits -/

namespace ContingencyTables.ScalarScheduleProgram
open Polynomial
noncomputable section

def Expr.bound : Expr → Polynomial ℕ
  | .input _ => X
  | .number n => C n
  | .plus a b => a.bound+b.bound
  | .times a b => a.bound*b.bound

end
end ContingencyTables.ScalarScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingControlBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial bounds for the observation and precision controls -/

namespace ContingencyTables.CountingControlBounds
open ScalarScheduleProgram CountingPhaseSchedule Polynomial
noncomputable section

def observationPolynomial : Polynomial ℕ :=
  CountingPhaseScalarProgram.observationNumerator.bound*(1600*(X+1)*X)^2+2
def returnPolynomial : Polynomial ℕ := CountingPhaseScalarProgram.returnCap.bound
def largePolynomial : Polynomial ℕ := X+observationPolynomial+returnPolynomial+1
def precisionPolynomial : Polynomial ℕ :=
  CountingPhaseScalarProgram.precisionBase.bound.comp largePolynomial+1600*(X+1)*X

end
end ContingencyTables.CountingControlBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPublicTerminalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public polynomial bounds for the terminal grid and phase controls -/

namespace ContingencyTables.CountingPublicTerminalBounds
open CountingTerminalBounds CountingPublicInputBounds CompanionFactorialApplication
open ScalarScheduleProgram Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

def restartPolynomial : Polynomial ℕ := CountingPhaseScalarProgram.restartTime.bound.comp basicPolynomial

end
end ContingencyTables.CountingPublicTerminalBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPublicControls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All dynamic scalar controls are polynomial in the public input -/

namespace ContingencyTables.CountingPublicControls
open CountingPublicInputBounds CountingPublicTerminalBounds CountingControlBounds
open CompanionFactorialApplication Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

def inputPolynomial : Polynomial ℕ := basicPolynomial+restartPolynomial+X
def observationPolynomial : Polynomial ℕ := CountingControlBounds.observationPolynomial.comp inputPolynomial
def returnPolynomial : Polynomial ℕ := CountingControlBounds.returnPolynomial.comp inputPolynomial
def precisionPolynomial : Polynomial ℕ := CountingControlBounds.precisionPolynomial.comp inputPolynomial

end
end ContingencyTables.CountingPublicControls

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPublicWordBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete counting word is polynomial in the original input -/

namespace ContingencyTables.CountingPublicWordBound
open CompanionFactorialApplication CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

def controlPolynomial : Polynomial ℕ :=
  CountingPublicControls.inputPolynomial+CountingPublicControls.observationPolynomial+
    CountingPublicControls.returnPolynomial+CountingPublicControls.precisionPolynomial+
    CountingTerminalBounds.gridPolynomial+2048*(CountingTerminalBounds.phasePolynomial+1)+X+1

end
end ContingencyTables.CountingPublicWordBound

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingDirectWordBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public word budget for the direct zero-label estimator -/
namespace ContingencyTables.CountingDirectWordBound
open CompanionFactorialApplication CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

def controlPolynomial : Polynomial ℕ := CountingPublicWordBound.controlPolynomial+4*X
def wordPolynomial : Polynomial ℕ := CountingOracleWordBounds.medianPolynomial.comp controlPolynomial

end
end ContingencyTables.CountingDirectWordBound

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingDirectBudgetBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public runtime allowance for the direct branch's padded random word -/
namespace ContingencyTables.CountingDirectBudgetBound
open Polynomial CountingPublicInputBounds
open scoped Classical
noncomputable section
variable {m n : ℕ}

def budgetPolynomial : Polynomial ℕ := CountingDirectWordBound.wordPolynomial+
  CountingMarkerBounds.paddingPolynomial.comp CountingDirectWordBound.controlPolynomial

end
end ContingencyTables.CountingDirectBudgetBound

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBranchBudgetBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the computed counting branches' public word budgets -/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section

def budgetPolynomial (positivePolynomial : Polynomial ℕ) : Polynomial ℕ :=
  CountingDirectBudgetBound.budgetPolynomial+positivePolynomial

end
end ContingencyTables.CountingBranchProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCompletionTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial exact acceptance test for a free integer matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

def completionNonnegative (z : CompletionCell) : Bool :=
  decide ((completionParts z).2≤(completionParts z).1)

def completionValid (z : CompletionData) : Bool :=
  (cellPairs z.1).all (fun ij => completionNonnegative (z,ij))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCompletedMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary construction of the completed integer matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def completedEntry (z : CompletionCell) : ℕ := (completionParts z).1-(completionParts z).2

def completionRows (z : CompletionData) : List ℕ := List.range z.1.1.length
def completionColumns (z : CompletionData) : List ℕ := List.range z.1.2.length

def completedRowEntry (z : (CompletionData×ℕ)×ℕ) : ℕ := completedEntry (z.1.1,(z.1.2,z.2))

def completedRow (z : CompletionData×ℕ) : List ℕ :=
  (completionColumns z.1).map (fun j => completedRowEntry (z,j))

def completedMatrix (z : CompletionData) : MatrixCode :=
  (completionRows z).map (fun i => completedRow (z,i))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete dense trial as a polynomial binary program -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

def acceptCompletion (z : CompletionData) : Option MatrixCode :=
  if completionValid z then some (completedMatrix z) else none

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseDrawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded dense draw as a single polynomial binary program -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

def drawChunks (z : DenseDrawData) : List (List Bool) :=
  wordChunks (trialWidth z.1.1,z.2)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete trial program uses the manuscript's finite-bit experiment -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits
open scoped BigOperators Classical

noncomputable section

def trialInput {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (h : ℕ) (a : Grid (I := Fin (m*n)) (4*d^8)) (bits : List Bool) : DenseTrialData :=
  (((((marginCode R,marginCode P),gridNatCode a),d),h),bits)

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MaximalListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing a maximal margin in binary -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

lemma listMaximum_mem_or_default (xs : List ℕ) (a : ℕ) :
    listMaximum (xs,a)=a ∨ listMaximum (xs,a)∈xs := by
  induction xs generalizing a with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    change listMaximum (bs,max b a)=a ∨ listMaximum (bs,max b a)∈b::bs
    rcases ih (max b a) with he|hm
    · rw [he]
      rcases le_total b a with h|h
      · exact Or.inl (max_eq_right h)
      · exact Or.inr (by simp [max_eq_left h])
    · exact Or.inr (List.mem_cons_of_mem b hm)

lemma listMaximum_mem (xs : List ℕ) (hx : xs≠[]) : listMaximum (xs,0)∈xs := by
  cases xs with
  | nil => exact (hx rfl).elim
  | cons a xs =>
    change listMaximum (xs,max a 0)∈a::xs
    rw [Nat.max_zero]
    rcases listMaximum_mem_or_default xs a with he|hm
    · simp [he]
    · exact List.mem_cons_of_mem a hm

theorem maximumIndex_lt (xs : List ℕ) (hx : xs≠[]) : maximumIndex xs < xs.length :=
  List.idxOf_lt_length_iff.mpr (listMaximum_mem xs hx)

theorem maximumIndex_value (xs : List ℕ) (hx : xs≠[]) :
    xs.getD (maximumIndex xs) 0=listMaximum (xs,0) := by
  rw [List.getD_eq_getElem xs 0 (maximumIndex_lt xs hx)]
  exact List.getElem_idxOf (maximumIndex_lt xs hx)

theorem maximumIndex_maximal (xs : List ℕ) (hx : xs≠[]) (a : ℕ) (ha : a∈xs) :
    a≤xs.getD (maximumIndex xs) 0 := by
  rw [maximumIndex_value xs hx]
  exact le_listMaximum_member xs 0 a ha

def maximumPosition {n : ℕ} (f : Fin (n+1) → ℕ) : Fin (n+1) :=
  ⟨maximumIndex (List.ofFn f),by
    simpa only [List.length_ofFn] using maximumIndex_lt (List.ofFn f)
      (by intro h; have := congrArg List.length h; simp only [List.length_ofFn,List.length_nil] at this; omega)⟩

theorem maximumPosition_spec {n : ℕ} (f : Fin (n+1) → ℕ) (i : Fin (n+1)) :
    f i≤f (maximumPosition f) := by
  have hx : List.ofFn f≠[] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_ofFn,List.length_nil] at this
    omega
  have hm := maximumIndex_maximal (List.ofFn f) hx (f i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have he : (List.ofFn f).getD (maximumIndex (List.ofFn f)) 0=f (maximumPosition f) := by
    rw [List.getD_eq_getElem (List.ofFn f) 0 (maximumIndex_lt (List.ofFn f) hx),List.getElem_ofFn]
    rfl
  rwa [he] at hm

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseNormalizeSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Correctness of computed maximal-margin normalization -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

def marginPosition {m : ℕ} (R : Option (Fin m) → ℕ) : Fin (m+1) :=
  maximumPosition (fun i => R (finSuccEquiv m i))

def normalizedMargin {m : ℕ} (R : Option (Fin m) → ℕ) : Option (Fin m) → ℕ :=
  fun i => R (indexPermutation (marginPosition R) i)

lemma normalizedMargin_max {m : ℕ} (R : Option (Fin m) → ℕ) (i : Fin m) :
    normalizedMargin R (some i)≤normalizedMargin R none := by
  unfold normalizedMargin indexPermutation
  simp only [Equiv.trans_apply,finSuccEquiv_symm_none,Equiv.swap_apply_left]
  exact maximumPosition_spec (fun i => R (finSuccEquiv m i)) _

lemma normalizedMargin_lower {m : ℕ} (R : Option (Fin m) → ℕ) (L : ℕ)
    (hR : ∀ i,L≤R i) : ∀ i,L≤normalizedMargin R i := fun _ => hR _

lemma normalizedMargin_total {m : ℕ} (R : Option (Fin m) → ℕ) :
    ∑ i,normalizedMargin R i=∑ i,R i := (indexPermutation (marginPosition R)).sum_comp R

def normalizedDrawBits {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d h : ℕ) : ℕ := denseDrawBits (normalizedMargin R) (normalizedMargin P) d finProdFinEquiv h

theorem normalizedDrawBits_polynomial {m n : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ) (d C b h : ℕ)
    (hq : m*n≤d) (hR : ∀ i,R i≤C) (hb : Nat.clog 2 (C+2)≤b) :
    normalizedDrawBits R P d h≤25*(d+b+h+1)^62 := by
  apply denseDrawBits_polynomial (normalizedMargin R) (normalizedMargin P) d C b h
    finProdFinEquiv hq
  · intro p
    exact (Nat.div_le_self _ _).trans ((min_le_left _ _).trans (hR _))
  · exact hb

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCanonicalSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Correctness of dense sampling with computed initialization -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

def canonicalOrigin (q d : ℕ) (hd : 0 < d) : Grid (I := Fin q) (4*d^8) :=
  fun _ => ⟨0,le_rfl,by
    have hp : 1≤4*d^8 := by
      have := one_le_pow₀ (n := 8) (Nat.succ_le_iff.mpr hd)
      omega
    have hz : (1:ℤ)≤(4*d^8:ℕ) := by exact_mod_cast hp
    omega⟩

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargeMarginProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the large rectangle and its padded margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma mem_largeIndices (U : ℕ) (r : List ℕ) (i : ℕ) :
    i∈largeIndices (U,r) ↔ i < r.length ∧ U ≤ r.getD i 0 := by
  simp only [largeIndices,List.mem_filter,List.mem_range,largeIndexTest,decide_eq_true_eq]

lemma largeIndices_nodup (U : ℕ) (r : List ℕ) : (largeIndices (U,r)).Nodup :=
  (List.nodup_range (n := r.length)).filter _

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargeMarginSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact indexing of the computed large residual margins -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms PaddedCompletions SmallContextCoordinates SmallContextFibres
open CompletionCounts
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ}

lemma largeIndices_ofFn_mem (r : Fin m → ℕ) (U : ℕ) (i : Fin m) :
    i.val∈largeIndices (U,List.ofFn r) ↔ U ≤ r i := by
  rw [mem_largeIndices]
  simp only [List.length_ofFn,i.isLt,true_and,List.getD_eq_getElem?_getD,
    List.getElem?_ofFn,dite_true,Option.getD_some,Fin.eta]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_TranslationDecisionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary arithmetic for the completion translation test -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms CompletionTranslation
open scoped BigOperators

abbrev TranslationData := (MarginPair×MarginPair)×MatrixCode

def starParts (z : MarginPair×(ℕ×ℕ)) : ℕ×ℕ :=
  completionParts ((z.1,[]),z.2)

def translationParts (z : TranslationCell) : ℕ×ℕ :=
  let old := starParts (z.1.1,z.2)
  let new := starParts (z.1.2,z.2)
  (new.1+old.2,new.2+old.1)

def translatedCell (z : TranslationData×(ℕ×ℕ)) : Bool :=
  let p := translationParts (z.1.1,z.2)
  decide (p.2 ≤ matrixEntry (z.1.2,z.2)+p.1)

def translationValid (z : TranslationData) : Bool :=
  (cellPairs z.1.1).all (fun ij => translatedCell (z,ij))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPositiveProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One executed positive-label counting run

The supplied word is partitioned into equally padded phase words. The phase
count only truncates a supplied list, so malformed scalar inputs do
not create an unbounded loop.
-/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev Prepared := CompanionPhaseContextProgram.Prepared

end ContingencyTables.CountingPositiveProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RepeatedFractionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent repetition of a finite-word rational program

The public confidence amplification only groups bits already supplied
on the tape. Its binary count cannot cause an unbounded allocation.
-/

namespace ContingencyTables.RepeatedFractionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

variable {X : Type} [Codec X]

def words (z : Input X) : List (List Bool) :=
  (wordChunks (z.1.2.2,z.2)).take z.1.2.1

variable {f : X×List Bool→TreeFraction.Fraction}

def sample (f : X×List Bool→TreeFraction.Fraction) (z : Input X×List Bool) : TreeFraction.Fraction :=
  f (z.1.1.1,z.2)

def samples (f : X×List Bool→TreeFraction.Fraction) (z : Input X) : List TreeFraction.Fraction :=
  (words z).map (fun bits => sample f (z,bits))

attribute [local irreducible] samples

def output (f : X×List Bool→TreeFraction.Fraction) (z : Input X) : TreeFraction.Fraction :=
  MedianFractionProgram.median (samples f z)

open GridBoundary CommonBasesFPRAS

end ContingencyTables.RepeatedFractionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPositiveWordBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public polynomial bounds for the executed positive counting words -/
namespace ContingencyTables.CountingPositiveWordBound
open MatchingFPRAS MatchingFPRAS.TreeTyped CompanionFactorialApplication CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

def measurePolynomial : Polynomial ℕ := 13*CountingPublicWordBound.controlPolynomial+1
def singlePolynomial : Polynomial ℕ :=
  CountingPublicWordBound.controlPolynomial*(widthPolynomial.comp measurePolynomial)
def amplifiedPolynomial : Polynomial ℕ := CountingAmplifiedProgram.budgetPolynomial singlePolynomial

end
end ContingencyTables.CountingPositiveWordBound

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteAcceptCounts
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer transition counts without enumerating acceptance bits -/

namespace ContingencyTables.FiniteAcceptCounts
open ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]

lemma offCount_mass (a b : α) (proposal : β → Option α) (gap : α → ℕ) (K : ℕ)
    (hba : b≠a) :
    (offCount a proposal gap K b:ℚ)/denominator (β := β) K =
      (finiteAcceptLaw a proposal (fun b => FairBits.acceptDyadic (gap b) K)).mass b := by
  rw [finiteAcceptLaw_off_diagonal a b proposal _ hba.symm]
  rw [Finset.filter_congr_decidable (Finset.univ : Finset (Fin (2^K)))
    (FairBits.acceptDyadic (gap b) K) (fun _ => Classical.propDecidable _)]
  rw [FairBits.acceptDyadic_count]
  simp only [offCount,ite_eq_right hba,denominator,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_ofNat,Fintype.card_fin]
  exact (div_mul_div_comm
    ((Finset.univ.filter (fun z => proposal z=some b)).card:ℚ)
    (Fintype.card β) (2^(K-gap b)) (2^K)).symm

lemma offCount_sum_le (a : α) (proposal : β → Option α) (gap : α → ℕ) (K : ℕ) :
    (∑ b,offCount a proposal gap K b) ≤ denominator (β := β) K := by
  let p:=finiteAcceptLaw a proposal (fun b => FairBits.acceptDyadic (gap b) K)
  have hQ : (0:ℚ)<denominator (β := β) K := by exact_mod_cast denominator_pos (β := β) K
  have hb (b : α) : (offCount a proposal gap K b:ℚ)/denominator (β := β) K ≤ p.mass b := by
    by_cases hba : b=a
    · subst b
      simpa only [offCount,ite_true, if_true,Nat.cast_zero,zero_div] using p.nonnegative a
    · exact (offCount_mass a b proposal gap K hba).le
  have hs:=Finset.sum_le_sum (fun b (_ : b∈Finset.univ) => hb b)
  rw [←Finset.sum_div,←Nat.cast_sum,p.total] at hs
  exact_mod_cast (div_le_one hQ).mp hs

lemma row_total (a : α) (proposal : β → Option α) (gap : α → ℕ) (K : ℕ) :
    ∑ b,row a proposal gap K b=denominator (β := β) K := by
  simp only [row,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  exact Nat.add_sub_of_le (offCount_sum_le a proposal gap K)

end
end ContingencyTables.FiniteAcceptCounts

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTransitionCounts
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact integer tabulation of the implemented dense bin walk -/

namespace ContingencyTables.GridBoundary
open ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseTransitionCount (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a b : Grid (I := Fin q) (4*d^8)) : ℕ :=
  FiniteAcceptCounts.row a (fun z : Fin (2^Nat.clog 2 (8*d)) => axisCodeStep a z)
    (fun b => denseExponent R P d e b-denseExponent R P d e a) (8*d^5) b

omit [DecidableEq I] [DecidableEq J] in
lemma denseTransitionCount_total (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4*d^8)) :
    ∑ b,denseTransitionCount R P d e a b=2^denseStepBits d := by
  have h:=FiniteAcceptCounts.row_total a
    (fun z : Fin (2^Nat.clog 2 (8*d)) => axisCodeStep a z)
    (fun b => denseExponent R P d e b-denseExponent R P d e a) (8*d^5)
  simpa only [denseTransitionCount,FiniteAcceptCounts.denominator,Fintype.card_fin,
    denseStepBits,pow_add] using h

omit [DecidableEq I] [DecidableEq J] in
/-- The tabulated integer matrix is the actual Boolean step law, including
all unused proposal codes and all rejections. -/
theorem denseTransitionCount_kernel (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4*d^8)) :
    IntegerPropagation.kernel (denseTransitionCount R P d e) (2^denseStepBits d)
      (by positivity) (denseTransitionCount_total R P d e) a =
        denseBitStepLaw R P d e a := by
  rw [denseBitStepLaw_eq_finite]
  apply RationalLaw.eq_of_off_diagonal _ _ a
  intro b hba
  change (denseTransitionCount R P d e a b:ℚ)/((2^denseStepBits d:ℕ):ℚ)=_
  have h:=FiniteAcceptCounts.offCount_mass a b
    (fun z : Fin (2^Nat.clog 2 (8*d)) => axisCodeStep a z)
    (fun b => denseExponent R P d e b-denseExponent R P d e a) (8*d^5) hba
  simpa only [denseTransitionCount,FiniteAcceptCounts.row,ite_eq_right hba,add_zero,
    FiniteAcceptCounts.denominator,Fintype.card_fin,denseStepBits,pow_add,Nat.cast_mul,
    Nat.cast_pow,Nat.cast_ofNat,finiteDenseStepLaw] using h

omit [DecidableEq I] [DecidableEq J] in
/-- Matrix propagation tabulates the complete adaptive bin walk with
one integer per bin; the precision affects integer lengths, not the
number of bins enumerated. -/
theorem denseWalkCount_mass (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a b : Grid (I := Fin q) (4*d^8)) (N : ℕ) :
    (IntegerPropagation.numerators (denseTransitionCount R P d e) a N b:ℚ) /
      (2:ℚ)^(N*denseStepBits d) = (denseBooleanWalkLaw R P d e a N).mass b := by
  have h:=IntegerPropagation.numerators_walkLaw (denseTransitionCount R P d e)
    (2^denseStepBits d) (by positivity) (denseTransitionCount_total R P d e) a N b
  have he : denseBooleanWalkLaw R P d e a N=
      walkLaw (denseBitStepLaw R P d e) a N := by
    unfold denseBooleanWalkLaw denseBooleanWalk
    rw [←FairBits.map_equiv (gridWordEquiv N (denseStepBits d)),FairBits.uniform_equiv]
    exact wordWalkLaw_eq _ _ _
  rw [he]
  have hk : IntegerPropagation.kernel (denseTransitionCount R P d e) (2^denseStepBits d)
      (by positivity) (denseTransitionCount_total R P d e)=denseBitStepLaw R P d e :=
    funext (denseTransitionCount_kernel R P d e)
  rw [hk] at h
  simpa only [Nat.cast_pow,Nat.cast_ofNat,←pow_mul,Nat.mul_comm (denseStepBits d) N] using h

end
end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerLaw
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer counts for the finite stages of law tabulation -/

namespace ContingencyTables
open scoped BigOperators

namespace IntegerLaw
open ResidualMixture FirstSuccess
open scoped Classical
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B] {Q P : ℕ}

def toRational (p : IntegerLaw A Q) (hQ : 0<Q) : RationalLaw A where
  mass a := (p.count a:ℚ)/Q
  nonnegative _ := by positivity
  total := by
    rw [←Finset.sum_div,←Nat.cast_sum,p.total]
    exact div_self (by exact_mod_cast hQ.ne')

def ofMass (p : RationalLaw A) (w : A → ℕ) (hQ : 0<Q)
    (hw : ∀ a,(w a:ℚ)/Q=p.mass a) : IntegerLaw A Q where
  count := w
  total := by
    have ht : ((∑ a,w a:ℕ):ℚ)/Q=1 := by
      rw [Nat.cast_sum,Finset.sum_div]
      simp_rw [hw]
      exact p.total
    have hQt : (Q:ℚ)≠0 := by exact_mod_cast hQ.ne'
    exact_mod_cast (div_eq_one_iff_eq hQt).mp ht

lemma toRational_ofMass (p : RationalLaw A) (w : A → ℕ) (hQ : 0<Q)
    (hw : ∀ a,(w a:ℚ)/Q=p.mass a) :
    (ofMass p w hQ hw).toRational hQ=p := by
  apply RationalLaw.ext
  exact funext hw

lemma toRational_rebase (p : IntegerLaw A Q) (h : Q=P) (hQ : 0<Q) (hP : 0<P) :
    (p.rebase h).toRational hP=p.toRational hQ := by subst P; rfl

theorem toRational_scale (p : IntegerLaw A Q) (hQ : 0<Q) (P : ℕ) (hP : 0<P) :
    (p.scale P).toRational (Nat.mul_pos hQ hP)=p.toRational hQ := by
  apply RationalLaw.ext
  funext a
  change ((p.count a*P:ℕ):ℚ)/((Q*P:ℕ):ℚ)=(p.count a:ℚ)/Q
  push_cast
  exact mul_div_mul_right _ _ (by exact_mod_cast hP.ne' : (P:ℚ)≠0)

theorem toRational_product (p : IntegerLaw A Q) (q : IntegerLaw B P)
    (hQ : 0<Q) (hP : 0<P) :
    (p.product q).toRational (Nat.mul_pos hQ hP)=
      productLaw (p.toRational hQ) (q.toRational hP) := by
  apply RationalLaw.ext
  funext x
  change ((p.count x.1*q.count x.2:ℕ):ℚ)/((Q*P:ℕ):ℚ)=
    (p.count x.1:ℚ)/Q*((q.count x.2:ℚ)/P)
  push_cast
  exact (div_mul_div_comm (p.count x.1:ℚ) Q (q.count x.2) P).symm

theorem toRational_push [DecidableEq B] (p : IntegerLaw A Q) (hQ : 0<Q) (f : A → B) :
    (p.push f).toRational hQ=mapLaw (p.toRational hQ) f := by
  apply RationalLaw.ext
  funext b
  change ((∑ a,if f a=b then p.count a else 0:ℕ):ℚ)/Q=
    ∑ a,if f a=b then (p.count a:ℚ)/Q else 0
  rw [Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

variable [DecidableEq A]

/-- First-success sums are evaluated in integers with a reserved common
denominator. No division by the acceptance probability occurs. -/
theorem toRational_retry (p : IntegerLaw (Option A) Q) (hQ : 0<Q)
    (fallback : A) (N : ℕ) :
    (p.retry fallback N).toRational (pow_pos hQ N)=
      retryLaw (p.toRational hQ) id fallback N := by
  apply RationalLaw.ext
  funext a
  induction N with
  | zero => simp [retry,toRational,retryCount,retryLaw,pointLaw]
  | succ N ih =>
    rw [retryLaw,retryStep_mass]
    simp only [successMass,failureMass,id_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
    simp only [retry,toRational,retryCount,Nat.cast_add,Nat.cast_mul,Nat.cast_pow] at ih ⊢
    rw [←ih]
    rw [pow_succ]
    field_simp [show (Q:ℚ)≠0 by exact_mod_cast hQ.ne']

end
end IntegerLaw
end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseIntegerLaw
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer tables for the actual dense completion draw -/

namespace ContingencyTables.GridBoundary
open ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical
noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseWalkCounts (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4*d^8)) (N : ℕ) :
    IntegerLaw (Grid (I := Fin q) (4*d^8)) (2^(N*denseStepBits d)) :=
  IntegerLaw.ofMass (denseBooleanWalkLaw R P d e a N)
    (IntegerPropagation.numerators (denseTransitionCount R P d e) a N)
    (by positivity) (fun b => by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using denseWalkCount_mass R P d e a b N)

omit [DecidableEq I] [DecidableEq J] in
lemma denseWalkCounts_law (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4*d^8)) (N : ℕ) :
    (denseWalkCounts R P d e a N).toRational (by positivity)=denseBooleanWalkLaw R P d e a N :=
  IntegerLaw.toRational_ofMass _ _ _ _

def offsetExponent (e : I × J ≃ Fin q) (w : I × J → ℕ) (h d : ℕ) : ℕ :=
  ∑ j : Fin q,offsetBitLength (w (e.symm j)) h d

def offsetCounts (e : I × J ≃ Fin q) (w : I × J → ℕ) (hw : ∀ p,0<w p) (h d : ℕ) :
    IntegerLaw (Offset w) (2^offsetExponent e w h d) :=
  IntegerLaw.ofMass (boundedOffsetLaw e w hw h d)
    (fun o => ∏ j : Fin q,OffsetCountPrograms.offsetCount
      ((w (e.symm j),2^offsetBitLength (w (e.symm j)) h d),
        ((offsetCoordinateEquiv e w).symm o j).val)) (by positivity) (by
      intro o
      change ((∏ j : Fin q,OffsetCountPrograms.offsetCount
        ((w (e.symm j),2^offsetBitLength (w (e.symm j)) h d),
          ((offsetCoordinateEquiv e w).symm o j).val):ℕ):ℚ)/
          (2^offsetExponent e w h d:ℕ)=
        ∏ j : Fin q,(scaledLaw (w (e.symm j)) (offsetBitLength (w (e.symm j)) h d)
          (hw _)).mass ((offsetCoordinateEquiv e w).symm o j)
      simp_rw [OffsetCountPrograms.scaledLaw_mass]
      rw [Finset.prod_div_distrib,←Nat.cast_prod]
      simp only [Nat.cast_pow,Nat.cast_ofNat,offsetExponent,Finset.prod_pow_eq_pow_sum])

lemma offsetCounts_law (e : I × J ≃ Fin q) (w : I × J → ℕ) (hw : ∀ p,0<w p) (h d : ℕ) :
    (offsetCounts e w hw h d).toRational (by positivity)=boundedOffsetLaw e w hw h d :=
  IntegerLaw.toRational_ofMass _ _ _ _

def denseTrialCounts (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I × J ≃ Fin q) (h : ℕ) (a : Grid (I := Fin q) (4*d^8)) :
    IntegerLaw (DenseTrial R P d q) (2^denseTrialBits R P d e h) :=
  ((denseWalkCounts R P d e a (d^50*(h+1)^2)).product
    (offsetCounts e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d)).rebase
      (by rw [←pow_add]; rfl)

lemma denseBooleanTrial_product (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I × J ≃ Fin q) (h : ℕ) (a : Grid (I := Fin q) (4*d^8)) :
    mapLaw (uniformLaw (α := Fin (denseTrialBits R P d e h) → Bool))
      (denseBooleanTrial R P d hd hR hP e h a)=
    productLaw (denseBooleanWalkLaw R P d e a (d^50*(h+1)^2))
      (boundedOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d) := by
  unfold denseBooleanTrial
  rw [←map_equiv (trialWordEquiv R P d e h)
    (uniformLaw (α := Fin (denseTrialBits R P d e h) → Bool))
    (fun z => (denseBooleanWalk R P d e a (d^50*(h+1)^2) z.1,
      drawOffsetWords e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d z.2)),
    uniform_equiv,←uniform_product,mapLaw_product,drawOffsetWordsLaw_eq]
  rfl

theorem denseTrialCounts_law (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I × J ≃ Fin q) (h : ℕ) (a : Grid (I := Fin q) (4*d^8)) :
    (denseTrialCounts R P d hd hR hP e h a).toRational (by positivity)=
    mapLaw (uniformLaw (α := Fin (denseTrialBits R P d e h) → Bool))
      (denseBooleanTrial R P d hd hR hP e h a) := by
  rw [denseTrialCounts,IntegerLaw.toRational_rebase,IntegerLaw.toRational_product,
    denseWalkCounts_law,offsetCounts_law,denseBooleanTrial_product] <;> positivity

def denseDrawCounts (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin q) (4*d^8)) (fallback : Table R P) :
    IntegerLaw (Table R P) (2^denseDrawBits R P d e h) :=
  (((denseTrialCounts R P d hd hR hP e h a).push (trialSuccess R P d e htotal)).retry
    fallback (d^4*(h+1))).rebase (by rw [←pow_mul,Nat.mul_comm]; rfl)

/-- Full first-success dense completion counts agree with the implemented
Boolean draw. Bin states and offset tuples are the only spaces summed. -/
theorem denseDrawCounts_law (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin q) (4*d^8)) (fallback : Table R P) :
    (denseDrawCounts R P d hd hR hP e htotal h a fallback).toRational (by positivity)=
      denseBooleanDrawLaw R P d hd hR hP e htotal h a fallback := by
  rw [denseDrawCounts,IntegerLaw.toRational_rebase,IntegerLaw.toRational_retry,
    IntegerLaw.toRational_push,denseTrialCounts_law,retryLaw_map,retryLaw_map]
  simp only [id_eq]
  change _ = mapLaw
    (uniformLaw (α := Fin ((d^4*(h+1))*denseTrialBits R P d e h) → Bool))
    (fun bits => wordRetry
      (fun word => trialSuccess R P d e htotal (denseBooleanTrial R P d hd hR hP e h a word))
      fallback (d^4*(h+1)) (gridWordEquiv (d^4*(h+1)) (denseTrialBits R P d e h) bits))
  rw [←map_equiv (gridWordEquiv (d^4*(h+1)) (denseTrialBits R P d e h)),uniform_equiv]
  exact (wordRetryLaw_eq _ _ _).symm
  all_goals positivity

end
end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTableCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the unique bin and offset of an accepted table -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary ProfilePrograms
open scoped BigOperators Classical

def tableFreeValue (z : ExponentData×(ℕ×ℕ)) : ℕ :=
  matrixEntry (z.1.1.2,(z.2.1+1,z.2.2+1))

def tableBinCoordinate (z : ExponentData×(ℕ×ℕ)) : ℕ := tableFreeValue z/gridCellWidth z

def tableOffsetCoordinate (z : ExponentData×(ℕ×ℕ)) : ℕ := tableFreeValue z%gridCellWidth z

def tableFreeCells (z : ExponentData) : List (ℕ×ℕ) := freeCells (z,0)

def tableBinCoordinates (z : ExponentData) : List ℕ :=
  (tableFreeCells z).map (fun ij => tableBinCoordinate (z,ij))

def tableOffsetCoordinates (z : ExponentData) : List ℕ :=
  (tableFreeCells z).map (fun ij => tableOffsetCoordinate (z,ij))

def tableWidths (z : ExponentData) : List ℕ :=
  (tableFreeCells z).map (fun ij => gridCellWidth (z,ij))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_AxisProposalTest
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Testing dense adjacency by the polynomial list of signed directions -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary

def axisNumberStep (z : AxisNumberData) : Option (List ℕ) :=
  axisListStep ((z.1,z.2/2),decide (z.2%2=1))

def proposalMatches (z : ProposalTestData×ℕ) : Bool :=
  (axisNumberStep (z.1.1,z.2)).elim false (fun xs => NatListEquality.listEqual (xs,z.1.2))

def hasProposal (z : ProposalTestData) : Bool :=
  (proposalIndices z).any (fun i => proposalMatches (z,i))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCountProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable dense off-diagonal counts without acceptance-word enumeration -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped Classical

abbrev CountInput := FlatExponentData×List ℕ

def countProposalInput (z : CountInput) : ProposalTestData :=
  ((4*z.1.2^8,z.1.1.2),z.2)

def countPowerInput (z : CountInput) : ℕ×ℕ :=
  (2,8*z.1.2^5-(flatExponent (replaceFlat (z.1,z.2))-flatExponent z.1))

def offCountCode (z : CountInput) : ℕ :=
  if hasProposal (countProposalInput z) then BinaryPowerPrograms.power (countPowerInput z) else 0

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PreparedDenseCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial transition entries with a shared acceptance allowance -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

abbrev PreparedCountInput := List Bool×CountInput

def preparedGap (z : PreparedCountInput) : ℕ :=
  flatExponent (replaceFlat z.2)-flatExponent z.2.1

def preparedOffCount (z : PreparedCountInput) : ℕ :=
  if hasProposal (countProposalInput z.2) then
    BoundedPowerPrograms.power (z.1,preparedGap z) else 0

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the actual dense transition matrix from its finite states -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

/-- Shared unary allowance and binary denominator, current exponent data,
and the enumeration of all states. -/
abbrev CountRowData := ((List Bool×ℕ)×FlatExponentData)×List (List ℕ)

def rowOffEntry (z : CountRowData×List ℕ) : ℕ :=
  preparedOffCount (z.1.1.1.1,(z.1.1.2,z.2))

def rowOffCounts (z : CountRowData) : List ℕ := z.2.map (fun b => rowOffEntry (z,b))

def rowEntry (z : CountRowData×List ℕ) : ℕ :=
  if NatListEquality.listEqual (z.1.1.2.1.2,z.2) then
    z.1.1.1.2-(rowOffCounts z.1).sum else rowOffEntry z

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial assembly of the dense count matrix in column order -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

def countMatrixEntryInput (z : (CountMatrixData×List ℕ)×List ℕ) : CountRowData×List ℕ :=
  ((((z.1.1.1.1,((z.1.1.1.2.1,z.2),z.1.1.1.2.2)),z.1.1.2)),z.1.2)

def countMatrixEntry (z : (CountMatrixData×List ℕ)×List ℕ) : ℕ :=
  rowEntry (countMatrixEntryInput z)

def countColumn (z : CountMatrixData×List ℕ) : List ℕ :=
  z.1.2.map (fun a => countMatrixEntry (z,a))

def countMatrix (z : CountMatrixData) : List (List ℕ) :=
  z.2.map (fun b => countColumn (z,b))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary matrix propagation of the implemented dense walk -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

def matrixWalkInput (z : MatrixWalkData) : ℕ×(List (List ℕ)×List ℕ) :=
  (z.1.1.length,(countMatrix z.1.2,initialVector (z.1.2.2,z.2)))

def matrixWalk (z : MatrixWalkData) : List ℕ :=
  IntegerMatrixPrograms.iterate (matrixWalkInput z)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteGridWords
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit finite-box state enumeration, independent of sampling precision -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators

def clippedGridPower (z : GridEnumerationData×ℕ) : ℕ :=
  BinaryPowerPrograms.power (clippedGridPowerInput z)

def gridCoordinate (z : GridCoordinateData) : ℕ :=
  z.1.2 / clippedGridPower (z.1.1,z.2) % z.1.1.2

def gridCoordinates (z : GridEnumerationData×ℕ) : List ℕ :=
  (gridCoordinateIndices z).map (fun i => gridCoordinate (z,i))

def gridStateCount (z : GridEnumerationData) : ℕ :=
  clippedGridPower (z,z.1.length)

def gridWords (z : GridEnumerationData) : List (List ℕ) :=
  (List.range (gridStateCount z)).map (fun i => gridCoordinates (z,i))

def gridEnumeration (q K : ℕ) : Fin (K^q) ≃ Grid (I := Fin q) K :=
  finFunctionFinEquiv.symm.trans (Equiv.piCongrRight (fun _ => gridDigitEquiv K))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseEnumeratedMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every state of the dense transition table -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators

def enumeratedMatrixInput (z : EnumeratedMatrixInput) : CountMatrixData :=
  (z.1,gridWords (enumerationData z))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseWalkTabulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical dense-walk tabulation from binary margins and precision -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

abbrev TabulationData := CanonicalParameters

def tabulationDimension (z : TabulationData) : ℕ :=
  z.1.1.tail.length*z.1.2.tail.length

def tabulationSteps (z : TabulationData) : ℕ := z.2.1^50*(z.2.2+1)^2

def tabulationAllowance (z : TabulationData) : ℕ := 8*z.2.1^5

def tabulationDenominatorInput (z : TabulationData) : ℕ×ℕ :=
  (2,denseStepBits z.2.1)

def tabulationDenominator (z : TabulationData) : ℕ :=
  BinaryPowerPrograms.power (tabulationDenominatorInput z)

def tabulationDimensions (z : TabulationData) : List Bool :=
  (zeroGrid z.1).map (fun _ => false)

def tabulationCountInput (z : TabulationData) : EnumeratedMatrixInput :=
  ((((unaryMarkers (tabulationAllowance z),tabulationDenominator z),
      (z.1,z.2.1))),tabulationDimensions z)

def tabulationInput (z : TabulationData) : MatrixWalkData :=
  ((unaryMarkers (tabulationSteps z),enumeratedMatrixInput (tabulationCountInput z)),zeroGrid z.1)

def tabulateDenseWalk (z : TabulationData) : List ℕ := matrixWalk (tabulationInput z)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridIndexProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary indexing into the explicitly enumerated grid -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators

def gridIndexTerm (z : GridIndexData×ℕ) : ℕ :=
  z.1.1.getD z.2 0*clippedGridPower (gridIndexPowerInput z)

def gridIndex (z : GridIndexData) : ℕ :=
  ((gridIndexIndices z).map (fun i => gridIndexTerm (z,i))).sum

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PreparedOffsetCount
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary evaluation of the offset numerator product -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary FairBits
open scoped BigOperators

def preparedOffsetInput (z : PreparedOffsetData×ℕ) : OffsetCountPrograms.Input :=
  ((z.1.1.1.2.getD z.2 0,
    BoundedPowerPrograms.power (z.1.1.1.1,
      z.1.1.1.1.length-z.1.1.2.getD z.2 0)),z.1.2.getD z.2 0)

def preparedOffsetFactor (z : PreparedOffsetData×ℕ) : ℕ :=
  OffsetCountPrograms.offsetCount (preparedOffsetInput z)

def preparedOffsetProduct (z : PreparedOffsetData) : ℕ :=
  ((preparedOffsetIndices z).map (fun i => preparedOffsetFactor (z,i))).prod

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialCountProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing one accepted-table numerator from the cached bin vector -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

/-- Cached walk vector, shared bit allowance, and the table/margin data
with the requested precision. -/
abbrev TrialCountData := (List ℕ×List Bool)×OffsetWidthData

def trialCountIndexInput (z : TrialCountData) : GridIndexData :=
  (tableBinCoordinates z.2.1,4*z.2.1.2^8)

def trialCountOffsetInput (z : TrialCountData) : PreparedOffsetData :=
  (((z.1.2,tableWidths z.2.1),offsetLengths z.2),tableOffsetCoordinates z.2.1)

def trialTableCount (z : TrialCountData) : ℕ :=
  z.1.1.getD (gridIndex (trialCountIndexInput z)) 0*
    preparedOffsetProduct (trialCountOffsetInput z)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CompletionEnumerationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit free-box enumeration with binary completion tests -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms
open scoped BigOperators Classical

def completionEnumerationData (z : CompletionMargins) : GridEnumerationData :=
  ((zeroGrid z).map (fun _ => false),z.1.sum+1)

def completionCandidate (z : CompletionMargins×List ℕ) : Option MatrixCode :=
  acceptCompletion (z.1,unflattenGrid z)

/-- Rejected candidates remain as `none`, allowing later integer sums
to ignore them without adding a second enumeration or an ordering oracle. -/
def completionCandidates (z : CompletionMargins) : List (Option MatrixCode) :=
  (gridWords (completionEnumerationData z)).map (fun v => completionCandidate (z,v))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCandidateCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact accepted counts throughout the enumerated completion box -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

abbrev TrialCountContext := (List ℕ×List Bool)×CanonicalParameters

def candidateCountInput (z : TrialCountContext×MatrixCode) : TrialCountData :=
  (z.1.1,(((z.1.2.1,z.2),z.1.2.2.1),z.1.2.2.2))

def candidateCount (z : TrialCountContext×Option MatrixCode) : ℕ :=
  z.2.elim 0 (fun X => trialTableCount (candidateCountInput (z.1,X)))

def candidateCounts (z : TrialCountContext) : List ℕ :=
  (completionCandidates z.2.1).map (fun o => candidateCount (z,o))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_OnlineComposition
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream StackComposition

variable {K Λ Λ' σ α : Type} {Γ : K → Type} [DecidableEq K]
namespace Executes
lemma relabel {M : Λ → TM2.Stmt Γ Λ σ} {coin : CoinTM1.Coins Λ}
    {out : α → TM2.Cfg Γ Λ σ} {c : TM2.Cfg Γ Λ σ} {p : Experiment α}
    (h : Executes M coin out c p) (N : Λ' → TM2.Stmt Γ Λ' σ)
    (co : CoinTM1.Coins Λ') (f : Λ → Λ') (halt : Option Λ')
    (hN : ∀ l,N (f l)=StackComposition.relabel f halt (M l))
    (hco : ∀ l,co (f l)=(coin l).map (fun g=>f ∘ g)) :
    Executes N co (fun a=>mapCfg f halt (out a)) (mapCfg f halt c) p := by
  induction h with
  | done a => exact .done a
  | read l v S g p hg rest ih =>
    apply Executes.read (f l) v S (f ∘ g) p
    · rw [hco,hg]; rfl
    · exact ih
  | step l v S p hs rest ih =>
    apply Executes.step (f l) v S p
    · rw [hco,hs]; rfl
    · rw [hN,StackComposition.relabel_eval]
      exact ih

lemma of_run (M : Λ → TM2.Stmt Γ Λ σ) (n : ℕ) (c : TM2.Cfg Γ Λ σ)
    (v : σ) (S : ∀ k,List (Γ k)) (he : MachineCost.run (TM2.step M) n c=⟨none,v,S⟩) :
    ∃ p : Experiment Unit,Executes M (fun _=>none) (fun _ : Unit=>⟨none,v,S⟩) c p ∧
      (∀ f : Unit → ℚ,p.mean f=f ()) ∧ p.cost≤n := by
  induction n generalizing c with
  | zero => cases he; exact ⟨.done (),.done (),fun _=>rfl,le_rfl⟩
  | succ n ih =>
    rcases c with ⟨l,v',S'⟩
    cases l with
    | none =>
      rw [StackComposition.run_halted] at he
      cases he
      exact ⟨.done (),.done (),fun _=>rfl,Nat.zero_le _⟩
    | some l =>
      obtain ⟨p,hp,hm,hc⟩:=ih (TM2.stepAux (M l) v' S') he
      exact ⟨.delay 1 p,.step l v' S' p rfl hp,hm,by simpa [Experiment.cost,Nat.add_comm] using Nat.succ_le_succ hc⟩
end Executes
end MatchingFPRAS.OnlineStack

namespace MatchingFPRAS.OnlineProc
open Turing MachineCost PhysicalStream OnlineStack RegisterProc

variable {K : Type} [DecidableEq K]

structure Proc (K : Type) extends RegisterProc.Proc K where
  coin : CoinTM1.Coins Label

def deterministic (P : RegisterProc.Proc K) : Proc K := ⟨P,fun _=>none⟩
def seq (P Q : Proc K) : Proc K where
  toProc := RegisterProc.seq P.toProc Q.toProc
  coin := fun l=>match l with
    | .inl l => (P.coin l).map (fun f b=>Sum.inl (f b))
    | .inr l => (Q.coin l).map (fun f b=>Sum.inr (f b))

end MatchingFPRAS.OnlineProc

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_OnlineTree
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open Turing MachineCost PhysicalStream OnlineStack TreeData TreeMachine TreeFunction TreeTyped

abbrev StoreCfg (P : OnlineProc.Proc (K Reg)) := TM2.Cfg (fun _ : K Reg=>Bool) P.Label RegisterProc.Store
variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def chooseProgram (P Q : OnlineProc.Proc (K Reg)) : OnlineProc.Proc (K Reg) where
  toProc := {
    Label := Unit ⊕ (P.Label ⊕ Q.Label)
    entry := ⟨.inl ()⟩
    code := fun l=>match l with
      | .inl _ => .halt
      | .inr (.inl l) => StackComposition.relabel (fun u=>Sum.inr (Sum.inl u)) none (P.code l)
      | .inr (.inr l) => StackComposition.relabel (fun u=>Sum.inr (Sum.inr u)) none (Q.code l) }
  coin := fun l=>match l with
    | .inl _ => some (fun b=>if b then .inr (.inr default) else .inr (.inl default))
    | .inr (.inl l) => (P.coin l).map (fun f b=>.inr (.inl (f b)))
    | .inr (.inr l) => (Q.coin l).map (fun f b=>.inr (.inr (f b)))

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreePostRealization
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreePost
open TreeTyped TreeData TreeFunction TreeMachine RegisterProc Turing Polynomial

abbrev Alphabet := TM2to1.Γ' (K Reg) (fun _=>Bool)
end MatchingFPRAS.TreePost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Packed
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreeFunction TreeMachine TreePost

abbrev Row := K Reg→Option Bool
def baseRow : Row
  | .inl _ => some false
  | .inr _ => none
def bitRow (b : Bool) : Row := fun k=>if k=Sum.inl 0 then some b else none
def bottom : Alphabet := (true,baseRow)
def letter (b : Bool) : Alphabet := (false,bitRow b)

noncomputable def block (a : Alphabet) : List Symbol :=
  (FixedEncoding.enc Alphabet a).toList.map BoolPostCompiler.up
noncomputable def header : List Symbol := block bottom
noncomputable def width : ℕ := Fintype.card Alphabet
end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_LiteralProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public binary input and output for typed finite programs

Literal packing is independent of the counting algorithm. Its cost includes every packing, execution, and printing step.
-/

namespace ContingencyTables.LiteralProgram
open MatchingFPRAS Turing PhysicalPost PhysicalStream LiteralPacked TreeTyped Polynomial

noncomputable def erase : Program := Program.ofTM1 (LiteralTape.eraseCode header.length) () ()

end ContingencyTables.LiteralProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MatrixCodeEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial equality of explicitly stored rectangular arrays -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

def matrixSignature (X : MatrixCode) : List ℕ×List ℕ := (X.map List.length,X.flatten)

lemma matrixSignature_injective : Function.Injective matrixSignature := by
  intro X Y h
  exact List.eq_iff_flatten_eq.mpr ⟨congrArg Prod.snd h,congrArg Prod.fst h⟩

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_OnlineControl
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel _root_.OAI.MatchingFPRAS.TreeTyped.instCodecData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineControl
open TreeData TreeMachine RegisterProc Turing MachineCost PhysicalStream OnlineStack

variable {R Λ α : Type} [DecidableEq R]
inductive Instr (R Λ : Type) where
  | halt
  | go (next : Λ)
  | branch (i : R) (nil cons : Λ)
  | call (P : OnlineProc.Proc (K R)) (next : Λ)

def procedure : Instr R Λ → OnlineProc.Proc (K R)
  | .call P _ => P
  | _ => OnlineProc.deterministic (atom .halt)
def successor : Instr R Λ → Option Λ
  | .call _ l => some l
  | _ => none
abbrev Label (M : Λ → Instr R Λ) := Λ ⊕ ((l : Λ) × (procedure (M l)).Label)
instance instFintypeLabel (M : Λ → Instr R Λ) [Fintype Λ] : Fintype (Label M) := by unfold Label; infer_instance

def code (M : Λ → Instr R Λ) : Label M → TM2.Stmt (fun _ : K R=>Bool) (Label M) Store
  | .inl l => match M l with
    | .halt => .halt
    | .go k => .goto (fun _=>.inl k)
    | .branch i a b => .peek (.inl i) (fun _ x=>x) (.branch (fun x=>x.getD false)
        (.load (fun _=>none) (.goto (fun _=>.inl b)))
        (.load (fun _=>none) (.goto (fun _=>.inl a))))
    | .call _ _ => .goto (fun _=>.inr ⟨l,default⟩)
  | .inr ⟨l,u⟩ => StackComposition.relabel (fun u=>.inr ⟨l,u⟩)
      ((successor (M l)).map Sum.inl) ((procedure (M l)).code u)
def coins (M : Λ → Instr R Λ) : CoinTM1.Coins (Label M)
  | .inl _ => none
  | .inr ⟨l,u⟩ => ((procedure (M l)).coin u).map (fun g b=>.inr ⟨l,g b⟩)
def compile [Fintype Λ] [Inhabited Λ] (M : Λ → Instr R Λ) : OnlineProc.Proc (K R) :=
  { toProc := { Label := Label M, entry := ⟨.inl default⟩, code := code M }, coin := coins M }
def cfg (M : Λ → Instr R Λ) (l : Option Λ) (E : Env R) : TM2.Cfg (fun _ : K R=>Bool) (Label M) Store :=
  ⟨l.map Sum.inl,none,encodeEnv E⟩
def At (M : Λ → Instr R Λ) (out : α → Env R) (l : Option Λ) (E : Env R) (p : Experiment α) : Prop :=
  Executes (code M) (coins M) (fun a=>cfg M none (out a)) (cfg M l E) p

lemma done (M : Λ → Instr R Λ) (out : α → Env R) (a : α) :
    At M out none (out a) (.done a) := .done a
lemma halt (M : Λ → Instr R Λ) (out : α → Env R) (l : Λ) (h : M l=.halt) (a : α) :
    At M out (some l) (out a) (.delay 1 (.done a)) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,cfg,Option.map_none] using done M out a
lemma nilBranch (M : Λ → Instr R Λ) (out : α → Env R) (l a b : Λ) (i : R)
    (h : M l=.branch i a b) (E : Env R) (hi : E i=.nil)
    (p : Experiment α) (hp : At M out (some a) E p) :
    At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,encodeEnv,hi,encode,List.head?_cons,Option.getD_some,Bool.cond_false,
    cfg,Option.map_some] using hp
lemma consBranch (M : Λ → Instr R Λ) (out : α → Env R) (l a b : Λ) (i : R)
    (h : M l=.branch i a b) (E : Env R) (x y : Data) (hi : E i=.cons x y)
    (p : Experiment α) (hp : At M out (some b) E p) :
    At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,encodeEnv,hi,encode,List.head?_cons,Option.getD_some,Bool.cond_true,
    cfg,Option.map_some] using hp

lemma call {β : Type} (M : Λ → Instr R Λ) (out : α → Env R) (l next : Λ)
    (P : OnlineProc.Proc (K R)) (h : M l=.call P next)
    (E : Env R) (F : β → Env R) (q : Experiment β)
    (hq : Executes P.code P.coin (fun b=>⟨none,none,encodeEnv (F b)⟩)
      ⟨some default,none,encodeEnv E⟩ q)
    (p : β → Experiment α) (hp : ∀ b,At M out (some next) (F b) (p b)) :
    At M out (some l) E (.delay 1 (q.bind p)) := by
  have hq' : Executes (procedure (M l)).code (procedure (M l)).coin
      (fun b=>⟨none,none,encodeEnv (F b)⟩) ⟨some default,none,encodeEnv E⟩ q := by
    rw [show procedure (M l)=P by rw [h]; rfl]
    exact hq
  have hh := hq'.relabel (code M) (coins M) (fun u=>Sum.inr ⟨l,u⟩)
    ((successor (M l)).map Sum.inl) (fun _=>rfl) (fun _=>rfl)
  apply Executes.step _ _ _ _ rfl
  have hb := hh.bind p (fun a=>cfg M none (out a)) (fun b=>by
    simpa only [At,cfg,Option.map_none,StackComposition.mapCfg_none,h,successor,Option.map_some] using hp b)
  simpa only [code,h,TM2.stepAux,StackComposition.mapCfg_some] using hb

lemma deterministicCall (M : Λ → Instr R Λ) (out : α → Env R) (l next : Λ)
    (P : RegisterProc.Proc (K R)) (h : M l=.call (OnlineProc.deterministic P) next)
    (E F : Env R) (n : ℕ) (he : RegisterProc.Exec P (encodeEnv E) (encodeEnv F) n)
    (p : Experiment α) (hp : At M out (some next) F p) :
    ∃ q,At M out (some l) E q ∧ (∀ f : α → ℚ,q.mean f=p.mean f) ∧ q.cost ≤ n+1+p.cost := by
  obtain ⟨k,hk,he⟩:=he
  obtain ⟨r,hr,hm,hc⟩:=Executes.of_run P.code k _ _ _ he
  refine ⟨.delay 1 (r.bind (fun _=>p)),call M out l next (OnlineProc.deterministic P) h E (fun _ : Unit=>F)
    r hr (fun _=>p) (fun _=>hp),?_,?_⟩
  · intro f
    simpa only [Experiment.mean,Experiment.mean_bind] using hm (fun _=>p.mean f)
  · have hh:=Experiment.cost_bind_le r (fun _=>p) p.cost (fun _=>le_rfl)
    simp only [Experiment.cost]
    omega
end MatchingFPRAS.OnlineControl

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OnlineIntegerRetry
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed online machine for repeat-until-success -/

namespace ContingencyTables.OnlineIntegerRetry
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeMachine
open MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeTyped (Codec)
open MatchingFPRAS.RegisterProc MatchingFPRAS.OnlineStack
open MatchingFPRAS.PhysicalStream

def prepareProc : RegisterProc.Proc (K Reg) :=
  RegisterProc.seq (copy 0 1 (by decide)) (cons 1 2 (by decide))
def finishProc : RegisterProc.Proc (K Reg) :=
  RegisterProc.seq (clear 1)
    (RegisterProc.seq (split 1 2 (by decide)) (clear 1))

end ContingencyTables.OnlineIntegerRetry

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RetryNumeratorProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary first-success numerators via a two-coordinate recurrence -/

namespace ContingencyTables.RetryNumeratorPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def count (z : Input) : ℕ := (IntegerMatrixPrograms.iterate (setup z)).headD 0

end ContingencyTables.RetryNumeratorPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalProfileProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the initial profile directly from the greedy table -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

abbrev OriginalViewInput := (List (ℕ×ℕ)×ℕ)×MatrixCode

def originalFirstView (z : OriginalViewInput) : List ℕ :=
  z.1.1.map (fun ij => matrixEntry (z.2,ij))

def originalViews (z : OriginalViewInput) : List ℕ×List ℕ :=
  (originalFirstView z,complementValues (z.1.2,originalFirstView z))

def initialViewInput (z : List ℕ×List ℕ) : OriginalViewInput :=
  ((marginCatalog z,marginThreshold z),GreedyFeasibleTable.listMatrix z.1 z.2)

def initialViews (z : List ℕ×List ℕ) : List ℕ×List ℕ := originalViews (initialViewInput z)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OuterTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reconstructing and testing an original table from an outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms Polynomial

abbrev OuterTableData :=
  ((List (ℕ×ℕ)×(List ℕ×List ℕ))×(List ℕ×List ℕ))×((ℕ×ℕ)×MatrixCode)
abbrev OuterTableCell := OuterTableData×(ℕ×ℕ)

def outputCellPosition (z : OuterTableCell) : ℕ := z.1.1.1.1.idxOf z.2

def outputSmallEntry (z : OuterTableCell) : ℕ := z.1.1.1.2.1.getD (outputCellPosition z) 0

def outputDensePosition (z : OuterTableCell) : ℕ×ℕ :=
  (z.1.1.2.1.idxOf z.2.1,z.1.1.2.2.idxOf z.2.2)

def outputLargeEntry (z : OuterTableCell) : ℕ :=
  matrixEntry (z.1.2.2,outputDensePosition z)-z.1.2.1.2

def outputEntry (z : OuterTableCell) : ℕ :=
  if outputCellPosition z < z.1.1.1.1.length then outputSmallEntry z else outputLargeEntry z

def paddingTest (z : ℕ×MatrixCode) : Bool := z.2.all (fun row => row.all (fun a => decide (z.1≤a)))

def outerSuccess (z : OuterTableData) : Bool :=
  balancedTest (z.1.1.2,z.2.1.1) && paddingTest (z.2.1.2,z.2.2)

abbrev OuterMatrixInput := (List ℕ×List ℕ)×OuterTableData

def outputShape (z : OuterMatrixInput) : CompletionData := (z.1,[])

def outputRows (z : OuterMatrixInput) : List ℕ := completionRows (outputShape z)
def outputColumns (z : OuterMatrixInput) : List ℕ := completionColumns (outputShape z)

def outputRowEntry (z : (OuterMatrixInput×ℕ)×ℕ) : ℕ := outputEntry (z.1.1.2,(z.1.2,z.2))

def outputRow (z : OuterMatrixInput×ℕ) : List ℕ :=
  (outputColumns z.1).map (fun j => outputRowEntry (z,j))

def outputMatrix (z : OuterMatrixInput) : MatrixCode :=
  (outputRows z).map (fun i => outputRow (z,i))

def acceptedTable (z : OuterMatrixInput) : Option MatrixCode :=
  if outerSuccess z.2 then some (outputMatrix z) else none

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the independent words of the physical outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def profileWalkChunks (z : ProfileWordInput) : List (List Bool) :=
  wordChunks (profileWordWidth z,z.2.take (profileWalkWidth z))

def profileWalkWords (z : ProfileWordInput) : List ProfileWord :=
  (profileWalkChunks z).map (fun bits => splitProfileWord (z.1.1.2,bits))

open FairBits GridBoundary
open scoped Classical
end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfilePublicProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sampler's public binary parser and matrix printer -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralParse MatchingFPRAS.LiteralCodec
open DensePrograms

def parsedSampling (as : List MatchingFPRAS.Symbol) : SamplingParameters := samplingInput (parse as)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_VectorRetryProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First-success propagation of an entire vector of integer counts -/

namespace ContingencyTables.VectorRetryPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

def counts (z : Input) : List ℕ :=
  (indices z).map (fun j => RetryNumeratorPrograms.count (entryInput (z,j)))

end ContingencyTables.VectorRetryPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary row and column checks for original-table candidates -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

abbrev OriginalCheckInput := (List ℕ×List ℕ)×MatrixCode

def originalColumnTotals (z : OriginalCheckInput) : List ℕ :=
  (List.range z.1.2.length).map (fun j => columnTotal (z.2,j))

/-- Applied to the fixed rectangular shape generated by the enumerator. -/
def originalTableTest (z : OriginalCheckInput) : Bool :=
  decide (z.2.map List.sum=z.1.1) && decide (originalColumnTotals z=z.1.2)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating original tables by all their bounded entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

def originalFreeMatrix (z : CompletionMargins×List ℕ) : MatrixCode :=
  unflattenGrid (originalLayoutMargins z.1,z.2)

def originalCandidate (z : CompletionMargins×List ℕ) : Option MatrixCode :=
  let X := originalFreeMatrix z
  if originalTableTest (z.1,X) then some X else none

def originalEnumerationData (z : CompletionMargins) : GridEnumerationData :=
  completionEnumerationData (originalLayoutMargins z)

def originalCandidates (z : CompletionMargins) : List (Option MatrixCode) :=
  (gridWords (originalEnumerationData z)).map (fun v => originalCandidate (z,v))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary lookup of an original table's finite-box index -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def originalIndexInput (z : CompletionMargins×MatrixCode) : GridIndexData :=
  (z.2.flatten,z.1.1.sum+1)

def originalIndex (z : CompletionMargins×MatrixCode) : ℕ := gridIndex (originalIndexInput z)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_TableIndexProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the position of a table in the completion enumeration -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

def tableFreeCoordinates (z : ExponentData) : List ℕ :=
  (tableFreeCells z).map (fun ij => tableFreeValue (z,ij))

def tableIndexInput (z : CompletionData) : GridIndexData :=
  (tableFreeCoordinates (z,0),z.1.1.sum+1)

def tableIndex (z : CompletionData) : ℕ := gridIndex (tableIndexInput z)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerEquivLaw
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer laws under bijective coordinate changes -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] {Q : ℕ}

lemma toRational_equiv (p : IntegerLaw A Q) (e : A ≃ B) (hQ : 0<Q) :
    (p.equiv e).toRational hQ=FirstSuccess.equivLaw e (p.toRational hQ) := by
  apply ResidualMixture.RationalLaw.ext
  rfl

/-- The integer propagation table also defines a normalized finite law. -/
def walk [DecidableEq A] (K : A → IntegerLaw A Q) (x : A) (n : ℕ) :
    IntegerLaw A (Q^n) where
  count := IntegerPropagation.numerators (fun x y => (K x).count y) x n
  total := IntegerPropagation.numerators_total _ Q (fun x => (K x).total) x n

end ContingencyTables.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BooleanEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating only the short proposal word -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

def booleanWords (xs : List Bool) : List (List Bool) :=
  (gridWords (xs,2)).map (List.map digitBool)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerMatrixPoint
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Propagating an executable point mass through an integer matrix -/

namespace ContingencyTables.IntegerMatrixPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def fromPoint (z : ℕ×(List (List ℕ)×ℕ)) : List ℕ :=
  iterate (z.1,(z.2.1,pointVector z.2))

end ContingencyTables.IntegerMatrixPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the number of feasible original-table box entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def originalCardEntry (o : Option MatrixCode) : ℕ := if o.isSome then 1 else 0

def originalCardinality (z : CompletionMargins) : ℕ :=
  ((originalCandidates z).map originalCardEntry).sum

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalResidualVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit integer correction weights on the original-table box -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

/-- Candidate matrices, ordinary numerators, denominator/branch size, and table count. -/
abbrev ResidualVectorCache := (List (Option MatrixCode)×List ℕ)×((ℕ×ℕ)×ℕ)

def residualVectorEntry (z : ResidualVectorCache×ℕ) : ℕ :=
  if (z.1.1.1.getD z.2 none).isSome then
    ResidualWeightPrograms.count (z.1.2.1,(z.1.2.2,z.1.1.2.getD z.2 0)) else 0

def residualVectorIndices (z : ResidualVectorCache) : List ℕ := List.range z.1.1.length

def residualVector (z : ResidualVectorCache) : List ℕ :=
  (residualVectorIndices z).map (fun k => residualVectorEntry (z,k))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScheduledResidualProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing residual weights from margins, precision, and branch denominator -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] residualVector originalCandidates originalCardinality

/-- Ordinary count vector, original margins, and reciprocal branch probability. -/
abbrev ScheduledResidualCache := List ℕ×(CompletionMargins×ℕ)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_OnlineFold
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeData TreeMachine RegisterProc TreeFunction TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B : Type} [Codec A] [Codec B]

namespace Fold
open OnlineControl
open TreeTyped.Fold (Point)

def code (P : OnlineProc.Proc (K Reg)) : Point → OnlineControl.Instr Reg Point
  | .loop => .call (OnlineProc.deterministic (TreeFunction.split 1 0 (by decide))) .check
  | .check => .branch 1 .halt .splitHead
  | .splitHead => .call (OnlineProc.deterministic (TreeFunction.split 3 1 (by decide))) .pushTail
  | .pushTail => .call (OnlineProc.deterministic (TreeFunction.cons 1 2 (by decide))) .pushArgs
  | .pushArgs => .call (OnlineProc.deterministic (TreeFunction.cons 3 0 (by decide))) .body
  | .body => .call P .popTail
  | .popTail => .call (OnlineProc.deterministic (TreeFunction.split 1 2 (by decide))) .rebuild
  | .rebuild => .call (OnlineProc.deterministic (TreeFunction.cons 1 0 (by decide))) .loop
  | .halt => .halt
end Fold

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_OnlineFrame
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeData TreeMachine RegisterProc TreeFunction TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]
namespace Second
open OnlineControl

def code (P : OnlineProc.Proc (K Reg)) : Point → OnlineControl.Instr Reg Point
  | .split => .call (OnlineProc.deterministic (TreeFunction.split 1 0 (by decide))) .save
  | .save => .call (OnlineProc.deterministic (TreeFunction.cons 1 2 (by decide))) .body
  | .body => .call P .pop
  | .pop => .call (OnlineProc.deterministic (TreeFunction.split 1 2 (by decide))) .cons
  | .cons => .call (OnlineProc.deterministic (TreeFunction.cons 1 0 (by decide))) .halt
  | .halt => .halt
end Second

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactIntegerProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of an exact integer-weighted rejection trial -/

namespace ContingencyTables.ExactIntegerPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

/-- Fractions share the total integer weight before canonical reduction. -/
def weightsCode (xs : List ℕ) : List TreeFraction.Fraction :=
  xs.map (fun w => TreeFraction.normalize (w,xs.sum))

def choiceInput (z : Input) : List TreeFraction.Fraction×TreeFraction.Fraction :=
  (weightsCode z.1,(StackAddition.value z.2,z.1.sum))

/-- One trial returns an index or requests another independent word.
All integers are processed in binary; no weight is expanded into copies. -/
def weightedIndex (z : Input) : Option ℕ :=
  if StackAddition.value z.2<z.1.sum then some (ExecutableChoice.choose (choiceInput z)) else none

end ContingencyTables.ExactIntegerPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactIntegerOnline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete fair-bit integer trial used by exact correction -/

namespace ContingencyTables.ExactIntegerOnline
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open ExactIntegerChoice ExactIntegerPrograms FirstSuccess ResidualMixture
open scoped BigOperators Classical

def trial (w : List ℕ) : Experiment (Option ℕ) :=
  FiniteWordExecution.experiment trialBits weightedIndex w

end ContingencyTables.ExactIntegerOnline

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactMatrixTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Returning a matrix from the exact integer-weighted trial -/

namespace ContingencyTables.ExactMatrixTrial
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open DensePrograms ProfilePrograms

/-- Enumerated candidates together with a feasible fallback. -/
abbrev Lookup := List (Option MatrixCode)×MatrixCode
abbrev Input := Lookup×List ℕ

def lookup (z : Lookup×ℕ) : MatrixCode := (z.1.1.getD z.2 none).getD z.1.2

def decode (z : Lookup×Option ℕ) : Option MatrixCode :=
  z.2.map (fun i => lookup (z.1,i))

def trial (z : Input) : Experiment (Option MatrixCode) :=
  (ExactIntegerOnline.trial z.2).map (fun i => decode (z.1,i))

end ContingencyTables.ExactMatrixTrial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactSamplingParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the exact sampler's precision from its margin-only input -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] marginDimension marginBinaryLength parameterWordCount

def exactPrecision (z : CompletionMargins) : ℕ := (marginDimension z)^6*(marginBinaryLength z)^2

attribute [local irreducible] exactPrecision

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_EdmondsKarpDistance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded shortest-path labels for Edmonds--Karp

An unreachable vertex has label n. Reachable vertices have their actual
shortest distance, at most n-1. These labels are obtained from the already
proved breadth-first search, independently of its deterministic tie rule.
-/
namespace ContingencyTables.EdmondsKarpDistance
open FiniteDirectedBFS PublishedEdmondsKarp
open scoped Classical
noncomputable section
variable {n : ℕ}

def distance (E : Fin n→Fin n→Bool) (s v : Fin n) : ℕ :=
  ((paths E s n v).map (fun xs => xs.length-1)).getD n

def label (c : Capacity n) (f : Flow n) (s v : Fin n) : ℕ :=
  distance (ResidualSearch.edge c f) s v

end
end ContingencyTables.EdmondsKarpDistance

end OAI
end


