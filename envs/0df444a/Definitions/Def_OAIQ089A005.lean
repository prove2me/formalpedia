-- Prove2me | Definitions.Def_OAIQ089A005
-- name    : OAIQ089A005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T02:53:57.899766+00:00
-- url     : https://prove2.me/theorems/ac181439-63e4-4d20-9ec1-e4d1eed5559b
-- title:
--   Definitions bundle OAIQ089A005 of the split of OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 462 declarations of OpenAI's Lean: 137 definitions, 1 inductive type or structure, 5 instances and 319 theorems. The definitions and types are `OAI.ContingencyTables.EstimatorWordBanks.wordEquiv`, `OAI.ContingencyTables.ExactIntegerChoice.trialLaw`, `OAI.ContingencyTables.ExcessContextProfiles.ValidAssignments`, `OAI.ContingencyTables.ExcessContextProfiles.contextVertices`, `OAI.ContingencyTables.FactorialSignatures.additionLiftMatrix`, `OAI.ContingencyTables.FactorialSignatures.factorialMatrix`, `OAI.ContingencyTables.FactorialSignatures.integerAdditionMatrix`, `OAI.ContingencyTables.FactorialSignatures.removalLiftMatrix`, `OAI.ContingencyTables.FairBits.listBitDraw`, `OAI.ContingencyTables.FairBits.rationalThresholdMass`, `OAI.ContingencyTables.FiniteChainSlowdown.slow`, `OAI.ContingencyTables.FiniteChainSlowdown.slowKilled`, `OAI.ContingencyTables.FiniteLawMoments.expectation`, `OAI.ContingencyTables.FiniteObservableTransport.SameLaw`, `OAI.ContingencyTables.FiniteObservableTransport.recorded`, `OAI.ContingencyTables.FiniteWordSlices.split`, `OAI.ContingencyTables.FirstPaperPhysicalMarginal.fullSoftFamily`, `OAI.ContingencyTables.FirstSuccess.varyingLaw`, `OAI.ContingencyTables.FixedCardinalityBits.roundedFixedLaw`, `OAI.ContingencyTables.FixedCardinalityBits.roundedHeadLaw`, `OAI.ContingencyTables.FixedCardinalityMixture.roundedSizeMixture`, `OAI.ContingencyTables.ForestAffineProgram.data`, `OAI.ContingencyTables.ForestAssignmentSplit.assignmentSplit`, `OAI.ContingencyTables.ForestBoxCardinality.Assignments`, `OAI.ContingencyTables.ForestCut.cutTerm`, `OAI.ContingencyTables.ForestLiteralCount.cellCount`, `OAI.ContingencyTables.ForestLiteralCount.profile`, `OAI.ContingencyTables.ForestRootPenalty.residualDemand`, `OAI.ContingencyTables.ForestScaledPenalty.zeroAssignment`, `OAI.ContingencyTables.GraphCompletionCounts.TreeIndex`, `OAI.ContingencyTables.GraphCompletionCounts.physical`, `OAI.ContingencyTables.InitialDefectChoices.chosen`, `OAI.ContingencyTables.InitialDefectChoices.defectEquivChoices`, `OAI.ContingencyTables.InitialDefectChoices.encode`, `OAI.ContingencyTables.InitialDefectChoices.localWeight`, `OAI.ContingencyTables.InitialFactorialBits.finiteChoiceLaw`, `OAI.ContingencyTables.IntegerBoxTruncation.truncate`, `OAI.ContingencyTables.IntegerWeightedTransport.ExcessAssignments`, `OAI.ContingencyTables.IntegerWeightedTransport.ValidExcess`, `OAI.ContingencyTables.IntegerWeightedTransport.auxiliaryKernel` and 98 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `ContingencyTables_Counting_EstimatorWordBanks`, `ContingencyTables_Machines_FiniteTraceSlowdown`, `ContingencyTables_Machines_FiniteVaryingWordWalk`, `ContingencyTables_Machines_FiniteWordDependent`, `ContingencyTables_Machines_FiniteWordSlices`, `ContingencyTables_Machines_FixedCardinalityBits`, `ContingencyTables_Machines_FixedCardinalityMixture`, `ContingencyTables_Machines_InitialDrawReindex`, `ContingencyTables_Machines_MedianFractionProgram`, `ContingencyTables_Machines_OnlineIntegerRetry`, `ContingencyTables_Rooted_ForestAffineProgram`, `ContingencyTables_Rooted_ForestAssignmentSplit`, `ContingencyTables_Rooted_ForestBoxCardinality`, `ContingencyTables_Rooted_ForestCapacity`, `ContingencyTables_Rooted_ForestCut`, `ContingencyTables_Rooted_ForestLiteralCount`, `ContingencyTables_Rooted_ForestPenaltyApplication`, `ContingencyTables_Rooted_ForestRootPenalty`, `ContingencyTables_Rooted_ForestScaledBounds`, `ContingencyTables_Rooted_ForestScaledPenalty`, `ContingencyTables_Rooted_LargePairEnumeration`, `ContingencyTables_Rooted_MaximumForest`, `ContingencyTables_Rooted_RootedAffine`, `ContingencyTables_Rooted_RootedBinDrawLaw`, `ContingencyTables_Rooted_RootedBinFramesProgram`, `ContingencyTables_Rooted_RootedCellDataProgram`, `ContingencyTables_Rooted_RootedCoefficientProgram`, `ContingencyTables_Rooted_RootedCompletion`, `ContingencyTables_Rooted_RootedComponentProgram`, `ContingencyTables_Rooted_RootedComputedEstimator`, `ContingencyTables_Rooted_RootedCorrectionSampleLaw`, `ContingencyTables_Rooted_RootedCut`, `ContingencyTables_Rooted_RootedDemandProgram`, `ContingencyTables_Rooted_RootedFarMass`, `ContingencyTables_Rooted_RootedHistoryStep`, `ContingencyTables_Rooted_RootedIntegerEvaluation`, `ContingencyTables_Rooted_RootedIntervals`, `ContingencyTables_Rooted_RootedLargeMarginal`, `ContingencyTables_Rooted_RootedLiteralCount`, `ContingencyTables_Rooted_RootedPenalty`, `ContingencyTables_Rooted_RootedPenaltyEvaluateProgram`, `ContingencyTables_Rooted_RootedPenaltyProgram`, `ContingencyTables_Rooted_RootedPhysicalCompletion`, `ContingencyTables_Rooted_RootedRootPenalty`, `ContingencyTables_Rooted_RootedScaledPenalty`, `ContingencyTables_Rooted_TreeMarginalEnumeration`, `ContingencyTables_Rooted_TreeMarginalSignature`, `ContingencyTables_Sampling_ExactIntegerRetry`, `ContingencyTables_Sampling_FirstPaperCodeNeighbors`, `ContingencyTables_Sampling_FirstPaperExposureVariance`, `ContingencyTables_Sampling_FirstPaperPhysicalMarginal`, `ContingencyTables_Sampling_FirstPaperPreparedProposal`, `ContingencyTables_Sampling_Padding`, `ContingencyTables_Sampling_PhysicalMassBound`, `ContingencyTables_Sampling_PhysicalPrefixEnergies`, `ContingencyTables_Sampling_ProfileExchangeProgram`, `ContingencyTables_Sampling_ProfileInverseRepairProgram`, `ContingencyTables_Sampling_ProfileRepairProgram`, `ContingencyTables_Sampling_RepairFibres`, `ContingencyTables_Sampling_RepairPrefixes`, `ContingencyTables_Sampling_ResidualMixture`, `ContingencyTables_Sampling_SmallBoundsProgram`, `ContingencyTables_Sampling_SmallCellIndexProgram`, `ContingencyTables_Sampling_SmallComplementProgram`, `ContingencyTables_Sampling_SmallContextCoordinates`, `ContingencyTables_Sampling_SmallContextEnumeration`, `ContingencyTables_Sampling_SmallContextFibres`, `ContingencyTables_Sampling_SmallDefectLabels`, `ContingencyTables_Sampling_SmallExchangeListProgram`, `ContingencyTables_Sampling_SmallInverseRepairList`, `ContingencyTables_Sampling_SmallLineSumProgram`, `ContingencyTables_Sampling_SmallMarginTestProgram`, `ContingencyTables_Sampling_SmallPatternArithmetic`, `ContingencyTables_Sampling_SmallPatternProgram`, `ContingencyTables_Sampling_SmallProfileFlatCode`, `ContingencyTables_Sampling_SmallRepairGeometryProgram`, `ContingencyTables_Sampling_SmallRepairListProgram`, `ContingencyTables_Transport_AuxiliaryRepairMass`, `ContingencyTables_Transport_BalancedSummation`, `ContingencyTables_Transport_ChoiceContextEnumeration`, `ContingencyTables_Transport_ContextAdjacentTransport`, `ContingencyTables_Transport_ContextChildVariance`, `ContingencyTables_Transport_ContextGraphMembership`, `ContingencyTables_Transport_ExcessContextProfiles`, `ContingencyTables_Transport_ExcessPairCoordinates`, `ContingencyTables_Transport_FactorialSignatures`, `ContingencyTables_Transport_FiniteChainGraphComparison`, `ContingencyTables_Transport_FiniteChainSlowdown`, `ContingencyTables_Transport_FiniteChainWeightVariance`, `ContingencyTables_Transport_FiniteCorrectionLaw`, `ContingencyTables_Transport_FiniteDependentApproximation`, `ContingencyTables_Transport_FiniteDependentLaw`, `ContingencyTables_Transport_FiniteDeterministicJoint`, `ContingencyTables_Transport_FiniteExchangeObservables`, `ContingencyTables_Transport_FiniteExposureBudget`, `ContingencyTables_Transport_FiniteExposureVariance`, `ContingencyTables_Transport_FiniteGraphPoincareBudget`, `ContingencyTables_Transport_FiniteLawDecidableEq`, `ContingencyTables_Transport_FiniteLawMoments`, `ContingencyTables_Transport_FiniteObservableTransport`, `ContingencyTables_Transport_FinitePartialDraw`, `ContingencyTables_Transport_FinitePartitionVariance`, `ContingencyTables_Transport_FinitePrefixVariance`, `ContingencyTables_Transport_FiniteRationalThreshold`, `ContingencyTables_Transport_FiniteRecordedHistory`, `ContingencyTables_Transport_FiniteRepairVariance`, `ContingencyTables_Transport_GraphCompletionCounts`, `ContingencyTables_Transport_GraphIntegralCompletion`, `ContingencyTables_Transport_InitialDefectChoices`, `ContingencyTables_Transport_IntegerAuxiliaryEnumeration`, `ContingencyTables_Transport_IntegerBoxTruncation`, `ContingencyTables_Transport_IntegerChildLogConcavity`, `ContingencyTables_Transport_IntegerChildVariance`, `ContingencyTables_Transport_IntegerCorrectionKernel`, `ContingencyTables_Transport_IntegerExposure`, `ContingencyTables_Transport_IntegerFutureKernel`, `ContingencyTables_Transport_IntegerFutureSquare`, `ContingencyTables_Transport_IntegerLeafEnergy`, `ContingencyTables_Transport_IntegerLeafTransport`, `ContingencyTables_Transport_IntegerPairRecursion`, `ContingencyTables_Transport_IntegerRecursiveFlow`, `ContingencyTables_Transport_IntegerRecursivePotential`, `ContingencyTables_Transport_IntegerRootTransport`, `ContingencyTables_Transport_IntegerSliceReindex`, `ContingencyTables_Transport_IntegerSliceRestriction`, `ContingencyTables_Transport_IntegerTransportLimit`, `ContingencyTables_Transport_IntegerTruncatedTransport`, `ContingencyTables_Transport_IntegerWeightedTransport`, `ContingencyTables_Transport_LabelledFactorial`, `ContingencyTables_Transport_LaminarSignature`, `ContingencyTables_Transport_LineUnarySignature`, `ContingencyTables_Transport_ListBitProposal`, `ContingencyTables_Transport_NestedPenaltyApplication`, `ContingencyTables_Transport_NestedProductSignature`, `ContingencyTables_Transport_NestedReindex`, `ContingencyTables_Transport_PairedProfileSemantics`, `ContingencyTables_Transport_PowerOfTwoApproximation`, `ContingencyTables_Transport_RealKernelApproximation`, `ContingencyTables_Transport_RealPathApproximation`, `ContingencyTables_Transport_ReferenceCompletionBounds`, `ContingencyTables_Transport_ReferenceEdgeAcceptance`, `ContingencyTables_Transport_RowMajorEnumeration`, `ContingencyTables_Transport_SliceFactorial`, `ContingencyTables_Transport_TransversalCount`, `ContingencyTables_Transport_TwoLiftStates`, `MatchingCount_Graphs_SafeTrace`, `MatchingCount_Tapes_TapeTools`.
--
--   **Imports.** It imports the published bundle `Def_ContingencyTables`; the bundles `OAIQ089A000`, `OAIQ089A001` and `OAIQ089A002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ089A007` and `OAIQ089A008`; the statements `OAI.ContingencyTables.CompanionPhaseContinuation.run_sameLaw` and `OAI.ContingencyTables.CompanionRestartProgram.output_native_sameLaw`.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A000
import Definitions.Def_OAIQ089A001
import Definitions.Def_OAIQ089A002

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

def padTable {r : I → ℕ} {c : J → ℕ} (P : I → J → ℕ) (X : Table r c) :
    Table (paddedRows r P) (paddedColumns c P) :=
  ⟨fun i j => X.val i j + P i j, by
    constructor
    · intro i
      rw [sum_add_distrib, X.property.1 i]
      rfl
    · intro j
      rw [sum_add_distrib, X.property.2 j]
      rfl⟩

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ResidualMixture
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact correction by a finite residual mixture

Finite probability arithmetic gives the residual correction used in exact
sampling. The construction is that of Göbel, Liu, Manurangsi and Pappik,
*Perfect sampling from rapidly mixing Markov chains*, arXiv:2410.00882v2
(2024), §3.1, Algorithm 1 and Theorem 6.

All probabilities are rational, as required for the finite fair-bit sampler.
-/

open scoped BigOperators

namespace ContingencyTables.ResidualMixture

variable {α : Type*} [Fintype α]

variable [Nonempty α]

/-- The residual point mass used on the rare correction branch. -/
def residualMass (p : RationalLaw α) (δ : ℚ) (x : α) : ℚ :=
  (uniformMass (α := α) - (1 - δ) * p.mass x) / δ

/-- The pointwise approximation and cardinality bound imply domination.
This is the estimate immediately before the definition of `r(z)` in 200-01. -/
lemma approximate_domination (p : RationalLaw α) {δ : ℚ}
    (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hcard : (Fintype.card α : ℚ) * δ ≤ 1)
    (happrox : ∀ x, p.mass x ≤ uniformMass (α := α) + δ ^ 2) (x : α) :
    (1 - δ) * p.mass x ≤ uniformMass (α := α) := by
  have hδu : δ ≤ uniformMass (α := α) := by
    rw [uniformMass, le_div_iff₀ card_pos]
    nlinarith [hcard]
  have hmul := mul_le_mul_of_nonneg_left (happrox x) (sub_nonneg.mpr hδone)
  have hδsq : δ ^ 2 ≤ δ := by nlinarith
  have herr : (1 - δ) * δ ^ 2 ≤ δ * uniformMass (α := α) := by
    have hfirst := mul_le_mul_of_nonneg_left hδsq (sub_nonneg.mpr hδone)
    have hsecond := mul_le_mul_of_nonneg_left hδu (le_of_lt hδ)
    nlinarith [hfirst, hsecond]
  nlinarith [hmul, herr]

omit [Nonempty α] in
lemma residualMass_nonnegative (p : RationalLaw α) {δ : ℚ} (hδ : 0 < δ)
    (hdom : ∀ x, (1 - δ) * p.mass x ≤ uniformMass (α := α)) (x : α) :
    0 ≤ residualMass p δ x := by
  exact div_nonneg (sub_nonneg.mpr (hdom x)) (le_of_lt hδ)

lemma residualMass_total (p : RationalLaw α) {δ : ℚ} (hδ : δ ≠ 0) :
    ∑ x, residualMass p δ x = 1 := by
  simp only [residualMass, ← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.mul_sum, uniformMass_total, p.total]
  field_simp
  ring

/-- A residual law exists whenever the ordinary branch is pointwise dominated
by the target law. No additional existence assumption is used. -/
def residualLaw (p : RationalLaw α) {δ : ℚ} (hδ : 0 < δ)
    (hdom : ∀ x, (1 - δ) * p.mass x ≤ uniformMass (α := α)) : RationalLaw α where
  mass := residualMass p δ
  nonnegative := residualMass_nonnegative p hδ hdom
  total := residualMass_total p (ne_of_gt hδ)

omit [Nonempty α] in
/-- The two branches combine to give exactly uniform point masses. -/
theorem mixture_exact (p : RationalLaw α) {δ : ℚ} (hδ : δ ≠ 0) (x : α) :
    (1 - δ) * p.mass x + δ * residualMass p δ x = uniformMass (α := α) := by
  dsimp [residualMass]
  field_simp
  ring

/-- The complete finite residual-mixture consequence of the pointwise
approximation bound used by the manuscript. -/
theorem exact_correction (p : RationalLaw α) {δ : ℚ}
    (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hcard : (Fintype.card α : ℚ) * δ ≤ 1)
    (happrox : ∀ x, p.mass x ≤ uniformMass (α := α) + δ ^ 2) :
    ∃ r : RationalLaw α, ∀ x,
      (1 - δ) * p.mass x + δ * r.mass x = uniformMass (α := α) := by
  refine ⟨residualLaw p hδ (approximate_domination p hδ hδone hcard happrox), ?_⟩
  exact mixture_exact p (ne_of_gt hδ)

/-- The numerator realizes the residual law exactly as a rational quotient. -/
lemma residualNumerator_quotient (Q T : ℤ) (a : α → ℤ)
    (hQ : Q ≠ 0) (hT : T ≠ 0) (x : α) :
    (residualNumerator Q T a x : ℚ) /
        ((Fintype.card α : ℚ) * Q) =
      (uniformMass (α := α) - (1 - 1 / (T : ℚ)) * ((a x : ℚ) / Q)) /
        (1 / (T : ℚ)) := by
  have hQc : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ
  have hTc : (T : ℚ) ≠ 0 := by exact_mod_cast hT
  have hc : (Fintype.card α : ℚ) ≠ 0 := ne_of_gt card_pos
  simp only [residualNumerator, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Int.cast_one, uniformMass]
  field_simp

/-- Pointwise domination makes the actual integer correction weights
nonnegative, so their cumulative sums define a finite exact draw. -/
lemma residualNumerator_nonnegative {Q T : ℤ} (a : α → ℤ)
    (hQ : 0 < Q) (hT : 0 < T)
    (hdom : ∀ x, (1 - 1 / (T : ℚ)) * ((a x : ℚ) / Q) ≤
      uniformMass (α := α)) (x : α) :
    0 ≤ residualNumerator Q T a x := by
  have hQc : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hTc : (0 : ℚ) < T := by exact_mod_cast hT
  have hres : (0 : ℚ) ≤
      (uniformMass (α := α) - (1 - 1 / (T : ℚ)) * ((a x : ℚ) / Q)) /
        (1 / (T : ℚ)) :=
    div_nonneg (sub_nonneg.mpr (hdom x)) (le_of_lt (one_div_pos.mpr hTc))
  rw [← residualNumerator_quotient Q T a (ne_of_gt hQ) (ne_of_gt hT) x] at hres
  have hden : (0 : ℚ) < (Fintype.card α : ℚ) * Q := mul_pos card_pos hQc
  have hnum : (0 : ℚ) ≤ residualNumerator Q T a x :=
    by simpa using (le_div_iff₀ hden).mp hres
  exact_mod_cast hnum

end ContingencyTables.ResidualMixture

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FinitePartialDraw
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One Boolean word per listed proposal, with unused words giving a hold -/

namespace ContingencyTables.FairBits

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

variable {X : Type*} [Fintype X]

lemma injectionDraw_eq_some {k : ℕ} (e : X ↪ Fin (2^k)) (b : Fin (2^k)) (x : X) :
    injectionDraw e b=some x ↔ b=e x := by
  by_cases h : ∃ y,e y=b
  · simp only [injectionDraw,dite_eq_left h,Option.some.injEq]
    constructor
    · intro hx
      rw [←hx]
      exact (Classical.choose_spec h).symm
    · intro hx
      apply e.injective
      exact (Classical.choose_spec h).trans hx
  · have hn : b≠e x := by
      intro hx
      exact h ⟨x,hx.symm⟩
    simp only [injectionDraw,dite_eq_right h,reduceCtorEq,hn]

/-- Every listed proposal gets exactly one equally likely bit string. -/
theorem injectionDraw_mass {k : ℕ} (e : X ↪ Fin (2^k)) (x : X) :
    (mapLaw (uniformLaw (α := Fin (2^k))) (injectionDraw e)).mass (some x)=1/(2:ℚ)^k := by
  simp only [mapLaw,injectionDraw_eq_some,uniformLaw,uniformMass,Fintype.card_fin]
  simp

theorem partialBitDraw_mass (k : ℕ) (h : Fintype.card X ≤ 2^k) (x : X) :
    (mapLaw (uniformLaw (α := Fin k → Bool)) (partialBitDraw k h)).mass (some x)=1/(2:ℚ)^k := by
  unfold partialBitDraw
  rw [←map_equiv (binaryWordEquiv k),uniform_equiv]
  exact injectionDraw_mass _ x

variable {S : Type*} [Fintype S] [DecidableEq X]

lemma optionMap_mass_injective (p : RationalLaw (Option S)) (f : S → X)
    (hf : Function.Injective f) (s : S) :
    (mapLaw p (Option.map f)).mass (some (f s))=p.mass (some s) := by
  simp only [mapLaw,Fintype.sum_option,Option.map_none,Option.map_some,
    Option.some.injEq,reduceCtorEq,ite_false,zero_add,hf.eq_iff]
  simp

lemma optionMap_mass_outside (p : RationalLaw (Option S)) (f : S → X) (x : X)
    (hx : ∀ s,f s≠x) : (mapLaw p (Option.map f)).mass (some x)=0 := by
  simp only [mapLaw,Fintype.sum_option,Option.map_none,Option.map_some,
    Option.some.injEq,reduceCtorEq,ite_false,zero_add,hx,Finset.sum_const_zero]

/-- Distinct listed outcomes each have the advertised dyadic mass. -/
theorem subsetBitDraw_mass (p : X → Prop) (k : ℕ)
    (h : Fintype.card {x // p x} ≤ 2^k) (x : X) :
    (mapLaw (uniformLaw (α := Fin k → Bool)) (subsetBitDraw p k h)).mass (some x)=
      if p x then 1/(2:ℚ)^k else 0 := by
  let : DecidableEq {x // p x} := Classical.decEq _
  change (mapLaw (uniformLaw (α := Fin k → Bool))
    (fun bits => Option.map Subtype.val (partialBitDraw k h bits))).mass (some x)=_
  rw [←mapLaw_comp]
  by_cases hx : p x
  · rw [ite_eq_left hx]
    exact (optionMap_mass_injective _ Subtype.val Subtype.val_injective ⟨x,hx⟩).trans
      (partialBitDraw_mass k h ⟨x,hx⟩)
  · rw [ite_eq_right hx]
    exact optionMap_mass_outside _ Subtype.val x (fun s hs => hx (hs ▸ s.property))

end
end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteLawDecidableEq
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit decidable equality at finite-law application boundaries -/

namespace ContingencyTables.FirstSuccess

open ResidualMixture

universe u v

variable {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]

/-- The output equality decision only computes the same finite fibres;
it does not change the mapped probability law. Keeping the decisions
explicit avoids reducing a large concrete state type to match instances. -/
theorem mapLaw_decidableEq_irrel (d e : DecidableEq Y)
    (p : RationalLaw X) (f : X → Y) :
    @mapLaw X Y _ _ d p f=@mapLaw X Y _ _ e p f := by
  cases Subsingleton.elim d e
  rfl

theorem mapLaw_mass_decidableEq_irrel (d e : DecidableEq Y)
    (p : RationalLaw X) (f : X → Y) (y : Y) :
    (@mapLaw X Y _ _ d p f).mass y=(@mapLaw X Y _ _ e p f).mass y := by
  rw [mapLaw_decidableEq_irrel d e]

end ContingencyTables.FirstSuccess

namespace ContingencyTables.FairBits

open ResidualMixture FirstSuccess
open scoped Classical

universe u

variable {X : Type u} [Fintype X]

/-- The actual subset bit draw has its exact dyadic mass with any chosen
output equality decision. The draw and its embedding are unchanged. -/
theorem subsetBitDraw_mass_decidableEq (d : DecidableEq (Option X))
    (p : X → Prop) (k : ℕ) (h : Fintype.card {x // p x} ≤ 2^k) (x : X) :
    (@mapLaw (Fin k → Bool) (Option X) _ _ d
      (uniformLaw (α := Fin k → Bool)) (subsetBitDraw p k h)).mass (some x)=
        if p x then 1/(2:ℚ)^k else 0 := by
  let dX : DecidableEq X := Classical.decEq X
  have he := mapLaw_mass_decidableEq_irrel d (@Option.instDecidableEq X dX)
    (uniformLaw (α := Fin k → Bool)) (subsetBitDraw p k h) (some x)
  exact he.trans (@subsetBitDraw_mass X _ dX p k h x)

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListBitProposal
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic proposals from an explicit list without repeated entries -/

namespace ContingencyTables.FairBits
open scoped BigOperators Classical
open ResidualMixture FirstSuccess

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Read a binary index; every index beyond the list gives a hold. -/
def listBitDraw (xs : List X) (k : ℕ) (bits : Fin k → Bool) : Option X :=
  xs[(binaryWordEquiv k bits).val]?

lemma listIndex_mass (xs : List X) (hn : xs.Nodup) (k : ℕ)
    (hlen : xs.length ≤ 2^k) (x : X) :
    (mapLaw (uniformLaw (α := Fin (2^k))) (fun b => xs[b.val]?)).mass (some x)=
      if x∈xs then 1/(2:ℚ)^k else 0 := by
  by_cases hx : x∈xs
  · obtain ⟨i,hi,hix⟩ := List.mem_iff_getElem.mp hx
    have he (b : Fin (2^k)) : xs[b.val]?=some x ↔ b=⟨i,hi.trans_le hlen⟩ := by
      rw [←hix]
      exact listIndex_eq_iff xs hn k hlen i hi b
    simp only [mapLaw,uniformLaw,uniformMass,Fintype.card_fin,he,ite_eq_left hx]
    simp
  · have he (b : Fin (2^k)) : xs[b.val]?≠some x := by
      intro hb
      obtain ⟨hb,hval⟩ := List.getElem?_eq_some_iff.mp hb
      exact hx (List.mem_iff_getElem.mpr ⟨b.val,hb,hval⟩)
    simp only [mapLaw,he,ite_false,Finset.sum_const_zero,ite_eq_right hx]

/-- This implementation has exactly the same masses as a uniform
injection into the dyadic code space, with no search for that injection. -/
theorem listBitDraw_mass (xs : List X) (hn : xs.Nodup) (k : ℕ)
    (hlen : xs.length ≤ 2^k) (x : X) :
    (mapLaw (uniformLaw (α := Fin k → Bool)) (listBitDraw xs k)).mass (some x)=
      if x∈xs then 1/(2:ℚ)^k else 0 := by
  have he := map_equiv (binaryWordEquiv k)
    (uniformLaw (α := Fin k → Bool)) (fun b : Fin (2^k) => xs[b.val]?)
  rw [uniform_equiv] at he
  change (mapLaw (uniformLaw (α := Fin k → Bool))
    (fun bits => xs[(binaryWordEquiv k bits).val]?)).mass (some x)=_
  rw [←he]
  exact listIndex_mass xs hn k hlen x

theorem listBitDraw_mass_decidableEq (d : DecidableEq (Option X))
    (xs : List X) (hn : xs.Nodup) (k : ℕ) (hlen : xs.length ≤ 2^k) (x : X) :
    (@mapLaw (Fin k → Bool) (Option X) _ _ d
      (uniformLaw (α := Fin k → Bool)) (listBitDraw xs k)).mass (some x)=
      if x∈xs then 1/(2:ℚ)^k else 0 := by
  have he := mapLaw_mass_decidableEq_irrel d (@Option.instDecidableEq X inferInstance)
    (uniformLaw (α := Fin k → Bool)) (listBitDraw xs k) (some x)
  exact he.trans (listBitDraw_mass xs hn k hlen x)

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedSummation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Balanced-pair summation of two-removal forms

This is the finite unweighted closure step in paper 200-01,
Lemma `lem:pair-summation` (`D'=B`), and paper 200-02,
Lemma `lem:integer-signature`. The hypotheses describe the actual old/fresh
blocks and their adjacent cross entries. Cumulative coefficients are
constructed from those cross entries; no transport or closure conclusion is
assumed. In particular the zero-diagonal capacity-two case is included.
-/

namespace ContingencyTables

open scoped BigOperators
open LinearMap (BilinForm)

section Cumulative

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Representation up to the balanced endpoint needs no value outside
that endpoint. This version is used for the `D'=B+1` interior displays. -/
lemma pairCoefficient_represents_le (S : ℕ → V →ₗ[ℝ] ℝ) (u : ℕ → ℝ)
    (n : ℕ) (v : V)
    (huint : ∀ j, 0 < j → j < n → 0 < u j)
    (hbalance : pairCumulative S v n = 0) {j : ℕ} (hj : j ≤ n) :
    u j * pairCoefficient S u v j = pairCumulative S v j := by
  by_cases hj0 : j = 0
  · subst j
    simp [pairCoefficient, pairCumulative_zero]
  by_cases hjn : j = n
  · subst j
    simp [pairCoefficient, hbalance]
  have hu : u j ≠ 0 := ne_of_gt (huint j (by omega) (by omega))
  dsimp [pairCoefficient]
  field_simp

lemma pairCumulative_difference (S : ℕ → V →ₗ[ℝ] ℝ) (v : V) {j : ℕ} (hj : 0 < j) :
    pairCumulative S v j - pairCumulative S v (j - 1) = S j v := by
  have hh := pairCumulative_succ S v (j - 1)
  have hj' : j - 1 + 1 = j := by omega
  rw [hj'] at hh
  linarith

end Cumulative

section Closure

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The actual weighted pair estimate (`D'=B+1`) used in integer
signed transport. Only the box-valid interior matrices are evaluated.
The coefficients are the explicitly constructed cumulative quotients. -/
theorem balancedPair_weighted_potential
    (n : ℕ) (B : ℕ → BilinForm ℝ W) (old : V →ₗ[ℝ] W) (ea eb : W)
    (S : ℕ → V →ₗ[ℝ] ℝ) (u : ℕ → ℝ) (v : V)
    (hsymm : ∀ j, 0 < j → j < n → ∀ x y, B j x y = B j y x)
    (hsig : ∀ j, 0 < j → j < n → OnePositiveDirection (B j))
    (hu0 : u 0 = 0) (hun : u n = 0)
    (huint : ∀ j, 0 < j → j < n → 0 < u j)
    (hbalance : pairCumulative S v n = 0)
    (haa : ∀ j, 0 < j → j < n → B j ea ea = u (j - 1))
    (hbb : ∀ j, 0 < j → j < n → B j eb eb = u (j + 1))
    (hab : ∀ j, 0 < j → j < n → B j ea eb = u j)
    (hha : ∀ j, 0 < j → j < n → B j (old v) ea = S j v)
    (hhb : ∀ j, 0 < j → j < n → B j (old v) eb = S (j + 1) v) :
    2 * (∑ j ∈ Finset.range (n + 1), u j * pairCoefficient S u v j ^ 2) ≤
      -(∑ j ∈ Finset.range (n + 1), (j : ℝ) * ((n : ℝ) - j) * B j (old v) (old v)) := by
  let g := pairCoefficient S u v
  have hrepr {j : ℕ} (hj : j ≤ n) : u j * g j = pairCumulative S v j :=
    pairCoefficient_represents_le S u n v huint hbalance hj
  have hu_nonneg {j : ℕ} (hj : j ≤ n) : 0 ≤ u j := by
    by_cases hj0 : j = 0
    · simp [hj0, hu0]
    by_cases hjn : j = n
    · simp [hjn, hun]
    exact le_of_lt (huint j (by omega) (by omega))
  apply weighted_second_differences_bound
    (fun j => u j * g j ^ 2) (fun j => B j (old v) (old v)) n
    (by simp [hu0]) (by simp [hun])
  intro j hj0 hjn
  have hleft : B j (old v) ea = u j * g j - u (j - 1) * g (j - 1) := by
    rw [hha j hj0 hjn, hrepr (by omega), hrepr (by omega)]
    exact (pairCumulative_difference S v hj0).symm
  have hright : B j (old v) eb = u (j + 1) * g (j + 1) - u j * g j := by
    rw [hhb j hj0 hjn, hrepr (by omega), hrepr (by omega), pairCumulative_succ]
    ring
  have hpositive : 0 < u (j - 1) ∨ 0 < u (j + 1) ∨
      (u (j - 1) = 0 ∧ u (j + 1) = 0 ∧ 0 < u j) := by
    by_cases hm : 0 < u (j - 1)
    · exact Or.inl hm
    by_cases hp : 0 < u (j + 1)
    · exact Or.inr (Or.inl hp)
    exact Or.inr (Or.inr ⟨le_antisymm (le_of_not_gt hm) (hu_nonneg (by omega)),
      le_antisymm (le_of_not_gt hp) (hu_nonneg (by omega)), huint j hj0 hjn⟩)
  simpa only [mul_assoc] using pair_step_of_signature (B j) (hsymm j hj0 hjn) (hsig j hj0 hjn)
    (old v) ea eb (u (j - 1)) (u j) (u (j + 1)) (g (j - 1)) (g j) (g (j + 1))
    (haa j hj0 hjn) (hbb j hj0 hjn) (hab j hj0 hjn) hleft hright
    (hu_nonneg (by omega)) (hu_nonneg (by omega)) hpositive

end Closure

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FactorialSignatures
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Factorial congruence for the two binary lifts

The integer-to-binary signature transfer in paper 200-02,
Lemma `lem:binary-signatures`. Coordinates with zero remaining copies
are allowed; a single remaining copy gives an invalid repeated removal.
The copy matrix is proved to be dominated by the integer form compressed
to group means. The difference is the nonnegative within-group variance.
-/

namespace ContingencyTables.FactorialSignatures

open scoped BigOperators Classical Matrix
open LinearMap (BilinForm)
open CommonBasesFPRAS

/-- Domination by a compressed one-positive form preserves the signature.
This is the precise group-mean argument, including forms with no positive direction. -/
theorem onePositive_of_dominated_compression
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (B : BilinForm ℝ V) (C : BilinForm ℝ W) (L : W →ₗ[ℝ] V)
    (hsymm : ∀ x y, C x y = C y x) (hsig : OnePositiveDirection B)
    (hdom : ∀ v, C v v ≤ B (L v) (L v)) : OnePositiveDirection C := by
  by_cases hpos : ∃ u, 0 < C u u
  · obtain ⟨u, hu⟩ := hpos
    apply onePositiveDirection_of_kernel C hsymm ((B (L u)).comp L)
    intro v hv
    exact (hdom v).trans (hsig (L u) (lt_of_lt_of_le hu (hdom u)) (L v) hv)
  · intro u hu
    exact False.elim (hpos ⟨u, hu⟩)

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- Raw integer signatures imply signatures of the actual copy matrix.
Zero groups are harmless and single-copy groups require no division argument. -/
theorem copyMatrix_onePositive (n : G → ℕ) (H : Matrix G G ℝ) (c : ℝ)
    (hc : 0 < c) (hH : ∀ u v, H u v = H v u)
    (hsig : OnePositiveDirection H.toBilin') (hdiag : ∀ u, 0 ≤ H u u) :
    OnePositiveDirection (copyMatrix n H c).toBilin' := by
  have hcSig : OnePositiveDirection (c • H.toBilin') := by
    intro u hu v hv
    simp only [LinearMap.smul_apply, smul_eq_mul] at hu hv ⊢
    have hu' : 0 < H.toBilin' u u := pos_of_mul_pos_right hu hc.le
    have hv' : H.toBilin' u v = 0 := (mul_eq_zero.mp hv).resolve_left (ne_of_gt hc)
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (hsig u hu' v hv')
  have hsymm : ∀ i j, copyMatrix n H c i j = copyMatrix n H c j i := by
    intro i j
    simp only [copyMatrix, normalizedMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply, groupOuter]
    rw [hH]
    simp only [mul_comm (n i.1 : ℝ) (n j.1 : ℝ)]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro u _
      ring
    · by_cases hij : i = j
      · subst j; rfl
      · simp [hij, Ne.symm hij]
  apply onePositive_of_dominated_compression (c • H.toBilin') _ (groupAverage n)
    (fun x y => (matrix_bilin_symm _ hsymm).eq x y) hcSig
  intro x
  rw [copyMatrix_form]
  change _ ≤ c * H.toBilin' (groupAverage n x) (groupAverage n x)
  apply sub_le_self
  apply Finset.sum_nonneg
  intro u _
  apply mul_nonneg _ (within_variance_nonnegative (n u) (fun i => x ⟨u, i⟩))
  exact div_nonneg (mul_nonneg hc.le (hdiag u)) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

omit [DecidableEq G] in
lemma factorialProduct_positive (n : G → ℕ) : 0 < factorialProduct n := by
  apply Finset.prod_pos
  intro u _
  exact_mod_cast Nat.factorial_pos (n u)

/-- Removing one labeled copy cancels precisely its coordinate count. -/
lemma factorialProduct_removeOne (n : G → ℕ) (u : G) (hu : 0 < n u) :
    factorialProduct (removeOne n u) = factorialProduct n / n u := by
  have hnu : (n u : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hu
  apply (eq_div_iff hnu).mpr
  unfold factorialProduct
  rw [← Finset.mul_prod_erase Finset.univ (fun v => ((removeOne n u v).factorial : ℝ))
    (Finset.mem_univ u),
    ← Finset.mul_prod_erase Finset.univ (fun v => ((n v).factorial : ℝ)) (Finset.mem_univ u)]
  have hrest : (∏ v ∈ Finset.univ.erase u, ((removeOne n u v).factorial : ℝ)) =
      ∏ v ∈ Finset.univ.erase u, ((n v).factorial : ℝ) := by
    apply Finset.prod_congr rfl
    intro v hv
    simp [removeOne, (Finset.mem_erase.mp hv).1]
  rw [hrest]
  have hfac : (n u : ℝ) * ((n u - 1).factorial : ℝ) = (n u).factorial := by
    exact_mod_cast Nat.mul_factorial_pred (Nat.ne_of_gt hu)
  simp only [removeOne, ite_true, if_true]
  calc
    _ = ((n u : ℝ) * ((n u - 1).factorial : ℝ)) *
        ∏ v ∈ Finset.univ.erase u, ((n v).factorial : ℝ) := by ring
    _ = _ := by rw [hfac]

/-- Two factorial reductions yield the exact cross-group or repeated-group
multiplicity denominator. -/
theorem factorialProduct_removeTwo (n : G → ℕ) (u v : G)
    (hu : 0 < n u) (hv : 0 < n v - if v = u then 1 else 0) :
    factorialProduct (removeTwo n u v) = factorialProduct n /
      ((n u : ℝ) * (if u = v then ((n u - 1 : ℕ) : ℝ) else n v)) := by
  rw [removeTwo, factorialProduct_removeOne _ v hv, factorialProduct_removeOne n u hu]
  by_cases huv : u = v
  · subst v
    simp only [removeOne, ite_true, if_true, div_div]
  · simp [removeOne, huv, Ne.symm huv, div_div]


noncomputable def factorialMatrix (n : G → ℕ) (H : Matrix G G ℝ) (D : ℝ) :
    Matrix (Copies n) (Copies n) ℝ := fun i j => if i = j then 0 else
      H i.1 j.1 * factorialProduct (removeTwo n i.1 j.1) / D

/-- Exact factorial congruence with the normalized integer matrix. -/
theorem factorialMatrix_eq (n : G → ℕ) (H : Matrix G G ℝ) (D : ℝ)
    (hzero : ∀ u, n u < 2 → H u u = 0) :
    factorialMatrix n H D = copyMatrix n H (factorialProduct n / D) := by
  ext i j
  rw [copyMatrix_apply n H _ hzero]
  by_cases hij : i = j
  · simp [factorialMatrix, hij]
  obtain ⟨hi, hj⟩ := distinct_copy_counts n i j hij
  simp only [factorialMatrix, hij, ite_false]
  rw [factorialProduct_removeTwo n i.1 j.1 hi hj]
  ring

/-- The literal factorial weights have the binary signature implied by
their integer two-removal or remaining-capacity addition matrix. -/
theorem factorialMatrix_onePositive (n : G → ℕ) (H : Matrix G G ℝ) (D : ℝ)
    (hD : 0 < D) (hH : ∀ u v, H u v = H v u)
    (hsig : OnePositiveDirection H.toBilin') (hdiag : ∀ u, 0 ≤ H u u)
    (hzero : ∀ u, n u < 2 → H u u = 0) :
    OnePositiveDirection (factorialMatrix n H D).toBilin' := by
  rw [factorialMatrix_eq n H D hzero]
  exact copyMatrix_onePositive n H _ (div_pos (factorialProduct_positive n) hD) hH hsig hdiag

noncomputable def removalLiftMatrix (h : (G → ℕ) → ℝ) (n : G → ℕ) (D : ℝ) :
    Matrix (Copies n) (Copies n) ℝ := fun i j => if i = j then 0 else
      h (removeTwo n i.1 j.1) * factorialProduct (removeTwo n i.1 j.1) / D

/-- The actual omission matrix of the first factorial lift, with all
integer invalid-removal entries set to zero. -/
theorem removalLift_onePositive (h : (G → ℕ) → ℝ) (n : G → ℕ) (D : ℝ)
    (hD : 0 < D) (hh : ∀ r, 0 ≤ h r)
    (hsig : OnePositiveDirection (integerRemovalMatrix h n).toBilin') :
    OnePositiveDirection (removalLiftMatrix h n D).toBilin' := by
  have heq : removalLiftMatrix h n D = factorialMatrix n (integerRemovalMatrix h n) D := by
    ext i j
    by_cases hij : i = j
    · simp [removalLiftMatrix, factorialMatrix, hij]
    have hv := distinct_copy_counts n i j hij
    simp [removalLiftMatrix, factorialMatrix, hij, integerRemovalMatrix, ValidPair, hv]
  rw [heq]
  apply factorialMatrix_onePositive n _ D hD
  · intro u v
    simp only [integerRemovalMatrix, validPair_symm n u v, removeTwo_comm n u v]
  · exact hsig
  · intro u
    unfold integerRemovalMatrix
    split_ifs <;> simp [hh]
  · intro u hu
    have hn : ¬ValidPair n u u := by simp [ValidPair]; omega
    simp [integerRemovalMatrix, hn]

noncomputable def integerAdditionMatrix (h : (G → ℕ) → ℝ) (r n : G → ℕ) : Matrix G G ℝ :=
  fun u v => if ValidPair n u v then h (addTwo r u v) else 0

noncomputable def additionLiftMatrix (h : (G → ℕ) → ℝ) (r n : G → ℕ) (D : ℝ) :
    Matrix (Copies n) (Copies n) ℝ := fun i j => if i = j then 0 else
      h (addTwo r i.1 j.1) * factorialProduct (removeTwo n i.1 j.1) / D

end ContingencyTables.FactorialSignatures

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerWeightedTransport
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual weighted integer pair estimate

For first-paper transport the pair display has total B+1 and capacity B,
so only the interior matrices are valid. The potential identity uses
exactly those matrices and the actual cumulative cross entries; it never
assumes an endpoint matrix signature.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The D'=B+1 weighted estimate for the actual raw integer removal forms.
The required balance is the zero total signed cross flow at the pair. -/
theorem weighted_pair_potential
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) (v : I → ℝ)
    (hsig : ∀ j, 0 < j → j < M →
      OnePositiveDirection (integerRemovalMatrix F (profile z j (M-j))).toBilin')
    (hpos : ∀ j, 0 < j → j < M → 0 < F (profile z (j-1) (M-1-j)))
    (hbalance : pairCumulative (cross F M z) v M = 0) :
    2*(∑ j ∈ Finset.range (M+1), innerWeight F M z j *
      pairCoefficient (cross F M z) (innerWeight F M z) v j ^ 2) ≤
      -(∑ j ∈ Finset.range (M+1), (j:ℝ)*((M:ℝ)-j)*
        (pairMatrix F M z j).toBilin' (old v) (old v)) := by
  apply balancedPair_weighted_potential M (fun j => (pairMatrix F M z j).toBilin') old
    (Pi.single (.inr false) 1) (Pi.single (.inr true) 1) (cross F M z) (innerWeight F M z) v
  · intro j _ _ x y
    exact (matrix_bilin_symm _ (integerRemoval_symm _ _)).eq x y
  · exact hsig
  · simp [innerWeight]
  · simp [innerWeight]
  · intro j hj0 hjM
    have ht : 0 < j ∧ j < M := ⟨hj0,hjM⟩
    simpa only [innerWeight,ite_eq_left ht] using hpos j hj0 hjM
  · exact hbalance
  · intro j _ hjM; simpa using pairMatrix_aa F M z j hjM.le
  · intro j _ hjM; simpa using pairMatrix_bb F M z j hjM.le
  · intro j _ hjM; simpa using pairMatrix_ab F M z j hjM.le
  · intro j _ hjM; exact cross_a F M z j hjM.le v
  · intro j _ hjM; exact cross_b F M z j hjM.le v

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerFutureSquare
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integer transport recursion's future square identity

The three new--new removal entries partition by the same resulting pair.
Their coefficients give an exact nonnegative square, without a signature
assumption on the weighted future form.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
lemma future_aa (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (n j : ℕ) :
    pairMatrix F (n+2) z j (.inr false) (.inr false) =
      if 2 ≤ j then F (profile z (j-2) (n+2-j)) else 0 := by
  have hv : ValidPair (profile z j (n+2-j)) (.inr false) (.inr false) ↔ 2 ≤ j := by
    simp [ValidPair, profile]; omega
  unfold IntegerMarginal.pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl, profile_removeAA]

omit [Fintype I] in
lemma future_bb (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (n j : ℕ) :
    pairMatrix F (n+2) z j (.inr true) (.inr true) =
      if j ≤ n then F (profile z j (n-j)) else 0 := by
  have hv : ValidPair (profile z j (n+2-j)) (.inr true) (.inr true) ↔ j ≤ n := by
    simp [ValidPair, profile]; omega
  unfold IntegerMarginal.pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl, profile_removeBB]
  split_ifs <;> congr 1
  congr 1
  omega

omit [Fintype I] in
lemma future_ab (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (n j : ℕ) :
    pairMatrix F (n+2) z j (.inr false) (.inr true) =
      if 1 ≤ j ∧ j ≤ n+1 then F (profile z (j-1) (n+1-j)) else 0 := by
  have hv : ValidPair (profile z j (n+2-j)) (.inr false) (.inr true) ↔
      1 ≤ j ∧ j ≤ n+1 := by
    simp [ValidPair, profile]; omega
  unfold IntegerMarginal.pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl, profile_removeAB]
  split_ifs <;> congr 1
  congr 1
  omega

omit [Fintype I] in
/-- The exact new--new part of the future correction: two diagonal
removals and the mixed removal of the same integer pair form a square. -/
theorem future_new_square
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (n : ℕ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n+3),
      (pairMatrix F (n+2) z j (.inr false) (.inr false) * g j ^ 2 -
      2 * pairMatrix F (n+2) z j (.inr false) (.inr true) * g j * g (j+1) +
      pairMatrix F (n+2) z j (.inr true) (.inr true) * g (j+1) ^ 2)) =
      ∑ k ∈ Finset.range (n+1), F (profile z k (n-k)) * (g (k+2)-g (k+1)) ^ 2 := by
  have haa : (∑ j ∈ Finset.range (n+3),
      pairMatrix F (n+2) z j (.inr false) (.inr false) * g j ^ 2) =
      ∑ k ∈ Finset.range (n+1), F (profile z k (n-k)) * g (k+2) ^ 2 := by
    convert sum_range_shift (n+1) 2 (fun k => F (profile z k (n-k)) * g (k+2)^2) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro j _
    rw [future_aa]
    split_ifs with hj
    · rw [show j-2+2 = j by omega, show n-(j-2) = n+2-j by omega]
    · simp
  have hbb : (∑ j ∈ Finset.range (n+3),
      pairMatrix F (n+2) z j (.inr true) (.inr true) * g (j+1) ^ 2) =
      ∑ k ∈ Finset.range (n+1), F (profile z k (n-k)) * g (k+1) ^ 2 := by
    convert sum_range_truncate (n+1) 2 (fun k => F (profile z k (n-k)) * g (k+1)^2) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro j _
    rw [future_bb]
    by_cases hj : j ≤ n
    · simp [hj, show j < n+1 by omega]
    · simp [hj, show ¬j < n+1 by omega]
  have hab : (∑ j ∈ Finset.range (n+3),
      2 * pairMatrix F (n+2) z j (.inr false) (.inr true) * g j * g (j+1)) =
      ∑ k ∈ Finset.range (n+1), 2 * F (profile z k (n-k)) * g (k+1) * g (k+2) := by
    convert sum_middle_shift n (fun k => 2 * F (profile z k (n-k)) * g (k+1) * g (k+2)) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro j _
    rw [future_ab]
    split_ifs with hj
    · rw [show j-1+1 = j by omega, show j-1+2 = j+1 by omega,
        show n-(j-1) = n+1-j by omega]
    · simp
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, haa, hab, hbb,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring


/-- The two mixed old--new sums telescope, including both invalid
endpoint removals. -/
theorem future_mixed_cancel
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (M : ℕ)
    (h : I → ℝ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (M+1),
      ((pairMatrix F M z j).toBilin' (old h) (Pi.single (.inr false) 1) * g j -
      (pairMatrix F M z j).toBilin' (old h) (Pi.single (.inr true) 1) * g (j+1))) = 0 := by
  calc
    _ = ∑ j ∈ Finset.range (M+1), (cross F M z j h * g j -
          cross F M z (j+1) h * g (j+1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjM : j ≤ M := by have := Finset.mem_range.mp hj; omega
      rw [cross_a F M z j hjM, cross_b F M z j hjM]
    _ = cross F M z 0 h * g 0 - cross F M z (M+1) h * g (M+1) :=
      Finset.sum_range_sub' (fun j => cross F M z j h * g j) (M+1)
    _ = 0 := by simp [cross]

/-- Old--old entries partition the parent's balanced marginal exactly. -/
theorem future_old_sum
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (M : ℕ) (h : I → ℝ) :
    (∑ j ∈ Finset.range (M+1), (pairMatrix F M z j).toBilin' (old h) (old h)) =
      (integerRemovalMatrix (marginal F M) z).toBilin' h h := by
  rw [marginal_old_block]
  simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply]


noncomputable def extendCoefficients (h : I → ℝ) (a b : ℝ) : I ⊕ Bool → ℝ :=
  old h + a • Pi.single (.inr false) 1 - b • Pi.single (.inr true) 1


omit [Fintype I] in
@[simp] lemma extendCoefficients_inl (h : I → ℝ) (a b : ℝ) (i : I) :
    extendCoefficients h a b (.inl i) = h i := by
  simp [extendCoefficients, old]

omit [Fintype I] in
@[simp] lemma extendCoefficients_a (h : I → ℝ) (a b : ℝ) :
    extendCoefficients h a b (.inr false) = a := by
  simp [extendCoefficients, old]

omit [Fintype I] in
@[simp] lemma extendCoefficients_b (h : I → ℝ) (a b : ℝ) :
    extendCoefficients h a b (.inr true) = -b := by
  simp [extendCoefficients, old]

lemma extended_quadratic (B : Matrix (I ⊕ Bool) (I ⊕ Bool) ℝ)
    (hB : ∀ i j, B i j = B j i) (h : I → ℝ) (a b : ℝ) :
    B.toBilin' (extendCoefficients h a b) (extendCoefficients h a b) =
      B.toBilin' (old h) (old h) +
      2 * (B.toBilin' (old h) (Pi.single (.inr false) 1) * a -
        B.toBilin' (old h) (Pi.single (.inr true) 1) * b) +
      (B (.inr false) (.inr false) * a^2 -
        2 * B (.inr false) (.inr true) * a * b + B (.inr true) (.inr true) * b^2) := by
  have hs := matrix_bilin_symm B hB
  unfold extendCoefficients
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  rw [hs.eq (Pi.single (.inr false) 1) (old h),
    hs.eq (Pi.single (.inr true) 1) (old h)]
  simp only [Matrix.toBilin'_single]
  rw [hB (.inr true) (.inr false)]
  ring

/-- Equation future-square of the first manuscript for actual integer
removal matrices. The parent is the balanced raw marginal. -/
theorem future_square_identity
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (n : ℕ)
    (h : I → ℝ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n+3),
      (pairMatrix F (n+2) z j).toBilin'
        (extendCoefficients h (g j) (g (j+1))) (extendCoefficients h (g j) (g (j+1)))) -
      (integerRemovalMatrix (marginal F (n+2)) z).toBilin' h h =
    ∑ k ∈ Finset.range (n+1), F (profile z k (n-k)) * (g (k+2)-g (k+1))^2 := by
  simp_rw [extended_quadratic (pairMatrix F (n+2) z _) (integerRemoval_symm F _) h]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    future_mixed_cancel, mul_zero, add_zero]
  rw [show n+3 = (n+2)+1 by omega, future_old_sum]
  rw [show n+2+1 = n+3 by omega, future_new_square]
  ring

/-- Processing an ordinary integer pair can only increase a future form.
No signature assertion about the weighted future kernel is required. -/
theorem future_form_monotone
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (n : ℕ)
    (h : I → ℝ) (g : ℕ → ℝ) (hF : ∀ p, 0 ≤ F p) :
    (integerRemovalMatrix (marginal F (n+2)) z).toBilin' h h ≤
      ∑ j ∈ Finset.range (n+3), (pairMatrix F (n+2) z j).toBilin'
        (extendCoefficients h (g j) (g (j+1))) (extendCoefficients h (g j) (g (j+1))) := by
  apply sub_nonneg.mp
  rw [future_square_identity]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hF _) (sq_nonneg _))

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerFutureKernel
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The weighted future-slot kernel

Weights a(M-a) are used inside the finite box 0≤a≤M. The common
nonnegative kernel identifies the integer transport's future correction
matrix.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def weightedFuture (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) : ℝ :=
  ∑ a ∈ Finset.range (M+1), (a:ℝ)*((M:ℝ)-a)*F (profile z a (M-a))

omit [Fintype I] [DecidableEq I] in
lemma weightedFuture_nonnegative (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ)
    (hF : ∀ p, 0 ≤ F p) (z : I → ℕ) : 0 ≤ weightedFuture F M z := by
  apply Finset.sum_nonneg
  intro a ha
  have haM : a ≤ M := by have := Finset.mem_range.mp ha; omega
  have haR : (a:ℝ) ≤ M := by exact_mod_cast haM
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr haR)) (hF _)

omit [Fintype I] in
/-- Weighted future matrices are the old block of the literal common
kernel. This is an equality, with no one-positive-direction hypothesis. -/
theorem weightedFuture_matrix (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) :
    integerRemovalMatrix (weightedFuture F M) z =
      ∑ a ∈ Finset.range (M+1), ((a:ℝ)*((M:ℝ)-a)) •
        (pairMatrix F M z a).submatrix Sum.inl Sum.inl := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.submatrix_apply, pairMatrix_old, integerRemovalMatrix, weightedFuture]
  split_ifs <;> simp

/-- The scalar correction Q_t is exactly the weighted two-old-hole sum. -/
theorem weightedFuture_form (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ)
    (z : I → ℕ) (h : I → ℝ) :
    (integerRemovalMatrix (weightedFuture F M) z).toBilin' h h =
      ∑ a ∈ Finset.range (M+1), (a:ℝ)*((M:ℝ)-a)*
        (pairMatrix F M z a).toBilin' (old h) (old h) := by
  rw [weightedFuture_matrix]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [old_old]

omit [Fintype I] [DecidableEq I] in
lemma profile_swap (z : I → ℕ) (j k a b : ℕ) :
    (fun t => profile (profile z a b) j k (swapPairs t)) =
      profile (profile z j k) a b := by
  funext t
  rcases t with (i | c) | c <;> rfl

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerSliceReindex
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Raw integer removal slices under coordinate bijections -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal BalancedBox BinaryContraction

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]

omit [Fintype C] [Fintype D] in
lemma removeOne_reindex (e : C ≃ D) (z : C → ℕ) (i : C) :
    (removeOne z i) ∘ e.symm = removeOne (z ∘ e.symm) (e i) := by
  funext d
  simp only [Function.comp_apply, removeOne]
  by_cases hd : d = e i
  · subst d
    simp
  · have hi : e.symm d ≠ i := by
      intro hi
      apply hd
      simpa only [Equiv.apply_symm_apply] using congrArg e hi
    simp only [hd, hi, ↓reduceIte]

omit [Fintype C] [Fintype D] in
lemma removeTwo_reindex (e : C ≃ D) (z : C → ℕ) (i j : C) :
    (removeTwo z i j) ∘ e.symm = removeTwo (z ∘ e.symm) (e i) (e j) := by
  simp only [removeTwo, removeOne_reindex]

omit [Fintype C] [Fintype D] in
lemma removalMatrix_reindex (e : C ≃ D) (F : (D → ℕ) → ℝ) (z : C → ℕ) :
    integerRemovalMatrix (fun x => F (x ∘ e.symm)) z =
      (integerRemovalMatrix F (z ∘ e.symm)).submatrix e e := by
  ext i j
  have hv : ValidPair (z ∘ e.symm) (e i) (e j) ↔ ValidPair z i j := by
    simp [ValidPair]
  change (if ValidPair z i j then F (removeTwo z i j ∘ e.symm) else 0) =
    if ValidPair (z ∘ e.symm) (e i) (e j) then
      F (removeTwo (z ∘ e.symm) (e i) (e j)) else 0
  simp only [hv, removeTwo_reindex]

omit [DecidableEq C] [DecidableEq D] in
lemma positiveSlice_reindex (e : C ≃ D) (F : (D → ℕ) → ℝ) (m : D → ℕ) (R : ℕ)
    (hF : PositiveSlice F m R) :
    PositiveSlice (fun x => F (x ∘ e.symm)) (m ∘ e) R := by
  intro z hz ht
  apply hF
  · intro d
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hz (e.symm d)
  · have he := e.sum_comp (fun d => z (e.symm d))
    simp only [Equiv.symm_apply_apply] at he
    exact he.symm.trans ht

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerExposure
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exposing an ordinary pair in the actual balanced marginal

Moving one pair into the retained coordinates changes only the coordinate
bijection. The remaining finite assignment sum is the same, so the actual
balanced marginal partitions into precisely the U+1 child families.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open BalancedFamily BalancedEnumeration IntegerMarginal

universe u

/-- Move the outermost pair inside all the other still-summed pairs. -/
def exposeEquiv {I : Type u} : (Ms : List ℕ) →
    Coordinates (I ⊕ Bool) Ms ≃ Coordinates I Ms ⊕ Bool
  | [] => Equiv.refl _
  | _::Ms => (Equiv.sumCongr (exposeEquiv (I := I) Ms) (Equiv.refl Bool)).trans swapPairs

lemma expose_embedding {I : Type*} (Ms : List ℕ) (z : I → ℕ) (a b : ℕ)
    (u : Assignments Ms) :
    (fun t => embedding Ms (profile z a b) u ((exposeEquiv (I := I) Ms).symm t)) =
      profile (embedding Ms z u) a b := by
  induction Ms with
  | nil => rfl
  | cons M Ms ih =>
    funext t
    rcases t with (i | c) | c
    · change embedding Ms (profile z a b) u.1 ((exposeEquiv (I := I) Ms).symm (.inl i)) =
        embedding Ms z u.1 i
      exact congrFun (ih u.1) (.inl i)
    · cases c <;> rfl
    · change embedding Ms (profile z a b) u.1 ((exposeEquiv (I := I) Ms).symm (.inr c)) = _
      exact congrFun (ih u.1) (.inr c)

noncomputable def exposedFamily {I : Type*} (Ms : List ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ) : ((I ⊕ Bool) → ℕ) → ℝ :=
  eliminate Ms (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))

/-- The literal child family sums back to its actual parent; the domain
is the same Cartesian product of all remaining balanced profiles. -/
theorem exposed_marginal {I : Type*} (Ms : List ℕ) (U : ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ) :
    marginal (exposedFamily Ms F) U = eliminate (U::Ms) F := by
  funext z
  change (∑ j ∈ Finset.range (U+1), exposedFamily Ms F (profile z j (U-j))) =
    eliminate Ms (marginal F U) z
  simp only [exposedFamily, eliminate_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  unfold marginal
  apply Finset.sum_congr rfl
  intro j _
  rw [expose_embedding]


lemma expose_bounds {I : Type*} (Ms : List ℕ) (m : I → ℕ) (U : ℕ) :
    (fun t => bounds (profile m U U) Ms ((exposeEquiv (I := I) Ms).symm t)) =
      profile (bounds m Ms) U U := by
  induction Ms with
  | nil => rfl
  | cons M Ms ih =>
    funext t
    rcases t with (i | c) | c
    · change bounds (profile m U U) Ms ((exposeEquiv (I := I) Ms).symm (.inl i)) = bounds m Ms i
      exact congrFun ih (.inl i)
    · cases c <;> rfl
    · change bounds (profile m U U) Ms ((exposeEquiv (I := I) Ms).symm (.inr c)) = _
      exact congrFun ih (.inr c)


lemma expose_bounds_forward {I : Type*} (Ms : List ℕ) (m : I → ℕ) (U : ℕ) :
    (profile (bounds m Ms) U U) ∘ exposeEquiv (I := I) Ms = bounds (profile m U U) Ms := by
  funext t
  have he := congrFun (expose_bounds Ms m U) (exposeEquiv (I := I) Ms t)
  simpa only [Equiv.symm_apply_apply, Function.comp_apply] using he.symm


theorem expose_source_positive {I : Type*} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (U : ℕ) (m : I → ℕ) (R : ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ)
    (hpos : BalancedBox.PositiveSlice F (profile (bounds m Ms) U U) (R+U+Ms.sum)) :
    BalancedBox.PositiveSlice (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (bounds (profile m U U) Ms) (R+U+Ms.sum) := by
  have hp := positiveSlice_reindex (exposeEquiv (I := I) Ms) F (profile (bounds m Ms) U U)
    (R+U+Ms.sum) hpos
  rw [expose_bounds_forward] at hp
  exact hp

theorem eliminate_positive {I : Type*} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (m : I → ℕ) (R : ℕ) (F : (Coordinates I Ms → ℕ) → ℝ)
    (hpos : BalancedBox.PositiveSlice F (bounds m Ms) (R+Ms.sum)) :
    BalancedBox.PositiveSlice (eliminate Ms F) m R := by
  induction Ms with
  | nil => simpa only [List.sum_nil, add_zero, eliminate, bounds] using hpos
  | cons U Ms ih =>
    apply ih (marginal F U)
    apply BalancedBox.marginal_positive_slice F (bounds m Ms) (R+Ms.sum) U
    rw [show R+Ms.sum+U=R+(U::Ms).sum by simp only [List.sum_cons]; omega]
    exact hpos

theorem exposed_positive {I : Type*} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (U : ℕ) (m : I → ℕ) (R : ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ)
    (hpos : BalancedBox.PositiveSlice F (profile (bounds m Ms) U U) (R+U+Ms.sum)) :
    BalancedBox.PositiveSlice (exposedFamily Ms F) (profile m U U) (R+U) :=
  eliminate_positive Ms (profile m U U) (R+U) _ (expose_source_positive Ms U m R F hpos)

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerPairRecursion
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Balanced coefficients and the actual integer child potentials -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def oneHole (F : (I → ℕ) → ℝ) (z : I → ℕ) (i : I) : ℝ :=
  if 0 < z i then F (removeOne z i) else 0

omit [Fintype I] in
lemma profile_removeOne_old (z : I → ℕ) (a b : ℕ) (i : I) :
    removeOne (profile z a b) (.inl i) = profile (removeOne z i) a b := by
  funext t
  rcases t with k | (_ | _) <;> simp [profile, removeOne]

omit [Fintype I] in
lemma profile_removeOne_a (z : I → ℕ) (a b : ℕ) :
    removeOne (profile z a b) (.inr false) = profile z (a-1) b := by
  funext t
  rcases t with k | (_ | _) <;> simp [profile, removeOne]

omit [Fintype I] in
lemma profile_removeOne_b (z : I → ℕ) (a b : ℕ) :
    removeOne (profile z a b) (.inr true) = profile z a (b-1) := by
  funext t
  rcases t with k | (_ | _) <;> simp [profile, removeOne]

omit [Fintype I] in
lemma old_hole_sum (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ)
    (U : ℕ) (i : I) :
    (∑ j ∈ Finset.range (U+1), oneHole F (profile z j (U-j)) (.inl i)) =
      oneHole (marginal F U) z i := by
  simp only [oneHole, profile_removeOne_old]
  change (∑ j ∈ Finset.range (U+1), if 0 < z i then
    F (profile (removeOne z i) j (U-j)) else 0) =
      if 0 < z i then marginal F U (removeOne z i) else 0
  by_cases hp : 0 < z i <;> simp [hp, marginal]

omit [Fintype I] in
lemma child_hole_a (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ)
    (U j : ℕ) (hj : j ≤ U) :
    oneHole F (profile z j (U-j)) (.inr false) = innerWeight F (U+1) z j := by
  unfold oneHole
  rw [profile_removeOne_a]
  change (if 0 < j then F (profile z (j-1) (U-j)) else 0) = _
  unfold innerWeight
  by_cases hp : 0 < j
  · rw [ite_eq_left hp, ite_eq_left (by omega)]
    congr 1
  · rw [ite_eq_right hp, ite_eq_right (by omega)]

omit [Fintype I] in
lemma child_hole_b (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ)
    (U j : ℕ) (hj : j ≤ U) :
    oneHole F (profile z j (U-j)) (.inr true) = innerWeight F (U+1) z (j+1) := by
  unfold oneHole
  rw [profile_removeOne_b]
  change (if 0 < U-j then F (profile z j (U-j-1)) else 0) = _
  unfold innerWeight
  by_cases hp : j < U
  · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    simp only [Nat.add_sub_cancel]
    congr 1
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma child_old_signed_mass (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ)
    (U j : ℕ) (hj : j ≤ U) (h : I → ℝ) :
    (∑ i, oneHole F (profile z j (U-j)) (.inl i) * h i) = cross F (U+1) z (j+1) h := by
  rw [← cross_a F (U+1) z (j+1) (by omega), old_single]
  apply Finset.sum_congr rfl
  intro i _
  have hv : ValidPair (profile z (j+1) (U+1-(j+1))) (.inl i) (.inr false) ↔ 0 < z i := by
    simp [ValidPair, profile]
  unfold IntegerMarginal.pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl, profile_removeOldA]
  unfold oneHole
  rw [profile_removeOne_old]
  simp only [Nat.add_sub_cancel, Nat.add_sub_add_right]
  change (if 0 < z i then F (profile (removeOne z i) j (U-j)) else 0) * h i =
    h i * (if 0 < z i then F (profile (removeOne z i) j (U-j)) else 0)
  exact mul_comm _ _

/-- The cumulative coefficients balance every integer child, including
zero-capacity endpoint removals. -/
theorem integer_child_balance
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (U j : ℕ) (hj : j ≤ U)
    (h : I → ℝ)
    (hpos : ∀ k, 0 < k → k < U+1 → 0 < innerWeight F (U+1) z k)
    (hbal : pairCumulative (cross F (U+1) z) h (U+1) = 0) :
    let g := pairCoefficient (cross F (U+1) z) (innerWeight F (U+1) z) h
    ∑ i : I ⊕ Bool, oneHole F (profile z j (U-j)) i *
      extendCoefficients h (g j) (g (j+1)) i = 0 := by
  dsimp only
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, extendCoefficients_inl,
    extendCoefficients_a, extendCoefficients_b, mul_neg]
  rw [child_old_signed_mass F z U j hj, child_hole_a F z U j hj, child_hole_b F z U j hj]
  rw [pairCoefficient_represents_le _ _ (U+1) h hpos hbal (by omega),
    pairCoefficient_represents_le _ _ (U+1) h hpos hbal (by omega)]
  rw [pairCumulative_succ]
  ring


noncomputable def holePotential (F : (I → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ) : ℝ :=
  ∑ i, oneHole F z i * h i ^ 2

lemma child_potential (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ)
    (U j : ℕ) (hj : j ≤ U) (h : I → ℝ) (g : ℕ → ℝ) :
    holePotential F (profile z j (U-j)) (extendCoefficients h (g j) (g (j+1))) =
      (∑ i, oneHole F (profile z j (U-j)) (.inl i) * h i ^ 2) +
      (innerWeight F (U+1) z j * g j ^ 2 + innerWeight F (U+1) z (j+1) * g (j+1) ^ 2) := by
  simp only [holePotential, Fintype.sum_sum_type, Fintype.sum_bool,
    extendCoefficients_inl, extendCoefficients_a, extendCoefficients_b, neg_sq]
  rw [child_hole_a F z U j hj, child_hole_b F z U j hj]
  ring

/-- The old potential partitions and the two fresh-hole contributions
have identical sums, including both invalid endpoint holes. -/
theorem integer_potential_increment
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (U : ℕ)
    (h : I → ℝ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (U+1),
      holePotential F (profile z j (U-j)) (extendCoefficients h (g j) (g (j+1)))) =
      holePotential (marginal F U) z h +
        2 * ∑ j ∈ Finset.range (U+2), innerWeight F (U+1) z j * g j ^ 2 := by
  have hold : (∑ j ∈ Finset.range (U+1),
      ∑ i, oneHole F (profile z j (U-j)) (.inl i) * h i ^ 2) =
      holePotential (marginal F U) z h := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, old_hole_sum]
    rfl
  have hshift := Finset.sum_range_sub'
    (fun j => innerWeight F (U+1) z j * g j ^ 2) (U+1)
  rw [Finset.sum_sub_distrib] at hshift
  have hz0 : innerWeight F (U+1) z 0 = 0 := by simp [innerWeight]
  have hzM : innerWeight F (U+1) z (U+1) = 0 := by simp [innerWeight]
  rw [hz0, hzM, zero_mul, zero_mul, sub_self] at hshift
  have hend : (∑ j ∈ Finset.range (U+2), innerWeight F (U+1) z j * g j ^ 2) =
      ∑ j ∈ Finset.range (U+1), innerWeight F (U+1) z j * g j ^ 2 := by
    rw [show U+2 = (U+1)+1 by omega, Finset.sum_range_succ]
    simp [innerWeight]
  calc
    _ = (∑ j ∈ Finset.range (U+1),
        ((∑ i, oneHole F (profile z j (U-j)) (.inl i) * h i ^ 2) +
        (innerWeight F (U+1) z j * g j ^ 2 + innerWeight F (U+1) z (j+1) * g (j+1) ^ 2))) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact child_potential F z U j (by have := Finset.mem_range.mp hj; omega) h g
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hold, hend]
      linarith

/-- A split is controlled by the actual D'=U+1 integer removal forms.
These are precisely the interior signatures available in the manuscript. -/
theorem integer_split_potential_bound
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (U : ℕ) (h : I → ℝ)
    (hsig : ∀ j, 0 < j → j < U+1 →
      OnePositiveDirection (integerRemovalMatrix F (profile z j (U+1-j))).toBilin')
    (hpos : ∀ j, 0 < j → j < U+1 → 0 < F (profile z (j-1) (U-j)))
    (hbalance : pairCumulative (cross F (U+1) z) h (U+1) = 0) :
    let g := pairCoefficient (cross F (U+1) z) (innerWeight F (U+1) z) h
    (∑ j ∈ Finset.range (U+1),
      holePotential F (profile z j (U-j)) (extendCoefficients h (g j) (g (j+1)))) ≤
      holePotential (marginal F U) z h -
        ∑ j ∈ Finset.range (U+2), (j:ℝ)*(((U+1:ℕ):ℝ)-(j:ℝ)) *
          (pairMatrix F (U+1) z j).toBilin' (old h) (old h) := by
  dsimp only
  rw [integer_potential_increment]
  have hp := weighted_pair_potential F (U+1) z h hsig (by
    intro j hj0 hjU
    simpa only [Nat.add_sub_cancel] using hpos j hj0 hjU) hbalance
  linarith


noncomputable def holeLinear (G : (I → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ) : ℝ :=
  ∑ i, oneHole G z i * h i

/-- Equal resulting one-hole states cancel across adjacent branches.
The numerator family G may already include the arbitrary test function H. -/
theorem integer_demand_conservation
    (G : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (U : ℕ)
    (h : I → ℝ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (U+1),
      holeLinear G (profile z j (U-j)) (extendCoefficients h (g j) (g (j+1)))) =
      holeLinear (marginal G U) z h := by
  have hold : (∑ j ∈ Finset.range (U+1),
      ∑ i, oneHole G (profile z j (U-j)) (.inl i) * h i) =
      holeLinear (marginal G U) z h := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, old_hole_sum]
    rfl
  have hshift := Finset.sum_range_sub'
    (fun j => innerWeight G (U+1) z j * g j) (U+1)
  rw [Finset.sum_sub_distrib] at hshift
  have hzero0 : innerWeight G (U+1) z 0 = 0 := by simp [innerWeight]
  have hzeroM : innerWeight G (U+1) z (U+1) = 0 := by simp [innerWeight]
  rw [hzero0, hzeroM, zero_mul, zero_mul, sub_self] at hshift
  calc
    _ = ∑ j ∈ Finset.range (U+1),
        ((∑ i, oneHole G (profile z j (U-j)) (.inl i) * h i) +
        (innerWeight G (U+1) z j * g j - innerWeight G (U+1) z (j+1) * g (j+1))) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjU : j ≤ U := by have := Finset.mem_range.mp hj; omega
      simp only [holeLinear, Fintype.sum_sum_type, Fintype.sum_bool,
        extendCoefficients_inl, extendCoefficients_a, extendCoefficients_b, mul_neg]
      rw [child_hole_a G z U j hjU, child_hole_b G z U j hjU]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hold, hshift, add_zero]

/-- Parent balance is exactly the zero cumulative cross mass required
by the weighted pair theorem. -/
theorem cumulative_eq_parent_demand
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (U : ℕ) (h : I → ℝ) :
    pairCumulative (cross F (U+1) z) h (U+1) =
      holeLinear (marginal F U) z h := by
  unfold pairCumulative
  calc
    _ = ∑ j ∈ Finset.range (U+1), ∑ i, oneHole F (profile z j (U-j)) (.inl i) * h i := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (child_old_signed_mass F z U j (by have := Finset.mem_range.mp hj; omega) h).symm
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, old_hole_sum]
      rfl

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerLeafTransport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer leaf cliques, allowing invalid holes of zero weight -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open SignedTransport

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Instantiation at the actual one-removal weights of an integer display. -/
theorem integer_leaf_transport (F : (I → ℕ) → ℝ) (z : I → ℕ)
    (h H : I → ℝ) (hF : ∀ p, 0 ≤ F p)
    (hbalance : ∑ i, oneHole F z i * h i = 0) :
    (∑ i, oneHole F z i * h i * H i)^2 ≤
      holePotential F z h * cliqueEnergy (oneHole F z) (fun _ => 1) H := by
  exact raw_leaf_transport (oneHole F z) h H
    (fun i => by unfold oneHole; split_ifs; exact hF _; exact le_rfl) hbalance

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerRecursiveFlow
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual recursive signed integer demands

Every node exposes an ordinary balanced pair, computes the cumulative
coefficients from its actual remaining marginal, and retains the old
coefficients. The numerator can include any test function on complete
configurations. Its total leaf demand is exactly its root demand.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open BalancedFamily BalancedEnumeration IntegerMarginal

universe u

noncomputable def recursivePotential : {I : Type u} → [Fintype I] → [DecidableEq I] →
    (Ms : List ℕ) → ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → (I → ℝ) → ℝ
  | _, _, _, [], F, z, h => holePotential F z h
  | I, _, _, U::Ms, F, z, h =>
    let f := exposedFamily Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    ∑ j : Fin (U+1), recursivePotential Ms
      (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))

noncomputable def recursiveDemand : {I : Type u} → [Fintype I] → [DecidableEq I] →
    (Ms : List ℕ) → ((Coordinates I Ms → ℕ) → ℝ) →
    ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → (I → ℝ) → ℝ
  | _, _, _, [], _, G, z, h => holeLinear G z h
  | I, _, _, U::Ms, F, G, z, h =>
    let f := exposedFamily Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    ∑ j : Fin (U+1), recursiveDemand Ms
      (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (fun x => G (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))

/-- All auxiliary ordinary negative-pair divergences cancel in the
actual recursion. No limit of recursive coefficients is needed. -/
theorem recursiveDemand_eq : ∀ (Ms : List ℕ) {I : Type u} [Fintype I] [DecidableEq I]
    (F G : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ),
    recursiveDemand Ms F G z h = holeLinear (eliminate Ms G) z h := by
  intro Ms
  induction Ms with
  | nil => intro I _ _ F G z h; rfl
  | cons U Ms ih =>
    intro I _ _ F G z h
    let f := exposedFamily Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    change (∑ j : Fin (U+1), recursiveDemand Ms
      (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (fun x => G (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))) = _
    simp_rw [ih]
    change (∑ j : Fin (U+1), holeLinear (exposedFamily Ms G)
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))) = _
    rw [Fin.sum_univ_eq_sum_range (fun j => holeLinear (exposedFamily Ms G)
      (profile z j (U-j)) (extendCoefficients h (g j) (g (j+1)))) (U+1)]
    rw [integer_demand_conservation, exposed_marginal]

theorem recursivePotential_nonnegative : ∀ (Ms : List ℕ) {I : Type u} [Fintype I] [DecidableEq I]
    (F : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ),
    (∀ p, 0≤F p) → 0 ≤ recursivePotential Ms F z h := by
  intro Ms
  induction Ms with
  | nil =>
    intro I _ _ F z h hF
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg _ (sq_nonneg _)
    unfold oneHole
    split_ifs
    · exact hF _
    · exact le_rfl
  | cons U Ms ih =>
    intro I _ _ F z h hF
    apply Finset.sum_nonneg
    intro j _
    exact ih _ _ _ (fun p => hF _)


noncomputable def recursiveEnergy : {I : Type u} → [Fintype I] → [DecidableEq I] →
    (Ms : List ℕ) → ((Coordinates I Ms → ℕ) → ℝ) →
    ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → (I → ℝ) → ℝ
  | _, _, _, [], F, H, z, _ =>
    SignedTransport.cliqueEnergy (oneHole F z) (fun _ => 1) (fun i => H (FactorialSignatures.removeOne z i))
  | I, _, _, U::Ms, F, H, z, h =>
    let f := exposedFamily Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    ∑ j : Fin (U+1), recursiveEnergy Ms
      (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (fun x => H (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))

lemma oneHole_nonnegative {I : Type*} [DecidableEq I] (F : (I → ℕ) → ℝ)
    (hF : ∀ p, 0≤F p) (z : I → ℕ) (i : I) : 0≤oneHole F z i := by
  unfold oneHole
  split_ifs
  · exact hF _
  · exact le_rfl

lemma oneHole_mul {I : Type*} [DecidableEq I] (F H : (I → ℕ) → ℝ)
    (z : I → ℕ) (i : I) :
    oneHole (fun p => F p*H p) z i = oneHole F z i * H (FactorialSignatures.removeOne z i) := by
  unfold oneHole
  split_ifs <;> simp

theorem recursiveEnergy_nonnegative : ∀ (Ms : List ℕ) {I : Type u} [Fintype I] [DecidableEq I]
    (F H : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ),
    (∀ p, 0≤F p) → 0 ≤ recursiveEnergy Ms F H z h := by
  intro Ms
  induction Ms with
  | nil =>
    intro I _ _ F H z h hF
    change 0≤SignedTransport.cliqueEnergy (oneHole F z) (fun _ => 1)
      (fun i => H (FactorialSignatures.removeOne z i))
    unfold SignedTransport.cliqueEnergy
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (le_min (by simpa using oneHole_nonnegative F hF z i)
      (by simpa using oneHole_nonnegative F hF z j)) (sq_nonneg _)
  | cons U Ms ih =>
    intro I _ _ F H z h hF
    apply Finset.sum_nonneg
    intro j _
    exact ih _ _ _ _ (fun p => hF _)


noncomputable def recursivelyBalanced : {I : Type u} → [Fintype I] → [DecidableEq I] →
    (Ms : List ℕ) → ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → (I → ℝ) → Prop
  | _, _, _, [], F, z, h => holeLinear F z h = 0
  | I, _, _, U::Ms, F, z, h =>
    let f := exposedFamily Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    ∀ j : Fin (U+1), recursivelyBalanced Ms
      (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))

/-- Positivity only on the valid box and degree supplies every cumulative
coefficient denominator and propagates root balance to all actual leaves. -/
theorem recursivelyBalanced_of_slice : ∀ (Ms : List ℕ) {I : Type u} [Fintype I] [DecidableEq I]
    (F : (Coordinates I Ms → ℕ) → ℝ) (m z : I → ℕ) (R : ℕ) (h : I → ℝ),
    BalancedBox.PositiveSlice F (bounds m Ms) (R+Ms.sum) →
    BalancedBox.InBox m z → (∑ i, z i)=R+1 →
    holeLinear (eliminate Ms F) z h=0 → recursivelyBalanced Ms F z h := by
  intro Ms
  induction Ms with
  | nil => intro I _ _ F m z R h _ _ _ hb; exact hb
  | cons U Ms ih =>
    intro I _ _ F m z R h hpos hz htotal hbalance
    have hp : BalancedBox.PositiveSlice F (profile (bounds m Ms) U U) (R+U+Ms.sum) := by
      rw [show R+U+Ms.sum=R+(U::Ms).sum by simp only [List.sum_cons]; omega]
      exact hpos
    let f := exposedFamily Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    have hfpos := exposed_positive Ms U m R F hp
    have hinner : ∀ k, 0 < k → k < U+1 → 0 < innerWeight f (U+1) z k := by
      intro k hk0 hkU
      rw [innerWeight, ite_eq_left ⟨hk0,hkU⟩]
      apply hfpos
      · apply BalancedBox.profile_inBox m z U (k-1) (U+1-1-k) hz <;> omega
      · rw [BalancedBox.profile_total, htotal]
        omega
    have hcum : pairCumulative (cross f (U+1) z) h (U+1)=0 := by
      rw [cumulative_eq_parent_demand]
      change holeLinear (marginal (exposedFamily Ms F) U) z h=0
      rw [exposed_marginal]
      exact hbalance
    change ∀ j : Fin (U+1), recursivelyBalanced Ms
      (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))
    intro j
    apply ih _ (profile m U U) _ (R+U) _ (expose_source_positive Ms U m R F hp)
    · exact BalancedBox.profile_inBox m z U j.val (U-j.val) hz (by omega) (Nat.sub_le _ _)
    · rw [BalancedBox.profile_total, htotal]
      have hj := j.isLt
      omega
    · change holeLinear f (profile z j.val (U-j.val))
        (extendCoefficients h (g j.val) (g (j.val+1)))=0
      exact integer_child_balance f z U j.val (by have := j.isLt; omega) h hinner hcum

/-- The full actual recursive signed demands satisfy the leaf energy
comparison once their recursively proved balances are supplied. -/
theorem recursive_signed_transport : ∀ (Ms : List ℕ) {I : Type u} [Fintype I] [DecidableEq I]
    (F H : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ),
    (∀ p, 0≤F p) → recursivelyBalanced Ms F z h →
    (recursiveDemand Ms F (fun p => F p*H p) z h)^2 ≤
      recursivePotential Ms F z h * recursiveEnergy Ms F H z h := by
  intro Ms
  induction Ms with
  | nil =>
    intro I _ _ F H z h hF hbal
    have ht := integer_leaf_transport F z h
      (fun i => H (FactorialSignatures.removeOne z i)) hF hbal
    change (holeLinear (fun p => F p*H p) z h)^2 ≤ holePotential F z h *
      SignedTransport.cliqueEnergy (oneHole F z) (fun _ => 1)
        (fun i => H (FactorialSignatures.removeOne z i))
    have he : holeLinear (fun p => F p*H p) z h =
        ∑ i, oneHole F z i * h i * H (FactorialSignatures.removeOne z i) := by
      unfold holeLinear
      simp_rw [oneHole_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    exact ht
  | cons U Ms ih =>
    intro I _ _ F H z h hF hbal
    change (∑ j : Fin (U+1), recursiveDemand Ms _ _ _ _)^2 ≤
      (∑ j : Fin (U+1), recursivePotential Ms _ _ _) *
      (∑ j : Fin (U+1), recursiveEnergy Ms _ _ _ _)
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    · intro j _
      exact recursivePotential_nonnegative Ms _ _ _ (fun p => hF _)
    · intro j _
      exact recursiveEnergy_nonnegative Ms _ _ _ _ (fun p => hF _)
    · intro j _
      exact ih _ _ _ _ (fun p => hF _) (hbal j)

/-- The full recursive comparison with all balances discharged from
the literal softened slice, expressed solely using the root numerator. -/
theorem integer_recursive_transport_of_slice {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (F H : (Coordinates I Ms → ℕ) → ℝ) (m z : I → ℕ)
    (R : ℕ) (h : I → ℝ) (hF : ∀ p, 0 ≤ F p)
    (hpos : BalancedBox.PositiveSlice F (bounds m Ms) (R+Ms.sum))
    (hz : BalancedBox.InBox m z) (htotal : (∑ i, z i)=R+1)
    (hbalance : holeLinear (eliminate Ms F) z h=0) :
    (holeLinear (eliminate Ms (fun p => F p*H p)) z h)^2 ≤
      recursivePotential Ms F z h * recursiveEnergy Ms F H z h := by
  rw [← recursiveDemand_eq Ms F (fun p => F p*H p) z h]
  exact recursive_signed_transport Ms F H z h hF
    (recursivelyBalanced_of_slice Ms F m z R h hpos hz htotal hbalance)

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerLeafEnergy
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

noncomputable def leafClique {C : Type*} [Fintype C] [DecidableEq C]
    (F H : (C → ℕ) → ℝ) (z : C → ℕ) : ℝ :=
  SignedTransport.cliqueEnergy (oneHole F z) (fun _ => 1) (fun i => H (removeOne z i))

lemma oneHole_reindex {C D : Type*} [DecidableEq C] [DecidableEq D]
    (e : C ≃ D) (F : (D → ℕ) → ℝ) (z : C → ℕ) (i : C) :
    oneHole (fun x => F (x ∘ e.symm)) z i = oneHole F (z ∘ e.symm) (e i) := by
  unfold oneHole
  simp only [Function.comp_apply, Equiv.symm_apply_apply, removeOne_reindex]

lemma leafClique_reindex {C D : Type*} [Fintype C] [Fintype D]
    [DecidableEq C] [DecidableEq D] (e : C ≃ D) (F H : (D → ℕ) → ℝ) (z : C → ℕ) :
    leafClique (fun x => F (x ∘ e.symm)) (fun x => H (x ∘ e.symm)) z =
      leafClique F H (z ∘ e.symm) := by
  unfold leafClique SignedTransport.cliqueEnergy
  simp only [one_mul, oneHole_reindex, removeOne_reindex]
  congr 1
  calc
    _ = ∑ i : C, ∑ j : D,
        min (oneHole F (z ∘ e.symm) (e i)) (oneHole F (z ∘ e.symm) j) *
          (H (removeOne (z ∘ e.symm) (e i))-H (removeOne (z ∘ e.symm) j))^2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact e.sum_comp (fun j : D =>
        min (oneHole F (z ∘ e.symm) (e i)) (oneHole F (z ∘ e.symm) j) *
          (H (removeOne (z ∘ e.symm) (e i))-H (removeOne (z ∘ e.symm) j))^2)
    _ = _ := e.sum_comp (fun i : D => ∑ j : D,
      min (oneHole F (z ∘ e.symm) i) (oneHole F (z ∘ e.symm) j) *
        (H (removeOne (z ∘ e.symm) i)-H (removeOne (z ∘ e.symm) j))^2)

noncomputable def leafEnergySum {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (F H : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) : ℝ :=
  ∑ a : Assignments Ms, leafClique F H (embedding Ms z a)

/-- Every recursive leaf is exactly its literal full display, counted
once in the Cartesian product of the ordinary balanced profiles. -/
theorem recursiveEnergy_eq_leafEnergySum : ∀ (Ms : List ℕ) {I : Type u}
    [Fintype I] [DecidableEq I] (F H : (Coordinates I Ms → ℕ) → ℝ)
    (z : I → ℕ) (h : I → ℝ),
    recursiveEnergy Ms F H z h=leafEnergySum Ms F H z := by
  intro Ms
  induction Ms with
  | nil =>
    intro I _ _ F H z h
    simp only [recursiveEnergy, leafEnergySum, Assignments, embedding, Fintype.sum_unique, leafClique]
  | cons U Ms ih =>
    intro I _ _ F H z h
    let f := exposedFamily Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    change (∑ j : Fin (U+1), recursiveEnergy Ms
      (fun x => F (x ∘ (exposeEquiv (I := I) Ms).symm))
      (fun x => H (x ∘ (exposeEquiv (I := I) Ms).symm))
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))) = _
    simp_rw [ih]
    unfold leafEnergySum
    simp_rw [leafClique_reindex]
    have he (j : Fin (U+1)) (a : Assignments Ms) :
        embedding Ms (profile z j.val (U-j.val)) a ∘ (exposeEquiv (I := I) Ms).symm =
          profile (embedding Ms z a) j.val (U-j.val) :=
      expose_embedding Ms z j.val (U-j.val) a
    simp_rw [he]
    rw [Finset.sum_comm]
    change (∑ a : Assignments Ms, ∑ j : Fin (U+1),
      leafClique F H (profile (embedding Ms z a) j.val (U-j.val))) =
      ∑ a : Assignments Ms × Fin (U+1), leafClique F H (embedding (U::Ms) z a)
    rw [Fintype.sum_prod_type]
    rfl

lemma embedding_injective {I : Type u} (Ms : List ℕ) (z : I → ℕ) :
    Function.Injective (embedding Ms z) := by
  induction Ms with
  | nil => intro a b _; exact Subsingleton.elim _ _
  | cons U Ms ih =>
    intro a b hab
    apply Prod.ext
    · apply ih
      funext i
      exact congrFun hab (.inl i)
    · apply Fin.ext
      exact congrFun hab (.inr false)

/-- Distinct valid holes recover their full display by the coordinate
maximum. This is the reason different leaf cliques share no edges. -/
lemma max_removeOne {C : Type*} [DecidableEq C] (z : C → ℕ) (i j : C)
    (hij : i ≠ j) :
    (fun k => max (removeOne z i k) (removeOne z j k))=z := by
  funext k
  unfold removeOne
  by_cases hki : k=i
  · subst k
    simp only [hij, ↓reduceIte, Nat.sub_zero]
    exact max_eq_right (Nat.sub_le _ _)
  · by_cases hkj : k=j
    · subst k
      simp only [hki, ↓reduceIte, Nat.sub_zero]
      exact max_eq_left (Nat.sub_le _ _)
    · simp only [hki,hkj,↓reduceIte,Nat.sub_zero,max_self]

lemma removeOne_injective_valid {C : Type*} [DecidableEq C] (z : C → ℕ)
    (i j : C) (hi : 0 < z i) (he : removeOne z i=removeOne z j) : i=j := by
  by_contra hij
  have h := congrFun he i
  simp only [removeOne, hij, ↓reduceIte, Nat.sub_zero] at h
  omega

def leafEdgeCodes {I : Type u} [Fintype I] [DecidableEq I] (Ms : List ℕ) (z : I → ℕ) :
    Finset (Assignments Ms × Coordinates I Ms × Coordinates I Ms) :=
  Finset.univ.filter (fun e => 0 < embedding Ms z e.1 e.2.1 ∧
    0 < embedding Ms z e.1 e.2.2 ∧ e.2.1 ≠ e.2.2)

def leafEdgeState {I : Type u} [DecidableEq I] (Ms : List ℕ) (z : I → ℕ)
    (e : Assignments Ms × Coordinates I Ms × Coordinates I Ms) :
    (Coordinates I Ms → ℕ) × (Coordinates I Ms → ℕ) :=
  (removeOne (embedding Ms z e.1) e.2.1, removeOne (embedding Ms z e.1) e.2.2)

/-- An oriented exchange edge determines its display, then its branch
assignment, then its two hole coordinates. -/
theorem leafEdgeState_injective {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (z : I → ℕ) :
    Set.InjOn (leafEdgeState Ms z) (leafEdgeCodes Ms z) := by
  intro a ha b hb he
  obtain ⟨hai,haj,haij⟩ := (Finset.mem_filter.mp ha).2
  obtain ⟨hbi,hbj,hbij⟩ := (Finset.mem_filter.mp hb).2
  have hd : embedding Ms z a.1=embedding Ms z b.1 := by
    calc
      _ = fun k => max ((leafEdgeState Ms z a).1 k) ((leafEdgeState Ms z a).2 k) :=
        (max_removeOne _ _ _ haij).symm
      _ = fun k => max ((leafEdgeState Ms z b).1 k) ((leafEdgeState Ms z b).2 k) := by rw [he]
      _ = _ := max_removeOne _ _ _ hbij
  have hab := embedding_injective Ms z hd
  apply Prod.ext hab
  apply Prod.ext
  · apply removeOne_injective_valid (embedding Ms z a.1) _ _ hai
    have ht := congrArg Prod.fst he
    change removeOne (embedding Ms z a.1) a.2.1=removeOne (embedding Ms z b.1) b.2.1 at ht
    simpa only [←hab] using ht
  · apply removeOne_injective_valid (embedding Ms z a.1) _ _ haj
    have ht := congrArg Prod.snd he
    change removeOne (embedding Ms z a.1) a.2.2=removeOne (embedding Ms z b.1) b.2.2 at ht
    simpa only [←hab] using ht

noncomputable def leafEdges {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (z : I → ℕ) :
    Finset ((Coordinates I Ms → ℕ) × (Coordinates I Ms → ℕ)) :=
  (leafEdgeCodes Ms z).image (leafEdgeState Ms z)

lemma leafClique_eq_valid_sum {C : Type*} [Fintype C] [DecidableEq C]
    (F H : (C → ℕ) → ℝ) (z : C → ℕ) (hF : ∀ x, 0 ≤ F x) :
    leafClique F H z = (∑ i, ∑ j,
      if 0 < z i ∧ 0 < z j ∧ i ≠ j then
        edgeTerm F H (removeOne z i,removeOne z j) else 0)/2 := by
  unfold leafClique SignedTransport.cliqueEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [one_mul]
  by_cases hij : i=j
  · subst j
    simp
  · by_cases hi : 0 < z i
    · by_cases hj : 0 < z j
      · simp [oneHole,edgeTerm,hi,hj,hij]
      · simp only [oneHole,hi,hj,↓reduceIte,and_false,false_and,
          min_eq_right (hF _),zero_mul]
    · have hj := oneHole_nonnegative F hF z j
      simp only [oneHole,hi,↓reduceIte] at hj ⊢
      rw [min_eq_left hj]
      simp

/-- Complete leaf cliques have disjoint oriented edges. The resulting
energy is exactly the ordinary minimum-endpoint graph sum. -/
theorem leafEnergySum_eq_edges {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (F H : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ)
    (hF : ∀ x, 0 ≤ F x) :
    leafEnergySum Ms F H z = (∑ e ∈ leafEdges Ms z, edgeTerm F H e)/2 := by
  unfold leafEnergySum
  simp_rw [leafClique_eq_valid_sum F H _ hF]
  rw [← Finset.sum_div]
  congr 1
  rw [leafEdges, Finset.sum_image (leafEdgeState_injective Ms z)]
  unfold leafEdgeCodes
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type]
  rfl

noncomputable def leafVertices {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (z : I → ℕ) : Finset (Coordinates I Ms → ℕ) :=
  Finset.univ.biUnion (fun a : Assignments Ms =>
    (Finset.univ.filter (fun i => 0 < embedding Ms z a i)).image
      (fun i => removeOne (embedding Ms z a) i))

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileExchangeProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary list program for a small-profile unit exchange -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

/-- The binary list program implements the exact coordinate update used
by the physical graph, with no bounded-integer overflow. -/
theorem listExchange_ofFn {n : ℕ} (v : Fin n → ℕ) (i j : Fin n) :
    listExchange (List.ofFn v,(i.val,j.val))=
      List.ofFn (IntegerWeightedTransport.exchangeTarget v i j) := by
  apply List.ext_getElem
  · simp only [listExchange,List.length_map,List.length_range,List.length_ofFn]
  · intro a ha _
    have han : a<n := by
      simpa only [listExchange,List.length_map,List.length_range,List.length_ofFn] using ha
    simp only [listExchange,List.getElem_map,List.getElem_range,List.getElem_ofFn,exchangeEntry,
      List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using han)]
    simp only [Option.getD_some,List.getElem_ofFn,IntegerWeightedTransport.exchangeTarget,Fin.ext_iff]

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargePairEnumeration
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical indexing of all balanced large-cell pairs

The recursively added pairs are identified with the actual finite cells,
and their assignments with the dependent product of the physical finite
intervals. No extra coordinate or assignment multiplicity is introduced.
-/

namespace ContingencyTables.LargePairEnumeration

open scoped BigOperators Classical
open BalancedFamily BalancedEnumeration IntegerMarginal

universe u

/-- The nested coordinate sums contain exactly the retained coordinates
and one doubled coordinate for each physical large cell. -/
def coordinateEquiv (S : Type u) : {n : ℕ} → (M : Fin n → ℕ) →
    Coordinates S (widths M) ≃ S⊕(Fin n×Bool)
  | 0,_ => (Equiv.sumEmpty S (Fin 0×Bool)).symm
  | n+1,M =>
    (Equiv.sumCongr (coordinateEquiv S (fun i => M i.succ)) (Equiv.refl Bool)).trans
      ((Equiv.sumAssoc S (Fin n×Bool) Bool).trans
        (Equiv.sumCongr (Equiv.refl S) (pairSuccEquiv n)))

/-- Balanced choices are the dependent product of the actual intervals. -/
def assignmentEquiv : {n : ℕ} → (M : Fin n → ℕ) →
    Assignments (widths M) ≃ ((i : Fin n) → Fin (M i+1))
  | 0,_ =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := by intro a; cases a; rfl
      right_inv := by intro a; funext i; exact Fin.elim0 i }
  | n+1,M =>
    { toFun := fun a => Fin.cases a.2 (assignmentEquiv (fun i => M i.succ) a.1)
      invFun := fun a => ((assignmentEquiv (fun i => M i.succ)).symm (fun i => a i.succ),a 0)
      left_inv := by intro a; simp only [Fin.cases_zero,Fin.cases_succ,Equiv.symm_apply_apply]; exact Prod.eta a
      right_inv := by
        intro a
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact congrFun ((assignmentEquiv (fun i => M i.succ)).apply_symm_apply
            (fun i => a i.succ)) j }

lemma embedding_coordinate {S : Type*} {n : ℕ} (M : Fin n → ℕ) (z : S → ℕ)
    (a : (i : Fin n) → Fin (M i+1)) (c : Coordinates S (widths M)) :
    embedding (widths M) z ((assignmentEquiv M).symm a) c=
      joinedProfile M z a (coordinateEquiv S M c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases c with
    | inl c =>
      change embedding (widths (fun i => M i.succ)) z
        ((assignmentEquiv (fun i => M i.succ)).symm (fun i => a i.succ)) c=_
      rw [ih]
      change joinedProfile (fun i => M i.succ) z (fun i => a i.succ)
        (coordinateEquiv S (fun i => M i.succ) c)=
        joinedProfile M z a (((Equiv.sumAssoc S (Fin n×Bool) Bool).trans
          (Equiv.sumCongr (Equiv.refl S) (pairSuccEquiv n)))
          (.inl (coordinateEquiv S (fun i => M i.succ) c)))
      generalize hc : coordinateEquiv S (fun i => M i.succ) c=q
      cases q with
      | inl s => rfl
      | inr p => rcases p with ⟨i,b⟩; rfl
    | inr b => cases b <;> rfl

/-- The recursively proved marginal is the direct finite sum over the
actual physical intervals. -/
theorem eliminate_eq_physical_sum {S : Type*} {n : ℕ} (M : Fin n → ℕ)
    (F : (S⊕(Fin n×Bool) → ℕ) → ℝ) (z : S → ℕ) :
    eliminate (widths M) (fun q => F (q ∘ (coordinateEquiv S M).symm)) z=
      ∑ a : ((i : Fin n) → Fin (M i+1)), F (joinedProfile M z a) := by
  rw [eliminate_eq_sum]
  apply Fintype.sum_equiv (assignmentEquiv M)
  intro a
  congr 1
  funext c
  have h := embedding_coordinate M z ((assignmentEquiv M) a) ((coordinateEquiv S M).symm c)
  simpa only [Equiv.symm_apply_apply,Equiv.apply_symm_apply,Function.comp_apply] using h

variable {C : Type*}

/-- This is the actual partition of doubled cells into small views and
large pairs. -/
noncomputable def partitionEquiv (small : C → Bool) :
    SmallView small⊕(LargeCell small×Bool) ≃ C×Bool where
  toFun
    | .inl p => (p.1.val,p.2)
    | .inr p => (p.1.val,p.2)
  invFun p := if h : small p.1=true then .inl (⟨p.1,h⟩,p.2)
    else .inr (⟨p.1,Bool.eq_false_iff.mpr h⟩,p.2)
  left_inv p := by
    cases p with
    | inl p => simp only [p.1.property,dite_eq_left]
    | inr p => simp only [p.1.property,Bool.false_eq_true,dite_false]
  right_inv p := by
    dsimp only
    split_ifs <;> rfl

noncomputable def physicalJoinEquiv (small : C → Bool) {n : ℕ}
    (e : Fin n ≃ LargeCell small) : SmallView small⊕(Fin n×Bool) ≃ C×Bool :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr e (Equiv.refl Bool))).trans
    (partitionEquiv small)

/-- Every finite enumeration of the large cells gives the same physical
coordinate space, with each original doubled cell appearing once. -/
noncomputable def physicalCoordinateEquiv (small : C → Bool) {n : ℕ}
    (e : Fin n ≃ LargeCell small) (M : Fin n → ℕ) :
    Coordinates (SmallView small) (widths M) ≃ C×Bool :=
  (coordinateEquiv (SmallView small) M).trans (physicalJoinEquiv small e)

theorem eliminate_eq_actual_cells (small : C → Bool) {n : ℕ}
    (e : Fin n ≃ LargeCell small) (M : Fin n → ℕ)
    (F : (C×Bool → ℕ) → ℝ) (z : SmallView small → ℕ) :
    eliminate (widths M) (fun q => F (q ∘ (physicalCoordinateEquiv small e M).symm)) z=
      ∑ a : ((i : Fin n) → Fin (M i+1)),
        F (joinedProfile M z a ∘ (physicalJoinEquiv small e).symm) := by
  exact eliminate_eq_physical_sum M (fun q => F (q ∘ (physicalJoinEquiv small e).symm)) z

end ContingencyTables.LargePairEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_LaminarSignature
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two-level laminar kernel in contingency-table weights

The factor groups in the sampling paper's laminar-signature lemma are line
coordinate sets, with one nested small-slot subset in each line. Row and
column coordinates belong to separate lines. The normalized kernel
decomposition gives the quadratic one-positive-direction property.
-/

namespace ContingencyTables

open scoped BigOperators
open LinearMap (BilinForm)

section TwoLevel

variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]

/-- This includes the full unsummed two-removal signature: positive scalar
and diagonal congruence, invalid diagonals removed, zero rows restored. -/
theorem correctedTwoLevel_onePositive (line : I → G) (inner : I → Bool) (γ δ : G → ℝ)
    (W : ℝ) (α κ : I → ℝ)
    (hγ0 : ∀ g, 0 ≤ γ g) (hγ1 : ∀ g, γ g ≤ 1) (hδ1 : ∀ g, δ g ≤ 1)
    (hW : 0 ≤ W) (hκ : ∀ i, 0 ≤ κ i) :
    OnePositiveDirection (weightedCorrection (twoLevelKernel line inner γ δ) W α κ).toBilin' := by
  refine onePositiveDirection_of_kernel _ ?_ (vectorSum α) ?_
  · intro x y
    rw [weightedCorrection_form, weightedCorrection_form,
      twoLevelKernel_form_symm line inner γ δ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro v hv
    have hsum : vectorSum (fun _ : I => 1) (fun i => α i * v i) = 0 := by
      simpa only [vectorSum_apply, one_mul] using hv
    have hK := twoLevelKernel_nonpositive line inner γ δ hγ0 hγ1 hδ1
      (fun i => α i * v i) hsum
    have hnegative := mul_nonpos_of_nonneg_of_nonpos hW hK
    have hdiagonal : 0 ≤ ∑ i, κ i * v i * v i := by
      apply Finset.sum_nonneg
      intro i _
      have h := mul_nonneg (hκ i) (mul_self_nonneg (v i))
      nlinarith
    rw [weightedCorrection_form]
    linarith

end TwoLevel

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_LineUnarySignature
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The line and unary factors of the bounded-table application

The bounded-table signature argument uses disjoint row/column line factors
and unary tree penalties. Factoring the product after two removals expresses
unary factors as nonnegative diagonal corrections of the line kernel.
-/

namespace ContingencyTables

open scoped BigOperators

section LineUnary

variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]

/-- The actual line/unary two-removal matrix has the required signature
when each factor satisfies its scalar log-concavity inequality. -/
theorem lineUnaryRemoval_onePositive (line : I → G)
    (a₀ a₁ a₂ : G → ℝ) (b₀ b₁ b₂ : I → ℝ)
    (ha₀ : ∀ g, 0 < a₀ g) (ha₁ : ∀ g, 0 < a₁ g) (ha₂ : ∀ g, 0 ≤ a₂ g)
    (hb₀ : ∀ i, 0 < b₀ i) (hb₁ : ∀ i, 0 < b₁ i)
    (halc : ∀ g, a₀ g * a₂ g ≤ (a₁ g) ^ 2)
    (hblc : ∀ i, b₀ i * b₂ i ≤ (b₁ i) ^ 2) :
    OnePositiveDirection (lineUnaryRemoval line a₀ a₁ a₂ b₀ b₁ b₂).toBilin' := by
  let W := (∏ g, a₀ g) * ∏ i, b₀ i
  let α : I → ℝ := fun i => (a₁ (line i) / a₀ (line i)) * (b₁ i / b₀ i)
  let γ : G → ℝ := fun g => a₀ g * a₂ g / (a₁ g) ^ 2
  let δ : I → ℝ := fun i => b₀ i * b₂ i / (b₁ i) ^ 2
  let K := twoLevelKernel line (fun _ => false) γ (fun _ => 1)
  let κ : I → ℝ := fun i => W * α i ^ 2 * γ (line i) * (1 - δ i)
  have hW : 0 ≤ W := mul_nonneg
    (Finset.prod_nonneg fun g _ => (ha₀ g).le) (Finset.prod_nonneg fun i _ => (hb₀ i).le)
  have hγ₀ (g : G) : 0 ≤ γ g :=
    div_nonneg (mul_nonneg (ha₀ g).le (ha₂ g)) (sq_nonneg _)
  have hγ₁ (g : G) : γ g ≤ 1 := by
    exact (div_le_one (sq_pos_of_pos (ha₁ g))).mpr (halc g)
  have hδ₁ (i : I) : δ i ≤ 1 := by
    exact (div_le_one (sq_pos_of_pos (hb₁ i))).mpr (hblc i)
  have hκ (i : I) : 0 ≤ κ i :=
    mul_nonneg (mul_nonneg (mul_nonneg hW (sq_nonneg _)) (hγ₀ _))
      (sub_nonneg.mpr (hδ₁ i))
  have heq : lineUnaryRemoval line a₀ a₁ a₂ b₀ b₁ b₂ = weightedCorrection K W α κ := by
    rw [← normalized_line_unary_correction line W α γ δ]
    ext i j
    exact lineUnaryRemoval_factor line a₀ a₁ a₂ b₀ b₁ b₂
      (fun g => ne_of_gt (ha₀ g)) (fun g => ne_of_gt (ha₁ g))
      (fun i => ne_of_gt (hb₀ i)) (fun i => ne_of_gt (hb₁ i)) i j
  rw [heq]
  exact correctedTwoLevel_onePositive line (fun _ => false) γ (fun _ => 1)
    W α κ hγ₀ hγ₁ (fun _ => le_refl _) hW hκ

end LineUnary

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerBoxTruncation
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual finite-box fixed-total weight

Truncating the positive product outside its box and required total leaves
every valid two-removal matrix entry unchanged at a box-valid display two
above that total. The balancing development therefore applies to the
paper's literal zero-extended weight.
-/

namespace ContingencyTables.IntegerBoxTruncation

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures ProductIntegerSignature BalancedBox

variable {I : Type*} [Fintype I]

noncomputable def truncate (f : (I → ℕ) → ℝ) (m : I → ℕ) (R : ℕ) (z : I → ℕ) : ℝ :=
  if InBox m z ∧ (∑ i, z i)=R then f z else 0

omit [Fintype I] in
lemma removal_inBox (m z : I → ℕ) (hz : InBox m z) (i j : I) : InBox m (removeTwo z i j) := by
  intro k
  apply le_trans _ (hz k)
  unfold removeTwo removeOne
  omega

end ContingencyTables.IntegerBoxTruncation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_NestedProductSignature
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The first paper's actual line and small-slot subgroup product

Each small-slot subgroup is contained in a disjoint line group. The literal
product after two removals is factored into the two-level kernel. Zero
integer counts are masked and invalid repeated removals subtract a
nonnegative diagonal.
-/

namespace ContingencyTables.NestedProductSignature

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures ProductIntegerSignature

variable {I G : Type*} [Fintype I] [Fintype G]

/-- Signature of the literal nested product update matrix. -/
theorem nestedRemoval_onePositive (line : I → G) (inner : I → Bool)
    (a₀ a₁ a₂ c₀ c₁ c₂ : G → ℝ)
    (ha₀ : ∀ g, 0 < a₀ g) (ha₁ : ∀ g, 0 < a₁ g) (ha₂ : ∀ g, 0 ≤ a₂ g)
    (hc₀ : ∀ g, 0 < c₀ g) (hc₁ : ∀ g, 0 < c₁ g)
    (halc : ∀ g, a₀ g*a₂ g ≤ (a₁ g)^2)
    (hclc : ∀ g, c₀ g*c₂ g ≤ (c₁ g)^2) :
    OnePositiveDirection (nestedRemoval line inner a₀ a₁ a₂ c₀ c₁ c₂).toBilin' := by
  let W := (∏ g, a₀ g) * ∏ g, c₀ g
  let α : I → ℝ := fun i => (a₁ (line i)/a₀ (line i)) *
    (if inner i then c₁ (line i)/c₀ (line i) else 1)
  let γ : G → ℝ := fun g => a₀ g*a₂ g/(a₁ g)^2
  let δ : G → ℝ := fun g => c₀ g*c₂ g/(c₁ g)^2
  have he : nestedRemoval line inner a₀ a₁ a₂ c₀ c₁ c₂ =
      weightedCorrection (twoLevelKernel line inner γ δ) W α (fun _ => 0) := by
    ext i j
    rw [nestedRemoval_factor line inner a₀ a₁ a₂ c₀ c₁ c₂
      (fun g => ne_of_gt (ha₀ g)) (fun g => ne_of_gt (ha₁ g))
      (fun g => ne_of_gt (hc₀ g)) (fun g => ne_of_gt (hc₁ g))]
    simp only [weightedCorrection,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      scaledMatrix,Matrix.diagonal_apply,ite_self,sub_zero]
    ring
  rw [he]
  exact correctedTwoLevel_onePositive line inner γ δ W α (fun _ => 0)
    (fun g => div_nonneg (mul_nonneg (ha₀ g).le (ha₂ g)) (sq_nonneg _))
    (fun g => (div_le_one (sq_pos_of_pos (ha₁ g))).mpr (halc g))
    (fun g => (div_le_one (sq_pos_of_pos (hc₁ g))).mpr (hclc g))
    (mul_nonneg (Finset.prod_nonneg fun g _ => (ha₀ g).le)
      (Finset.prod_nonneg fun g _ => (hc₀ g).le)) (fun _ => le_rfl)

noncomputable def nestedWeight (line : I → G) (inner : I → Bool)
    (a c : G → ℕ → ℝ) (z : I → ℕ) : ℝ :=
  (∏ g, a g (lineTotal line z g)) * ∏ g, c g (smallTotal line inner z g)

omit [Fintype I] in
lemma masked_correction (h : (I → ℕ) → ℝ) (z : I → ℕ) (H : Matrix I I ℝ)
    (hentry : ∀ i j, ValidPair z i j → h (removeTwo z i j)=H i j) :
    integerRemovalMatrix h z = scaledMatrix H (activeMask z) -
      Matrix.diagonal (fun i => if z i=1 then H i i else 0) := by
  ext i j
  simp only [Matrix.sub_apply,Matrix.diagonal_apply,integerRemovalMatrix,scaledMatrix,activeMask]
  by_cases hv : ValidPair z i j
  · have hi : 0 < z i := hv.1
    have hj : 0 < z j := by have := hv.2; omega
    rw [ite_eq_left hv,hentry i j hv]
    simp only [hi,hj,ite_true, if_true,one_mul,mul_one]
    by_cases hij : i=j
    · subst j
      have hn : z i ≠ 1 := by have := hv.2; simp at this; omega
      simp [hn]
    · simp [hij]
  · rw [ite_eq_right hv]
    by_cases hi : 0 < z i
    · by_cases hj : 0 < z j
      · have hij : i=j := by by_contra h; exact hv ⟨hi,by simpa [Ne.symm h] using hj⟩
        subst j
        have hn : z i=1 := by simp [ValidPair] at hv; omega
        simp [hn]
      · by_cases hij : i=j
        · subst j
          have hn : z i=0 := by omega
          simp [hn]
        · simp [hj,hij]
    · by_cases hij : i=j
      · subst j
        have hn : z i=0 := by omega
        simp [hn]
      · simp [hi,hij]

end ContingencyTables.NestedProductSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_LabelledFactorial
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Literal subset factorial lifts and their conditioned copy displays

A display is the actual subtype of available labelled elements. Its group
fibres are reindexed by Fin of their exact cardinalities. Removing or adding
actual labels changes the group counts by the exact integer updates, so the
conditioned subset matrices are congruent to the proved factorial copy
matrices. No binary-lift signature is assumed.
-/

namespace ContingencyTables.LabelledFactorial

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS BinaryContraction FactorialSignatures

variable {I G : Type*} [Fintype I] [Fintype G]

omit [Fintype G] in
lemma groupCount_remove (group : I → G) (S : Set I) (i : I) (hi : i ∈ S) :
    groupCount group (S \ {i}) = removeOne (groupCount group S) (group i) := by
  funext u
  have heq : Finset.univ.filter (fun j => j ∈ S \ {i} ∧ group j = u) =
      (Finset.univ.filter (fun j => j ∈ S ∧ group j = u)).erase i := by
    ext j; simp; tauto
  unfold groupCount removeOne
  have hc := congrArg Finset.card heq
  convert hc.trans ?_ using 1
  · congr 1; ext j; simp
  · by_cases h : group i = u
    · rw [Finset.card_erase_of_mem (by simp [hi,h])]
      simp [h]
    · rw [Finset.erase_eq_of_notMem (by simp [h])]
      simp [Ne.symm h]

omit [Fintype G] in
lemma groupCount_removeTwo (group : I → G) (S : Set I) (i j : I)
    (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    groupCount group (S \ {i,j}) = removeTwo (groupCount group S) (group i) (group j) := by
  have heq : S \ {i,j} = (S \ {i}) \ {j} := by ext x; simp; tauto
  rw [heq, groupCount_remove group _ j (by simp [hj,hij.symm]), groupCount_remove group S i hi]
  rfl

omit [Fintype G] in
lemma fibre_card (group : I → G) (S : Set I) (u : G) :
    Fintype.card {i : {i // i ∈ S} // group i.val = u} = groupCount group S u := by
  let E : {i : {i // i ∈ S} // group i.val = u} ≃
      {i : I // i ∈ Finset.univ.filter (fun i => i ∈ S ∧ group i = u)} :=
    { toFun := fun i => ⟨i.val.val, by simp [i.val.property,i.property]⟩
      invFun := fun i => ⟨⟨i.val, by simpa using (Finset.mem_filter.mp i.property).2.1⟩,
        (Finset.mem_filter.mp i.property).2.2⟩
      left_inv := fun i => rfl
      right_inv := fun i => rfl }
  exact (Fintype.card_congr E).trans (Fintype.card_coe _)

/-- The actual finite display, reindexed fibre by fibre by its exact copy count. -/
noncomputable def displayCopyEquiv (group : I → G) (S : Set I) :
    {i // i ∈ S} ≃ Copies (groupCount group S) :=
  (Equiv.sigmaFiberEquiv (fun i : {i // i ∈ S} => group i.val)).symm.trans
    (Equiv.sigmaCongrRight (fun u => Fintype.equivFinOfCardEq (fibre_card group S u)))

omit [Fintype G] in
lemma displayCopyEquiv_group (group : I → G) (S : Set I) (i : {i // i ∈ S}) :
    (displayCopyEquiv group S i).1 = group i.val := rfl

lemma groupCount_total (group : I → G) (S : Set I) :
    ∑ u, groupCount group S u = S.ncard := by
  have h := Fintype.card_congr (displayCopyEquiv group S)
  simp only [Copies, Fintype.card_sigma, Fintype.card_fin] at h
  have hc : Fintype.card {i // i ∈ S} = S.ncard := by
    exact Set.fintypeCard_eq_ncard S
  omega

noncomputable def secondLift (group : I → G) (h : (G → ℕ) → ℝ) (D : ℝ) (S : Set I) : ℝ :=
  h (groupCount group S) * factorialProduct (groupCount group Sᶜ) / D

/-- Every entry of the literal subset omission matrix equals the copy
matrix entry at the canonical labels of the available display. -/
theorem firstLift_omission_matrix (group : I → G) (h : (G → ℕ) → ℝ) (D : ℝ) (A : Set I) :
    faceHessian (complementWeight (firstLift group h D)) A =
      (removalLiftMatrix h (groupCount group Aᶜ) D).submatrix
        (displayCopyEquiv group Aᶜ) (displayCopyEquiv group Aᶜ) := by
  ext i j
  by_cases hij : i = j
  · simp [faceHessian, removalLiftMatrix, Matrix.submatrix_apply, hij]
  have he : displayCopyEquiv group Aᶜ i ≠ displayCopyEquiv group Aᶜ j :=
    fun h => hij ((displayCopyEquiv group Aᶜ).injective h)
  have hs : (A ∪ {i.val,j.val})ᶜ = Aᶜ \ {i.val,j.val} := by ext x; simp; tauto
  have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  simp only [faceHessian, hij, ite_false, Matrix.submatrix_apply, removalLiftMatrix, he,
    complementWeight, firstLift, displayCopyEquiv_group]
  rw [hs, groupCount_removeTwo group Aᶜ i.val j.val i.property j.property hval]

end ContingencyTables.LabelledFactorial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_SliceFactorial
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual fixed-total signatures give the labelled factorial properties

Every subset count is in its true label-capacity box and its total is the
subset's cardinality. These identities connect the proved integer slice
signatures to the first factorial lift, without any binary-signature input.
-/

namespace ContingencyTables.SliceFactorial

open scoped BigOperators Classical Matrix Topology
open CommonBasesFPRAS BinaryContraction FactorialSignatures LabelledFactorial BalancedBox

variable {L C : Type*} [Fintype L] [Fintype C]

omit [Fintype C] in
lemma groupCount_inBox (group : L → C) (S : Set L) :
    InBox (groupCount group Set.univ) (groupCount group S) := by
  intro c
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_univ] at hi ⊢
  exact hi.2

/-- Positivity of the proved actual total-slice marginal gives positivity
of the literal labelled factorial lift on exactly that subset degree. -/
theorem firstLift_degreePositive (group : L → C) (h : (C → ℕ) → ℝ) (D : ℝ) (R : ℕ)
    (hD : 0 < D) (hpos : PositiveSlice h (groupCount group Set.univ) R) :
    DegreePositive (firstLift group h D) R := by
  intro S hS
  apply div_pos _ hD
  apply mul_pos _ (factorialProduct_positive _)
  apply hpos _ (groupCount_inBox group S)
  rw [groupCount_total,hS]

end ContingencyTables.SliceFactorial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_NestedPenaltyApplication
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The first paper's actual positive penalties and hard equality limit

Full row/column deviations give absolute affine line factors; the nested
small-slot residual constraints give positive-part affine factors. Their
product is exactly 2^(-L D). Balanced large-slot sums retain their proved
signature, and their finite limit is the exact zero-penalty indicator sum.
-/

namespace ContingencyTables.NestedPenaltyApplication

open scoped BigOperators Classical Matrix Topology
open Filter CommonBasesFPRAS FactorialSignatures ProductIntegerSignature
open NestedProductSignature ScalarPenalty IntegerMarginal BalancedBox BalancedFamily

variable {C G : Type*} [Fintype C] [Fintype G]

noncomputable def softWeight (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) : (C → ℕ) → ℝ :=
  nestedWeight line inner
    (fun g => factor L (fun n => |offset g+(n:ℝ)*slope g|))
    (fun g => factor L (fun n => max (smallOffset g+(n:ℝ)*smallSlope g) 0))

lemma penalty_nonnegative (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (z : C → ℕ) :
    0 ≤ penalty line inner offset slope smallOffset smallSlope z := by
  apply add_nonneg <;> apply Finset.sum_nonneg
  · intro g _; exact abs_nonneg _
  · intro g _; exact le_max_right _ _

/-- This is the manuscript's literal exponential of the full deviation
plus the small residual violation penalty, with eta=2^(-L). -/
theorem softWeight_eq (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (z : C → ℕ) :
    softWeight line inner offset slope smallOffset smallSlope L z =
      (2:ℝ)^(-L*penalty line inner offset slope smallOffset smallSlope z) := by
  unfold softWeight nestedWeight factor penalty
  rw [prod_pow,prod_pow,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 1
  ring

lemma softWeight_positive (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (z : C → ℕ) :
    0 < softWeight line inner offset slope smallOffset smallSlope L z := by
  rw [softWeight_eq]
  exact Real.rpow_pos_of_pos (by norm_num) _

end ContingencyTables.NestedPenaltyApplication

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_NestedReindex
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical coordinate reindexing of the first paper's nested penalties -/

namespace ContingencyTables.NestedReindex

open scoped BigOperators Classical
open ProductIntegerSignature NestedProductSignature NestedPenaltyApplication
open BalancedFamily BalancedBox

variable {C D G : Type*} [Fintype C] [Fintype D] [Fintype G]

variable {S : Type*} [Fintype S] [DecidableEq S]

omit [Fintype S] in
/-- Box congruence with the ambient equality decision used by the actual
physical view type. -/
lemma removal_congr_box (f h : (S → ℕ) → ℝ) (m z : S → ℕ) (hz : InBox m z)
    (heq : ∀ x, InBox m x → f x=h x) :
    FactorialSignatures.integerRemovalMatrix f z=FactorialSignatures.integerRemovalMatrix h z := by
  have hd : (inferInstance : DecidableEq S)=Classical.decEq S := Subsingleton.elim _ _
  cases hd
  ext i j
  unfold FactorialSignatures.integerRemovalMatrix
  split_ifs with hv
  · exact heq _ (IntegerBoxTruncation.removal_inBox m z hz i j)
  · rfl

end ContingencyTables.NestedReindex

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPhysicalMarginal
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The first paper's physical hard marginal and its proved raw signature

This bridges the finite balanced-pair elimination theorem to the actual
supported padded-completion count, in the original row/column coordinates.
-/

namespace ContingencyTables.FirstPaperPhysicalMarginal

open scoped BigOperators Classical
open LargePairEnumeration PhysicalLargeProfiles CompletionCounts
open RowColumnPenalties PaddedCompletions NestedPenaltyApplication BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def fullSoftFamily (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (a : ℝ) : (((I×J)×Bool) → ℕ) → ℝ :=
  softWeight cellLine (smallCoordinate small)
    (fullOffset B (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L)) viewSlope
    (smallOffset small B r c) viewSlope a

end ContingencyTables.FirstPaperPhysicalMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerSliceRestriction
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting fixed prefix coordinates

A context is fixed before the signed transport starts. Its coordinates
are removed from the transport index set, so leaf cliques cannot move a
hole into that prefix. The remaining removal form is a principal block.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal BalancedBox BinaryContraction

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]

omit [Fintype C] [Fintype D] in
lemma removeOne_fixed (c : C → ℕ) (z : D → ℕ) (i : D) :
    removeOne (Sum.elim c z) (.inr i) = Sum.elim c (removeOne z i) := by
  funext t
  rcases t with t | t <;> simp [removeOne]

omit [Fintype C] [Fintype D] in
lemma removeTwo_fixed (c : C → ℕ) (z : D → ℕ) (i j : D) :
    removeTwo (Sum.elim c z) (.inr i) (.inr j) = Sum.elim c (removeTwo z i j) := by
  simp only [removeTwo, removeOne_fixed]

omit [Fintype C] [Fintype D] in
lemma removalMatrix_fixed (F : ((C ⊕ D) → ℕ) → ℝ) (c : C → ℕ) (z : D → ℕ) :
    integerRemovalMatrix (fun x => F (Sum.elim c x)) z =
      (integerRemovalMatrix F (Sum.elim c z)).submatrix Sum.inr Sum.inr := by
  ext i j
  change (if ValidPair z i j then F (Sum.elim c (removeTwo z i j)) else 0) =
    if ValidPair (Sum.elim c z) (.inr i) (.inr j) then
      F (removeTwo (Sum.elim c z) (.inr i) (.inr j)) else 0
  simp only [ValidPair, Sum.elim_inr, Sum.inr.injEq, removeTwo_fixed]
  split_ifs <;> rfl

omit [DecidableEq C] [DecidableEq D] in
theorem positiveSlice_fixed (F : ((C ⊕ D) → ℕ) → ℝ) (mC c : C → ℕ) (mD : D → ℕ)
    (R : ℕ) (hc : InBox mC c)
    (hp : PositiveSlice F (Sum.elim mC mD) ((∑ i, c i)+R)) :
    PositiveSlice (fun x => F (Sum.elim c x)) mD R := by
  intro z hz ht
  apply hp
  · intro t
    rcases t with i | i
    · exact hc i
    · exact hz i
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ht]

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerCorrectionKernel
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal sum of future-slot correction kernels

Each summand gives exactly one unexposed ordinary pair occupancy M+1,
with multiplier a(M+1-a); every other pair is summed at its ordinary
balance. The coordinate changes below preserve complete configurations.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open BalancedFamily BalancedEnumeration IntegerMarginal

universe u

def exposePullback {I : Type u} (Ms : List ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ) :
    (Coordinates (I ⊕ Bool) Ms → ℕ) → ℝ :=
  fun x => F (x ∘ (exposeEquiv (I := I) Ms).symm)

lemma exposed_profile {I : Type u} (Ms : List ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (a b : ℕ) :
    exposedFamily Ms F (profile z a b) =
      eliminate Ms (fun x => F (profile x a b)) z := by
  unfold exposedFamily
  simp only [eliminate_eq_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [expose_embedding]

lemma expose_pair {I : Type u} (Ms : List ℕ) (V : ℕ)
    (x : Coordinates (I ⊕ Bool) Ms → ℕ) (a b : ℕ) :
    (profile x a b) ∘ (exposeEquiv (I := I) (V::Ms)).symm =
      (profile (x ∘ (exposeEquiv (I := I) Ms).symm) a b) ∘ swapPairs := by
  funext t
  rcases t with (i | c) | c <;> rfl

lemma exposed_double_profile {I : Type u} (Ms : List ℕ) (V : ℕ)
    (F : (((Coordinates I Ms ⊕ Bool) ⊕ Bool) → ℕ) → ℝ)
    (z : I → ℕ) (j k a b : ℕ) :
    exposedFamily Ms (exposePullback (V::Ms) F) (profile (profile z j k) a b) =
      eliminate Ms (fun x => F (profile (profile x a b) j k)) z := by
  unfold exposedFamily exposePullback
  simp only [eliminate_eq_sum]
  apply Finset.sum_congr rfl
  intro v _
  change F ((embedding Ms (profile (profile z j k) a b) v ∘
    (exposeEquiv (I := I ⊕ Bool) Ms).symm) ∘
    (exposeEquiv (I := I) (V::Ms)).symm) = _
  have he := expose_embedding Ms (profile z j k) a b v
  change embedding Ms (profile (profile z j k) a b) v ∘
    (exposeEquiv (I := I ⊕ Bool) Ms).symm = _ at he
  rw [he, expose_pair]
  have he' := expose_embedding Ms z j k v
  change embedding Ms (profile z j k) v ∘ (exposeEquiv (I := I) Ms).symm = _ at he'
  rw [he']
  exact congrArg F (profile_swap (embedding Ms z v) a b j k)

lemma eliminate_sum {I : Type u} {A : Type*} (Ms : List ℕ) (s : Finset A)
    (F : A → (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) :
    eliminate Ms (fun x => ∑ a ∈ s, F a x) z =
      ∑ a ∈ s, eliminate Ms (F a) z := by
  simp only [eliminate_eq_sum]
  rw [Finset.sum_comm]

/-- The same current and future profiles occur on both sides, including
the complete fixed-domain sum over every other ordinary slot. -/
lemma weighted_exposed_commute {I : Type u} (Ms : List ℕ) (U V : ℕ)
    (F : (((Coordinates I Ms ⊕ Bool) ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) :
    weightedFuture (exposedFamily Ms (marginal F U)) (V+1) z =
      marginal (weightedFuture (exposedFamily Ms (exposePullback (V::Ms) F)) (V+1)) U z := by
  unfold weightedFuture
  conv_lhs => tactic => simp_rw [exposed_profile, marginal, eliminate_sum, Finset.mul_sum]
  unfold marginal
  rw [Finset.sum_comm]
  simp_rw [exposed_double_profile]

lemma pullback_marginal {I : Type u} (Ms : List ℕ) (V : ℕ)
    (F : (((Coordinates I Ms ⊕ Bool) ⊕ Bool) → ℕ) → ℝ) :
    marginal (exposePullback (V::Ms) F) V =
      exposePullback Ms (marginal (fun x => F (x ∘ swapPairs)) V) := by
  funext x
  unfold marginal exposePullback
  apply Finset.sum_congr rfl
  intro j _
  rw [expose_pair]

lemma marginal_swap_commute {J : Type u} (F : (((J ⊕ Bool) ⊕ Bool) → ℕ) → ℝ)
    (U V : ℕ) :
    marginal (marginal F U) V = marginal (marginal (fun x => F (x ∘ swapPairs)) V) U := by
  funext z
  unfold marginal
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg F (profile_swap z a (V-a) j (U-j)).symm

noncomputable def correctionKernel {I : Type u} : (Ms : List ℕ) →
    ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → ℝ
  | [], _ => fun _ => 0
  | U::Ms, F => fun z => weightedFuture (exposedFamily Ms F) (U+1) z +
      correctionKernel Ms (marginal F U) z

theorem correctionKernel_nonnegative {I : Type u} (Ms : List ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (hF : ∀ x, 0 ≤ F x) (z : I → ℕ) :
    0 ≤ correctionKernel Ms F z := by
  induction Ms with
  | nil => exact le_rfl
  | cons U Ms ih =>
    apply add_nonneg
    · apply weightedFuture_nonnegative
      intro x
      exact eliminate_nonnegative Ms _ (fun p => hF _) x
    · apply ih
      intro x
      exact Finset.sum_nonneg (fun j _ => hF _)

/-- Summing the currently exposed pair commutes with the literal sum
of all the other future corrections. -/
theorem correctionKernel_current_commute : ∀ (Ms : List ℕ) {I : Type u}
    (U : ℕ) (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ),
    correctionKernel Ms (marginal F U) =
      marginal (correctionKernel Ms (exposePullback Ms F)) U := by
  intro Ms
  induction Ms with
  | nil => intro I U F; funext z; simp [correctionKernel, marginal]
  | cons V Ms ih =>
    intro I U F
    funext z
    change weightedFuture (exposedFamily Ms (marginal F U)) (V+1) z +
      correctionKernel Ms (marginal (marginal F U) V) z =
      ∑ j ∈ Finset.range (U+1),
        (weightedFuture (exposedFamily Ms (exposePullback (V::Ms) F)) (V+1)
          (profile z j (U-j)) +
        correctionKernel Ms (marginal (exposePullback (V::Ms) F) V) (profile z j (U-j)))
    rw [Finset.sum_add_distrib, weighted_exposed_commute, marginal_swap_commute]
    have ht := congrFun (ih U (marginal (fun x => F (x ∘ swapPairs)) V)) z
    rw [← pullback_marginal] at ht
    rw [ht]
    rfl

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerRecursivePotential
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Telescoping the actual raw integer recursion

The literal future kernel commutation and nonnegative square identity
control every future correction after a split. No signature property of
the weighted correction kernel is used.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures BalancedFamily BalancedEnumeration IntegerMarginal

universe u

variable {I : Type u} [Fintype I] [DecidableEq I]

lemma correction_future_lower (Ms : List ℕ) (U : ℕ) (hU : 2 ≤ U)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ)
    (h : I → ℝ) (g : ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (integerRemovalMatrix (correctionKernel Ms (marginal F U)) z).toBilin' h h ≤
      ∑ j : Fin (U+1),
        (integerRemovalMatrix (correctionKernel Ms (exposePullback Ms F))
          (profile z j.val (U-j.val))).toBilin'
          (extendCoefficients h (g j.val) (g (j.val+1)))
          (extendCoefficients h (g j.val) (g (j.val+1))) := by
  rw [correctionKernel_current_commute]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    (integerRemovalMatrix (correctionKernel Ms (exposePullback Ms F))
      (profile z j (U-j))).toBilin'
      (extendCoefficients h (g j) (g (j+1)))
      (extendCoefficients h (g j) (g (j+1)))) (U+1)]
  have ht := future_form_monotone (correctionKernel Ms (exposePullback Ms F)) z
    (U-2) h g (correctionKernel_nonnegative Ms _ (fun x => hF _))
  simpa only [show U-2+2=U by omega, show U-2+3=U+1 by omega, IntegerMarginal.pairMatrix] using ht

omit [Fintype I] in
lemma integerRemovalMatrix_add (F G : (I → ℕ) → ℝ) (z : I → ℕ) :
    integerRemovalMatrix (fun x => F x+G x) z =
      integerRemovalMatrix F z + integerRemovalMatrix G z := by
  ext i j
  simp only [integerRemovalMatrix, Matrix.add_apply]
  split_ifs <;> simp

lemma correction_form_cons (Ms : List ℕ) (U : ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ) :
    (integerRemovalMatrix (correctionKernel (U::Ms) F) z).toBilin' h h =
      (integerRemovalMatrix (weightedFuture (exposedFamily Ms F) (U+1)) z).toBilin' h h +
      (integerRemovalMatrix (correctionKernel Ms (marginal F U)) z).toBilin' h h := by
  rw [correctionKernel, integerRemovalMatrix_add]
  simp only [map_add, LinearMap.add_apply]

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerRootTransport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root transport with the actual auxiliary defect sum

The auxiliary kernel gives one ordinary slot occupancy M+1 and all
others their balances. Removing the two special coordinates leaves the
special slot negative, exactly the root defects in the manuscript.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open FactorialSignatures BalancedFamily BalancedEnumeration IntegerMarginal

universe u

noncomputable def auxiliaryKernel {I : Type u} : (Ms : List ℕ) →
    ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → ℝ
  | [], _ => fun _ => 0
  | U::Ms, F => fun z => marginal (exposedFamily Ms F) (U+1) z +
      auxiliaryKernel Ms (marginal F U) z

lemma weightedFuture_upper {I : Type u} (F : ((I ⊕ Bool) → ℕ) → ℝ)
    (M W : ℕ) (hM : M ≤ W+1) (hF : ∀ x, 0 ≤ F x) (z : I → ℕ) :
    weightedFuture F M z ≤ ((W:ℝ)+1)^2 * marginal F M z := by
  unfold weightedFuture marginal
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have haM : a ≤ M := by have := Finset.mem_range.mp ha; omega
  have haR : (a:ℝ) ≤ M := by exact_mod_cast haM
  have hMR : (M:ℝ) ≤ (W:ℝ)+1 := by exact_mod_cast hM
  apply mul_le_mul_of_nonneg_right _ (hF _)
  calc
    _ ≤ ((W:ℝ)+1)*((W:ℝ)+1) :=
      mul_le_mul (haR.trans hMR) (by linarith) (by linarith) (by positivity)
    _ = _ := by ring

theorem correctionKernel_upper {I : Type u} (Ms : List ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (W : ℕ)
    (hwidth : ∀ U ∈ Ms, U ≤ W) (hF : ∀ x, 0 ≤ F x) (z : I → ℕ) :
    correctionKernel Ms F z ≤ ((W:ℝ)+1)^2 * auxiliaryKernel Ms F z := by
  induction Ms with
  | nil => simp [correctionKernel,auxiliaryKernel]
  | cons U Ms ih =>
    have hcur := weightedFuture_upper (exposedFamily Ms F) (U+1) W
      (by have := hwidth U (by simp); omega)
      (fun x => eliminate_nonnegative Ms _ (fun p => hF _) _) z
    have htail := ih (marginal F U) (fun V hV => hwidth V (by simp [hV]))
      (fun x => Finset.sum_nonneg (fun j _ => hF _))
    change _+_ ≤ ((W:ℝ)+1)^2 * (_+_)
    linarith

lemma removal_nonnegative {C : Type*} [DecidableEq C] (F : (C → ℕ) → ℝ)
    (hF : ∀ x, 0 ≤ F x) (z : C → ℕ) (i j : C) :
    0 ≤ integerRemovalMatrix F z i j := by
  unfold integerRemovalMatrix
  split_ifs
  · exact hF _
  · exact le_rfl

lemma correction_offdiagonal_upper (Ms : List ℕ)
    (F : (Coordinates Bool Ms → ℕ) → ℝ) (W : ℕ)
    (hwidth : ∀ U ∈ Ms, U ≤ W) (hF : ∀ x, 0 ≤ F x) (z : Bool → ℕ) :
    integerRemovalMatrix (correctionKernel Ms F) z false true ≤
      ((W:ℝ)+1)^2 * integerRemovalMatrix (auxiliaryKernel Ms F) z false true := by
  unfold integerRemovalMatrix
  split_ifs
  · exact correctionKernel_upper Ms F W hwidth hF _
  · simp

lemma root_balance (f : (Bool → ℕ) → ℝ) (z : Bool → ℕ)
    (hs : 0 < oneHole f z false) (ht : 0 < oneHole f z true) :
    holeLinear f z (rootCoefficients (oneHole f z false) (oneHole f z true))=0 := by
  simp only [holeLinear,Fintype.sum_bool,rootCoefficients,Bool.false_eq_true,↓reduceIte]
  field_simp [ne_of_gt hs,ne_of_gt ht]
  ring

lemma root_holePotential (f : (Bool → ℕ) → ℝ) (z : Bool → ℕ)
    (hs : 0 < oneHole f z false) (ht : 0 < oneHole f z true) :
    holePotential f z (rootCoefficients (oneHole f z false) (oneHole f z true)) =
      1/oneHole f z false+1/oneHole f z true := by
  simpa only [holePotential,Fintype.sum_bool,rootCoefficients,
    Bool.false_eq_true,↓reduceIte] using root_potential _ _ hs ht

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerTransportLimit
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The hard-zero limit of the actual integer transport

The final bound contains only finite marginal and auxiliary defect sums,
minimum-endpoint graph energies, and the two positive endpoint masses.
Thus no limit of recursively defined coefficients is needed.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Topology
open FactorialSignatures BalancedFamily BalancedEnumeration IntegerMarginal Filter

universe u

variable {K : Type*} {l : Filter K}

lemma auxiliaryKernel_tendsto {I : Type u} (Ms : List ℕ)
    (F : K → (Coordinates I Ms → ℕ) → ℝ) (f : (Coordinates I Ms → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x))) (z : I → ℕ) :
    Tendsto (fun t => auxiliaryKernel Ms (F t) z) l (nhds (auxiliaryKernel Ms f z)) := by
  induction Ms with
  | nil => exact tendsto_const_nhds
  | cons U Ms ih =>
    apply Tendsto.add
    · unfold marginal
      apply tendsto_finsetSum
      intro j _
      exact eliminate_tendsto Ms _ _ (fun x => hlim _) _
    · apply ih
      intro x
      unfold marginal
      apply tendsto_finsetSum
      intro j _
      exact hlim _

lemma removal_tendsto {C : Type*} [DecidableEq C]
    (F : K → (C → ℕ) → ℝ) (f : (C → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x))) (z : C → ℕ) (i j : C) :
    Tendsto (fun t => integerRemovalMatrix (F t) z i j) l
      (nhds (integerRemovalMatrix f z i j)) := by
  by_cases hv : ValidPair z i j
  · simpa only [integerRemovalMatrix,hv,↓reduceIte] using hlim (removeTwo z i j)
  · simpa only [integerRemovalMatrix,hv,↓reduceIte] using
      (tendsto_const_nhds : Tendsto (fun _ : K => (0:ℝ)) l (nhds 0))

lemma oneHole_tendsto {C : Type*} [DecidableEq C]
    (F : K → (C → ℕ) → ℝ) (f : (C → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x))) (z : C → ℕ) (i : C) :
    Tendsto (fun t => oneHole (F t) z i) l (nhds (oneHole f z i)) := by
  by_cases hi : 0 < z i
  · simpa only [oneHole,hi,↓reduceIte] using hlim (removeOne z i)
  · simpa only [oneHole,hi,↓reduceIte] using
      (tendsto_const_nhds : Tendsto (fun _ : K => (0:ℝ)) l (nhds 0))

lemma root_linear_eq (g : (Bool → ℕ) → ℝ) (z : Bool → ℕ) (s t : ℝ) :
    holeLinear g z (rootCoefficients s t) = oneHole g z false/s-oneHole g z true/t := by
  simp only [holeLinear,Fintype.sum_bool,rootCoefficients,Bool.false_eq_true,↓reduceIte]
  ring

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerChildLogConcavity
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional child masses have no internal valley

The actual two-coordinate removal form gives the local log-concavity
inequality. The endpoint-minimum property passes to the hard-zero limit.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Topology Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal BalancedBox Filter

lemma bool_diagonal_product (A : Matrix Bool Bool ℝ)
    (hsymm : ∀ i j, A i j=A j i) (hsig : OnePositiveDirection A.toBilin')
    (haa : 0 < A false false) : A false false*A true true ≤ (A false true)^2 := by
  let ea : Bool → ℝ := Pi.single false 1
  let eb : Bool → ℝ := Pi.single true 1
  have ha : 0 < A.toBilin' ea ea := by
    simpa [ea,Matrix.toBilin'_apply] using haa
  have hp := (le_div_iff₀ ha).mp
    (positive_projection A.toBilin' (fun x y => (matrix_bilin_symm A hsymm).eq x y) hsig ea eb ha)
  simpa [ea,eb,Matrix.toBilin'_apply,mul_comm] using hp

lemma childProfile_inBox (U k : ℕ) (hk : k ≤ U) :
    InBox (fun _ : Bool => U) (childProfile U k) := by
  intro b
  cases b
  · exact hk
  · exact Nat.sub_le _ _

theorem child_logConcave (f : (Bool → ℕ) → ℝ) (U : ℕ)
    (hp : PositiveSlice f (fun _ => U) U) (hs : RemovalSlice f (fun _ => U) U)
    (k : ℕ) (hk : k+2 ≤ U) :
    f (childProfile U k)*f (childProfile U (k+2)) ≤ (f (childProfile U (k+1)))^2 := by
  let D : Bool → ℕ := fun b => if b then U-k else k+2
  have hDbox : InBox (fun _ : Bool => U) D := by
    intro b
    cases b
    · exact hk
    · exact Nat.sub_le _ _
  have hDsum : (∑ b, D b)=U+2 := by
    simp only [D,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte]
    omega
  have hsig := hs D hDbox hDsum
  have haa : integerRemovalMatrix f D false false=f (childProfile U k) := by
    have hv : ValidPair D false false := by simp [ValidPair,D]
    rw [integerRemovalMatrix,ite_eq_left hv]
    congr 1
    funext b
    cases b <;> simp [removeTwo,removeOne,D,childProfile]
  have hbb : integerRemovalMatrix f D true true=f (childProfile U (k+2)) := by
    have hv : ValidPair D true true := by simp [ValidPair,D]; omega
    rw [integerRemovalMatrix,ite_eq_left hv]
    congr 1
    funext b
    cases b
    · simp [removeTwo,removeOne,D,childProfile]
    · simp [removeTwo,removeOne,D,childProfile]
      omega
  have hab : integerRemovalMatrix f D false true=f (childProfile U (k+1)) := by
    have hv : ValidPair D false true := by simp [ValidPair,D]; omega
    rw [integerRemovalMatrix,ite_eq_left hv]
    congr 1
    funext b
    cases b
    · simp [removeTwo,removeOne,D,childProfile]
    · simp [removeTwo,removeOne,D,childProfile]
      omega
  have hpos : 0 < integerRemovalMatrix f D false false := by
    rw [haa]
    exact hp _ (childProfile_inBox U k (by omega)) (childProfile_total U k (by omega))
  have hdet := bool_diagonal_product _ (integerRemoval_symm f D) hsig hpos
  rwa [haa,hbb,hab] at hdet

theorem child_minimum (f : (Bool → ℕ) → ℝ) (U : ℕ)
    (hp : PositiveSlice f (fun _ => U) U) (hs : RemovalSlice f (fun _ => U) U)
    (a j b : ℕ) (haj : a ≤ j) (hjb : j ≤ b) (hbU : b ≤ U) :
    min (f (childProfile U a)) (f (childProfile U b)) ≤ f (childProfile U j) := by
  apply positive_sequence_minimum (fun k => f (childProfile U k)) U a j b
  · intro k hk
    exact hp _ (childProfile_inBox U k hk) (childProfile_total U k hk)
  · exact child_logConcave f U hp hs
  · exact haj
  · exact hjb
  · exact hbU

/-- Every mass between two positive hard children is at least the
smaller endpoint mass, including when other children have zero weight. -/
theorem child_minimum_limit {K : Type*} {l : Filter K} [l.NeBot]
    (F : K → (Bool → ℕ) → ℝ) (f : (Bool → ℕ) → ℝ) (U : ℕ)
    (hlim : ∀ z, Tendsto (fun t => F t z) l (nhds (f z)))
    (hsoft : ∀ᶠ t in l, PositiveSlice (F t) (fun _ => U) U ∧
      RemovalSlice (F t) (fun _ => U) U)
    (a j b : ℕ) (haj : a ≤ j) (hjb : j ≤ b) (hbU : b ≤ U) :
    min (f (childProfile U a)) (f (childProfile U b)) ≤ f (childProfile U j) := by
  apply le_of_tendsto_of_tendsto ((hlim _).min (hlim _)) (hlim _)
  filter_upwards [hsoft] with t ht
  exact child_minimum (F t) U ht.1 ht.2 a j b haj hjb hbU

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RepairPrefixes
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal repair values and row-major prefix preservation -/

namespace ContingencyTables

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [Fintype J] in
lemma IsDefect.negative_entry {x q : I → J → ℕ} {s t : I×J}
    (h : IsDefect x q s t) : q s.1 s.2=x s.1 s.2+1 := by
  have hst : ¬(s.1=t.1 ∧ s.2=t.2) := by
    rintro ⟨h1,h2⟩
    exact h.1 (Prod.ext h1 h2)
  have he := h.2 s.1 s.2
  simp only [transferInt,hst,↓reduceIte,and_self,sub_zero] at he
  omega

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RepairFibres
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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

def JointDefect (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (s t : I×J) :=
  {Z : RowColumnPair rbar cbar // IsDefect Z.val.1 Z.val.2 s t ∧
    (∀ i, smallRow small Z.val.1 i ≤ r i) ∧
    (∀ j, smallColumnView small Z.val.2 j ≤ c j)}

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallContextFibres
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual small-prefix fibres and conditional repair

Only small cells in the row-major prefix are fixed. Large completions
remain free and retain their full counting multiplicity.
-/

namespace ContingencyTables.SmallContextFibres

open scoped BigOperators Classical
open PaddedCompletions CompletionCounts
open FirstPaperPhysicalMarginal LargePairEnumeration

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def SmallJointDefectContext [LT I] [LT J]
    (small : I → J → Bool) (r rbar : I → ℕ) (c cbar : J → ℕ)
    (s t : I×J) (σ : I×J → ℕ) (l : ℕ) :=
  {Z : JointDefect small r c rbar cbar s t //
    SmallPrefix small s σ Z.val.val.1 ∧ Z.val.val.1 s.1 s.2=l-1}

end ContingencyTables.SmallContextFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallContextCoordinates
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual row-major small-prefix coordinate splitting

The retained prefix is precisely the earlier small cells. The remaining
ordinary cells all follow the next exposed cell, which is the condition
needed for the completion-retaining conditional repair injection.
-/

namespace ContingencyTables.SmallContextCoordinates

open scoped Classical
open LargePairEnumeration BalancedFamily

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

def Earlier (small : I → J → Bool) (s : I×J) := {a : Cells small // RowMajorBefore a.val s}
def Later (small : I → J → Bool) (s : I×J) := {a : Cells small // RowMajorBefore s a.val}

noncomputable instance earlierFintype [Fintype I] [Fintype J]
    (small : I → J → Bool) (s : I×J) : Fintype (Earlier small s) := by
  unfold Earlier
  infer_instance

noncomputable instance laterFintype [Fintype I] [Fintype J]
    (small : I → J → Bool) (s : I×J) : Fintype (Later small s) := by
  unfold Later
  infer_instance

noncomputable def cellSplitEquiv (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) :
    (Earlier small s ⊕ (Unit ⊕ Later small s)) ≃ Cells small where
  toFun
    | .inl a => a.val
    | .inr (.inl _) => ⟨s,hs⟩
    | .inr (.inr a) => a.val
  invFun a :=
    if hp : RowMajorBefore a.val s then .inl ⟨a,hp⟩
    else if he : a.val=s then .inr (.inl ())
    else .inr (.inr ⟨a,by
      rcases rowMajor_trichotomy a.val s with h|h|h
      · exact False.elim (hp h)
      · exact False.elim (he h)
      · exact h⟩)
  left_inv a := by
    cases a with
    | inl a =>
      simp only [dite_eq_left a.property]
      exact congrArg Sum.inl (Subtype.ext rfl)
    | inr a =>
      cases a with
      | inl a =>
        cases a
        have hp : ¬RowMajorBefore s s := fun h => h.ne rfl
        simp only [dite_eq_right hp,↓reduceDIte]
      | inr a =>
        have hp : ¬RowMajorBefore a.val.val s := fun h => (h.trans a.property).ne rfl
        have he : a.val.val≠s := a.property.ne.symm
        simp only [dite_eq_right hp,dite_eq_right he]
        exact congrArg Sum.inr (congrArg Sum.inr (Subtype.ext rfl))
  right_inv a := by
    by_cases hp : RowMajorBefore a.val s
    · simp only [dite_eq_left hp]
    · by_cases he : a.val=s
      · simp only [dite_eq_right hp,dite_eq_left he]
        exact Subtype.ext he.symm
      · simp only [dite_eq_right hp,dite_eq_right he]

/-- The exact small-coordinate bijection required by physical context
transport. The suffix enumeration introduces no extra assignment. -/
noncomputable def contextEquiv (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) {n : ℕ} (e : Fin n ≃ Later small s) (U : ℕ) :
    ((Earlier small s×Bool) ⊕ Coordinates Bool (widths (fun _ : Fin n => U))) ≃
      SmallView (fun a : I×J => small a.1 a.2) :=
  (Equiv.sumCongr (Equiv.refl _) ((coordinateEquiv Bool (fun _ : Fin n => U)).trans
    (Equiv.sumCongr (Equiv.refl Bool) (e.prodCongr (Equiv.refl Bool))))).trans
      ((splitPairEquiv _ _).trans ((cellSplitEquiv small s hs).prodCongr (Equiv.refl Bool)))

lemma contextEquiv_prefix (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) {n : ℕ} (e : Fin n ≃ Later small s) (U : ℕ)
    (a : Earlier small s) (b : Bool) :
    contextEquiv small s hs e U (.inl (a,b))=(a.val,b) := rfl

lemma contextEquiv_special (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) {n : ℕ} (e : Fin n ≃ Later small s) (U : ℕ) (b : Bool) :
    contextEquiv small s hs e U
      (.inr ((coordinateEquiv Bool (fun _ : Fin n => U)).symm (.inl b)))=(⟨s,hs⟩,b) := by
  simp only [contextEquiv,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inr,Sum.map_inl,Equiv.refl_apply,
    Equiv.apply_symm_apply]
  rfl

lemma contextEquiv_later (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) {n : ℕ} (e : Fin n ≃ Later small s) (U : ℕ)
    (a : Fin n) (b : Bool) :
    contextEquiv small s hs e U
      (.inr ((coordinateEquiv Bool (fun _ : Fin n => U)).symm (.inr (a,b))))=((e a).val,b) := by
  simp only [contextEquiv,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inr,
    Equiv.apply_symm_apply]
  rfl

end ContingencyTables.SmallContextCoordinates

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallContextEnumeration
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical enumeration of a balanced exposure child

Every later small-cell choice occurs once, with the retained prefix fixed.
The large-cell capacities remain the original capacities throughout.
-/

namespace ContingencyTables.SmallContextEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres
open LargePairEnumeration BalancedEnumeration BalancedFamily IntegerWeightedTransport
open FirstPaperPhysicalMarginal

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

noncomputable def splitChoices (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1))
    (y : Later small s → Fin (U+1)) : Cells small → Fin (U+1) :=
  (Sum.elim τ (Sum.elim (fun _ : Unit => k) y)) ∘ (cellSplitEquiv small s hs).symm

lemma splitChoices_prefix (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1))
    (y : Later small s → Fin (U+1)) (a : Earlier small s) :
    splitChoices small s hs U τ k y a.val=τ a := by
  change Sum.elim τ (Sum.elim (fun _ : Unit => k) y)
    ((cellSplitEquiv small s hs).symm ((cellSplitEquiv small s hs) (.inl a)))=τ a
  rw [Equiv.symm_apply_apply]
  rfl

lemma splitChoices_special (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1))
    (y : Later small s → Fin (U+1)) :
    splitChoices small s hs U τ k y ⟨s,hs⟩=k := by
  change Sum.elim τ (Sum.elim (fun _ : Unit => k) y)
    ((cellSplitEquiv small s hs).symm ((cellSplitEquiv small s hs) (.inr (.inl ()))))=k
  rw [Equiv.symm_apply_apply]
  rfl

lemma splitChoices_later (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1))
    (y : Later small s → Fin (U+1)) (a : Later small s) :
    splitChoices small s hs U τ k y a.val=y a := by
  change Sum.elim τ (Sum.elim (fun _ : Unit => k) y)
    ((cellSplitEquiv small s hs).symm ((cellSplitEquiv small s hs) (.inr (.inr a))))=y a
  rw [Equiv.symm_apply_apply]
  rfl

noncomputable def prefixChoices (small : I → J → Bool) (s : I×J)
    (σ : I×J → ℕ) (U : ℕ)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) : Earlier small s → Fin (U+1) :=
  fun a => ⟨σ a.val.val,Nat.lt_succ_of_le (hσ a)⟩

def prefixRaw (small : I → J → Bool) (s : I×J) (σ : I×J → ℕ) (U : ℕ) :
    Earlier small s×Bool → ℕ := fun a => if a.2 then U-σ a.1.val.val else σ a.1.val.val

noncomputable def reindexChoices {n U : ℕ} (small : I → J → Bool) (s : I×J)
    (e : Fin n ≃ Later small s) :
    (Fin n → Fin (U+1)) ≃ (Later small s → Fin (U+1)) where
  toFun y := y ∘ e.symm
  invFun y := y ∘ e
  left_inv y := by funext a; exact congrArg y (e.symm_apply_apply a)
  right_inv y := by funext a; exact congrArg y (e.apply_symm_apply a)

lemma embedding_coordinate_apply {n : ℕ} (M : Fin n → ℕ) (z : Bool → ℕ)
    (q : Assignments (widths M)) (a : Coordinates Bool (widths M)) :
    embedding (widths M) z q a=
      joinedProfile M z ((assignmentEquiv M) q) (coordinateEquiv Bool M a) := by
  have h := embedding_coordinate M z ((assignmentEquiv M) q) a
  simpa only [Equiv.symm_apply_apply] using h

end ContingencyTables.SmallContextEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerTruncatedTransport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Raw transport with the literal box and degree zero extension

Excess-pair auxiliary sums may visit profiles outside the original box.
Their zero extension is therefore retained in the auxiliary count and
energy. Balanced endpoint masses and numerators are unchanged.
-/

namespace ContingencyTables.IntegerBoxTruncation

open scoped BigOperators Classical Topology
open BalancedFamily BalancedBox FactorialSignatures IntegerWeightedTransport
open ProductIntegerSignature

variable {C : Type*} [Fintype C]

lemma truncate_nonnegative (f : (C → ℕ) → ℝ) (m : C → ℕ) (R : ℕ)
    (hf : ∀ x, 0 ≤ f x) (x : C → ℕ) : 0 ≤ truncate f m R x := by
  unfold truncate
  split_ifs
  · exact hf x
  · exact le_rfl

lemma truncate_mul (f H : (C → ℕ) → ℝ) (m : C → ℕ) (R : ℕ) :
    (fun x => truncate f m R x*H x)=truncate (fun x => f x*H x) m R := by
  funext x
  unfold truncate
  split_ifs <;> simp

lemma truncate_tendsto {K : Type*} {l : Filter K}
    (F : K → (C → ℕ) → ℝ) (f : (C → ℕ) → ℝ) (m : C → ℕ) (R : ℕ)
    (hlim : ∀ x, Filter.Tendsto (fun t => F t x) l (nhds (f x))) (x : C → ℕ) :
    Filter.Tendsto (fun t => truncate (F t) m R x) l (nhds (truncate f m R x)) := by
  by_cases hx : InBox m x ∧ (∑ i, x i)=R
  · simpa only [truncate,hx,and_self,↓reduceIte] using hlim x
  · simpa only [truncate,hx,and_self,↓reduceIte] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : K => (0:ℝ)) l (nhds 0))

lemma eliminate_truncate {I : Type*} [Fintype I]
    (Ms : List ℕ) (f : (Coordinates I Ms → ℕ) → ℝ) (m z : I → ℕ) (R : ℕ)
    (hz : InBox m z) (htotal : (∑ i, z i)=R) :
    eliminate Ms (truncate f (bounds m Ms) (R+Ms.sum)) z=eliminate Ms f z := by
  apply eliminate_congr_slice Ms m R _ f _ z hz htotal
  intro x hx ht
  simp only [truncate,hx,ht,↓reduceIte,and_self]

lemma active_removeOne_sum {I : Type*} [Fintype I] [DecidableEq I]
    (z : I → ℕ) (i : I) (hi : 0 < z i) :
    (∑ j, removeOne z i j)+1=∑ j, z j := by
  have he : (∑ j, z j)=(∑ j, (removeOne z i j+if j=i then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro j _
    unfold removeOne
    by_cases hj : j=i
    · subst j
      simp only [↓reduceIte]
      omega
    · simp only [hj,↓reduceIte,Nat.sub_zero,Nat.add_zero]
  rw [Finset.sum_add_distrib] at he
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte] using he.symm

lemma active_truncate_removal {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℕ) → ℝ) (m z : I → ℕ) (R : ℕ)
    (hz : InBox m z) (htotal : (∑ i, z i)=R+2) :
    integerRemovalMatrix (truncate f m R) z=integerRemovalMatrix f z := by
  ext i j
  unfold integerRemovalMatrix
  split_ifs with hv
  · have hb : InBox m (removeTwo z i j) := by
      intro k
      apply le_trans _ (hz k)
      unfold removeTwo removeOne
      omega
    have hi : 0 < z i := hv.1
    have hj : 0 < removeOne z i j := by
      simpa only [removeOne] using hv.2
    have h1 := active_removeOne_sum z i hi
    have h2 := active_removeOne_sum (removeOne z i) j hj
    have ht : (∑ k, removeTwo z i j k)=R := by
      unfold removeTwo
      omega
    simp only [truncate,hb,ht,and_self,↓reduceIte]
  · rfl

lemma truncate_all_slices {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℕ) → ℝ) (m : I → ℕ) (R : ℕ)
    (hf : ∀ x, 0 ≤ f x) (hp : PositiveSlice f m R) (hs : RemovalSlice f m R) :
    (∀ x, 0 ≤ truncate f m R x) ∧ PositiveSlice (truncate f m R) m R ∧
      RemovalSlice (truncate f m R) m R := by
  refine ⟨truncate_nonnegative f m R hf,?_,?_⟩
  · intro z hz ht
    simpa only [truncate,hz,ht,and_self,↓reduceIte] using hp z hz ht
  · intro z hz ht
    rw [active_truncate_removal f m z R hz ht]
    exact hs z hz ht

lemma oneHole_eliminate_truncate {I : Type*} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (f : (Coordinates I Ms → ℕ) → ℝ) (m z : I → ℕ) (R : ℕ)
    (hz : InBox m z) (htotal : (∑ i, z i)=R+1) (i : I) :
    oneHole (eliminate Ms (truncate f (bounds m Ms) (R+Ms.sum))) z i=
      oneHole (eliminate Ms f) z i := by
  by_cases hi : 0 < z i
  · simp only [oneHole,hi,↓reduceIte]
    apply eliminate_truncate Ms f m (removeOne z i) R
    · intro j
      apply le_trans _ (hz j)
      unfold removeOne
      omega
    · have h := active_removeOne_sum z i hi
      omega
  · simp only [oneHole,hi,↓reduceIte]

end ContingencyTables.IntegerBoxTruncation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerAuxiliaryEnumeration
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The auxiliary kernel enumerates exactly one excess ordinary pair

The finite assignment carries its excess-pair position. Its raw full
profile recovers the position and every choice uniquely. Box truncation
removes exactly the two inadmissible endpoints of that excess pair.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open BalancedFamily BalancedEnumeration IntegerMarginal BalancedBox
open IntegerBoxTruncation

/-- One distinguished ordinary pair has occupancy U+1. -/
@[reducible] def ExcessAssignments : List ℕ → Type
  | [] => Empty
  | U::Ms => (Assignments Ms × Fin (U+2)) ⊕ (ExcessAssignments Ms × Fin (U+1))

@[reducible] instance excessAssignmentsFintype (Ms : List ℕ) : Fintype (ExcessAssignments Ms) := by
  induction Ms with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons U Ms ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((Assignments Ms × Fin (U+2)) ⊕
      (ExcessAssignments Ms × Fin (U+1))))

def excessEmbedding {I : Type*} : (Ms : List ℕ) → (I → ℕ) →
    ExcessAssignments Ms → Coordinates I Ms → ℕ
  | [],_,a => Empty.elim a
  | U::Ms,z,.inl a => profile (embedding Ms z a.1) a.2.val (U+1-a.2.val)
  | U::Ms,z,.inr a => profile (excessEmbedding Ms z a.1) a.2.val (U-a.2.val)

def ValidExcess : (Ms : List ℕ) → ExcessAssignments Ms → Prop
  | [],a => Empty.elim a
  | U::_,.inl a => 0 < a.2.val ∧ a.2.val ≤ U
  | _::Ms,.inr a => ValidExcess Ms a.1

/-- Exact finite expansion of the actual recursive auxiliary kernel. -/
theorem auxiliaryKernel_eq_excess_sum {I : Type*} (Ms : List ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) :
    auxiliaryKernel Ms F z=∑ a : ExcessAssignments Ms, F (excessEmbedding Ms z a) := by
  induction Ms with
  | nil => simp only [auxiliaryKernel,ExcessAssignments,Finset.univ_eq_empty,Finset.sum_empty]
  | cons U Ms ih =>
    change marginal (exposedFamily Ms F) (U+1) z+auxiliaryKernel Ms (marginal F U) z=
      ∑ a : (Assignments Ms × Fin (U+2)) ⊕ (ExcessAssignments Ms × Fin (U+1)),
        F (excessEmbedding (U::Ms) z a)
    rw [Fintype.sum_sum_type]
    congr 1
    · unfold marginal exposedFamily
      simp_rw [eliminate_eq_sum,expose_embedding]
      rw [Finset.sum_comm,Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      exact (Fin.sum_univ_eq_sum_range
        (fun j => F (profile (embedding Ms z a) j (U+1-j))) (U+2)).symm
    · rw [ih,Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      unfold marginal
      exact (Fin.sum_univ_eq_sum_range
        (fun j => F (profile (excessEmbedding Ms z a) j (U-j))) (U+1)).symm

lemma excessEmbedding_injective {I : Type*} (Ms : List ℕ) (z : I → ℕ) :
    Function.Injective (excessEmbedding Ms z) := by
  induction Ms with
  | nil => intro a; exact Empty.elim a
  | cons U Ms ih =>
    intro a b he
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have hj := congrFun he (.inr false)
        change a.2.val=b.2.val at hj
        have ho : embedding Ms z a.1=embedding Ms z b.1 := by
          funext i
          exact congrFun he (.inl i)
        exact congrArg Sum.inl (Prod.ext (embedding_injective Ms z ho) (Fin.ext hj))
      | inr b =>
        have hj := congrFun he (.inr false)
        have hk := congrFun he (.inr true)
        change a.2.val=b.2.val at hj
        change U+1-a.2.val=U-b.2.val at hk
        have ha := a.2.isLt
        have hb := b.2.isLt
        omega
    | inr a =>
      cases b with
      | inl b =>
        have hj := congrFun he (.inr false)
        have hk := congrFun he (.inr true)
        change a.2.val=b.2.val at hj
        change U-a.2.val=U+1-b.2.val at hk
        have ha := a.2.isLt
        have hb := b.2.isLt
        omega
      | inr b =>
        have hj := congrFun he (.inr false)
        change a.2.val=b.2.val at hj
        have ho : excessEmbedding Ms z a.1=excessEmbedding Ms z b.1 := by
          funext i
          exact congrFun he (.inl i)
        exact congrArg Sum.inr (Prod.ext (ih ho) (Fin.ext hj))

lemma excessEmbedding_total {I : Type*} [Fintype I] (Ms : List ℕ)
    (z : I → ℕ) (a : ExcessAssignments Ms) :
    (∑ i, excessEmbedding Ms z a i)=(∑ i, z i)+Ms.sum+1 := by
  induction Ms with
  | nil => exact Empty.elim a
  | cons U Ms ih =>
    cases a with
    | inl a =>
      change (∑ i, profile (embedding Ms z a.1) a.2.val (U+1-a.2.val) i)=_
      rw [profile_total,embedding_total]
      have ha := a.2.isLt
      simp only [List.sum_cons]
      omega
    | inr a =>
      change (∑ i, profile (excessEmbedding Ms z a.1) a.2.val (U-a.2.val) i)=_
      rw [profile_total,ih]
      have ha := a.2.isLt
      simp only [List.sum_cons]
      omega

lemma excessEmbedding_inBox_iff {I : Type*} (Ms : List ℕ) (m z : I → ℕ)
    (hz : InBox m z) (a : ExcessAssignments Ms) :
    InBox (bounds m Ms) (excessEmbedding Ms z a) ↔ ValidExcess Ms a := by
  induction Ms with
  | nil => exact Empty.elim a
  | cons U Ms ih =>
    cases a with
    | inl a =>
      constructor
      · intro h
        have ha := h (.inr false)
        have hb := h (.inr true)
        change a.2.val ≤ U at ha
        change U+1-a.2.val ≤ U at hb
        change 0 < a.2.val ∧ a.2.val ≤ U
        omega
      · intro h
        apply profile_inBox (bounds m Ms) (embedding Ms z a.1) U a.2.val (U+1-a.2.val)
        · exact embedding_inBox Ms m z hz a.1
        · exact h.2
        · have ha := h.1
          omega
    | inr a =>
      constructor
      · intro h
        apply (ih a.1).mp
        intro i
        exact h (.inl i)
      · intro h
        apply profile_inBox (bounds m Ms) (excessEmbedding Ms z a.1) U a.2.val (U-a.2.val)
        · exact (ih a.1).mpr h
        · have ha := a.2.isLt
          omega
        · exact Nat.sub_le _ _

/-- The zero-extended auxiliary count includes precisely the admissible
single-excess-pair profiles, each once. -/
theorem auxiliaryKernel_truncate_eq_valid_sum {I : Type*} [Fintype I]
    (Ms : List ℕ) (F : (Coordinates I Ms → ℕ) → ℝ) (m z : I → ℕ) (R : ℕ)
    (hz : InBox m z) (htotal : (∑ i, z i)+1=R) :
    auxiliaryKernel Ms (truncate F (bounds m Ms) (R+Ms.sum)) z=
      ∑ a ∈ Finset.univ.filter (ValidExcess Ms), F (excessEmbedding Ms z a) := by
  rw [auxiliaryKernel_eq_excess_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  have ht : (∑ i, excessEmbedding Ms z a i)=R+Ms.sum := by
    rw [excessEmbedding_total]
    omega
  simp only [truncate,ht,excessEmbedding_inBox_iff Ms m z hz a,and_true]

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ExcessPairCoordinates
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unique excess pair in physical finite coordinates -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open BalancedFamily BalancedEnumeration LargePairEnumeration IntegerMarginal

lemma embedding_root {S : Type*} {n : ℕ} (M : Fin n → ℕ) (z : S → ℕ)
    (q : Assignments (widths M)) (s : S) :
    embedding (widths M) z q ((coordinateEquiv S M).symm (.inl s))=z s := by
  have h := embedding_coordinate M z ((assignmentEquiv M) q)
    ((coordinateEquiv S M).symm (.inl s))
  simpa only [Equiv.symm_apply_apply,Equiv.apply_symm_apply,joinedProfile] using h

lemma embedding_pair_total {S : Type*} {n : ℕ} (M : Fin n → ℕ) (z : S → ℕ)
    (q : Assignments (widths M)) (i : Fin n) :
    embedding (widths M) z q ((coordinateEquiv S M).symm (.inr (i,false)))+
      embedding (widths M) z q ((coordinateEquiv S M).symm (.inr (i,true)))=M i := by
  have hfalse := embedding_coordinate M z ((assignmentEquiv M) q)
    ((coordinateEquiv S M).symm (.inr (i,false)))
  have htrue := embedding_coordinate M z ((assignmentEquiv M) q)
    ((coordinateEquiv S M).symm (.inr (i,true)))
  simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply,joinedProfile,
    Bool.false_eq_true,↓reduceIte] at hfalse htrue
  rw [hfalse,htrue]
  have hb := ((assignmentEquiv M) q i).isLt
  omega

def excessIndex : {n : ℕ} → (M : Fin n → ℕ) → ExcessAssignments (widths M) → Fin n
  | 0,_,q => Empty.elim q
  | _+1,_,.inl _ => 0
  | _+1,M,.inr q => (excessIndex (fun i => M i.succ) q.1).succ

lemma excessEmbedding_root {S : Type*} {n : ℕ} (M : Fin n → ℕ) (z : S → ℕ)
    (q : ExcessAssignments (widths M)) (s : S) :
    excessEmbedding (widths M) z q ((coordinateEquiv S M).symm (.inl s))=z s := by
  induction n with
  | zero => exact Empty.elim q
  | succ n ih =>
    cases q with
    | inl q =>
      change embedding (widths (fun i => M i.succ)) z q.1
        ((coordinateEquiv S (fun i => M i.succ)).symm (.inl s))=z s
      exact embedding_root (fun i => M i.succ) z q.1 s
    | inr q =>
      change excessEmbedding (widths (fun i => M i.succ)) z q.1
        ((coordinateEquiv S (fun i => M i.succ)).symm (.inl s))=z s
      exact ih (fun i => M i.succ) q.1

/-- The raw finite profile recovers the distinguished position by its
pair total; all other pairs have their original total. -/
lemma excessEmbedding_pair_total {S : Type*} {n : ℕ} (M : Fin n → ℕ) (z : S → ℕ)
    (q : ExcessAssignments (widths M)) (i : Fin n) :
    excessEmbedding (widths M) z q ((coordinateEquiv S M).symm (.inr (i,false)))+
      excessEmbedding (widths M) z q ((coordinateEquiv S M).symm (.inr (i,true)))=
      M i+if i=excessIndex M q then 1 else 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases q with
    | inl q =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change q.2.val+(M 0+1-q.2.val)=M 0+if (0 : Fin (n+1))=0 then 1 else 0
        have hb := q.2.isLt
        simp only [↓reduceIte]
        omega
      · change embedding (widths (fun j => M j.succ)) z q.1
            ((coordinateEquiv S (fun j => M j.succ)).symm (.inr (j,false)))+
          embedding (widths (fun j => M j.succ)) z q.1
            ((coordinateEquiv S (fun j => M j.succ)).symm (.inr (j,true)))=M j.succ+if j.succ=0 then 1 else 0
        rw [embedding_pair_total]
        simp only [Fin.succ_ne_zero,↓reduceIte,add_zero]
    | inr q =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change q.2.val+(M 0-q.2.val)=M 0+
          if (0 : Fin (n+1))=(excessIndex (fun j => M j.succ) q.1).succ then 1 else 0
        have hb := q.2.isLt
        have hn : (0 : Fin (n+1))≠(excessIndex (fun j => M j.succ) q.1).succ :=
          (Fin.succ_ne_zero _).symm
        simp only [hn,↓reduceIte,add_zero]
        omega
      · change excessEmbedding (widths (fun j => M j.succ)) z q.1
            ((coordinateEquiv S (fun j => M j.succ)).symm (.inr (j,false)))+
          excessEmbedding (widths (fun j => M j.succ)) z q.1
            ((coordinateEquiv S (fun j => M j.succ)).symm (.inr (j,true)))=M j.succ+
          if j.succ=(excessIndex (fun j => M j.succ) q.1).succ then 1 else 0
        rw [ih]
        simp only [Fin.succ_inj]

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ExcessContextProfiles
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical defect profiles in the auxiliary context kernel -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma auxRoot_inBox (U l : ℕ) (hl : l ≤ U) : InBox (fun _ => U) (auxRoot U l) := by
  intro b
  cases b
  · exact (Nat.sub_le _ _).trans hl
  · exact Nat.sub_le _ _

lemma bounds_constant (U : ℕ) {n : ℕ} :
    bounds (fun _ : Bool => U) (widths (fun _ : Fin n => U))=(fun _ => U) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext a
    cases a with
    | inl a => exact congrFun ih a
    | inr b => cases b <;> rfl

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_AuxiliaryRepairMass
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional repair bounds the literal auxiliary kernel mass -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport
open FirstPaperPhysicalMarginal IntegerBoxTruncation
open PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

abbrev ValidAssignments (U n : ℕ) :=
  {q : ExcessAssignments (widths (fun _ : Fin n => U)) // ValidExcess _ q}

noncomputable instance validAssignmentsFintype (U n : ℕ) : Fintype (ValidAssignments U n) :=
  inferInstanceAs (Fintype {q : ExcessAssignments (widths (fun _ : Fin n => U)) // ValidExcess _ q})

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ContextAdjacentTransport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adjacent physical exposure means with the repaired coefficient -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport
open FirstPaperPhysicalMarginal IntegerBoxTruncation
open PaddedCompletions CompletionCounts FactorialSignatures

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma rootDisplay_inBox (U l : ℕ) (hl0 : 1 ≤ l) (hlU : l ≤ U) :
    InBox (fun _ : Bool => U) (rootDisplay U l) := by
  intro b
  cases b
  · exact hlU
  · change U-l+1 ≤ U
    omega

lemma rootDisplay_remove_false (U l : ℕ) (hl0 : 1 ≤ l) (hlU : l ≤ U) :
    removeOne (rootDisplay U l) false=childProfile U (l-1) := by
  funext b
  cases b <;> simp only [removeOne,rootDisplay,childProfile,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte]
  omega

lemma rootDisplay_remove_true (U l : ℕ) :
    removeOne (rootDisplay U l) true=childProfile U l := by
  funext b
  cases b <;> simp [removeOne,rootDisplay,childProfile]

lemma rootDisplay_remove_two (U l : ℕ) :
    removeTwo (rootDisplay U l) false true=auxRoot U l := by
  funext b
  cases b <;> simp [removeTwo,removeOne,rootDisplay,auxRoot]

lemma rootDisplay_oneHole_false (F : (Bool → ℕ) → ℝ) (U l : ℕ)
    (hl0 : 1 ≤ l) (hlU : l ≤ U) :
    oneHole F (rootDisplay U l) false=F (childProfile U (l-1)) := by
  rw [oneHole,ite_eq_left (show 0 < rootDisplay U l false by exact hl0),
    rootDisplay_remove_false U l hl0 hlU]

lemma rootDisplay_oneHole_true (F : (Bool → ℕ) → ℝ) (U l : ℕ) :
    oneHole F (rootDisplay U l) true=F (childProfile U l) := by
  rw [oneHole,ite_eq_left (show 0 < rootDisplay U l true by change 0 < U-l+1; omega),
    rootDisplay_remove_true]

lemma rootDisplay_removal (F : (Bool → ℕ) → ℝ) (U l : ℕ) (hl0 : 1 ≤ l) :
    integerRemovalMatrix F (rootDisplay U l) false true=F (auxRoot U l) := by
  have hv : ValidPair (rootDisplay U l) false true := by
    simp only [ValidPair,rootDisplay,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte]
    omega
  rw [integerRemovalMatrix,ite_eq_left hv,rootDisplay_remove_two]

lemma prefixRaw_inBox (small : I → J → Bool) (s : I×J) (σ : I×J → ℕ) (U : ℕ)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) :
    InBox (fun _ : Earlier small s×Bool => U) (prefixRaw small s σ U) := by
  rintro ⟨a,b⟩
  cases b
  · exact hσ a
  · exact Nat.sub_le _ _

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerChildVariance
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Between-child variance from raw integer transport

The no-valley bound for child masses turns adjacent transport into a
bound on every pair of child means. Finite Cauchy--Schwarz and the exact
weighted pair formula then bound the between-child variance.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open CommonBasesFPRAS

/-- Exact unnormalized weighted variance pair formula. -/
lemma finite_weighted_variance_pair {X : Type*} [Fintype X] (w H : X → ℝ)
    (hZ : 0 < ∑ x, w x) :
    (∑ x, w x*(H x-(∑ y, w y*H y)/(∑ y, w y))^2)=
      (∑ x, ∑ y, w x*w y/(∑ k, w k)*(H x-H y)^2)/2 := by
  have hc := finite_center_at_mean Finset.univ w H (ne_of_gt hZ)
  rw [hc]
  have he : (∑ x, ∑ y, w x*w y/(∑ k, w k)*(H x-H y)^2)=
      (∑ x, ∑ y, w x*w y*(H x-H y)^2)/(∑ k, w k) := by
    simp_rw [div_mul_eq_mul_div,←Finset.sum_div]
  rw [he,finite_pair_square]
  field_simp

/-- The paper's between-child estimate, including zero-mass children. -/
theorem child_variance_bound (z H : ℕ → ℝ) (U : ℕ) (A E : ℝ)
    (hz : ∀ j ≤ U, 0 ≤ z j) (hZ : 0 < ∑ j : Fin (U+1), z j.val)
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hminimum : ∀ a j b, a ≤ j → j ≤ b → b ≤ U → min (z a) (z b) ≤ z j)
    (hadj : ∀ j, j < U → min (z j) (z (j+1))*(H j-H (j+1))^2 ≤ A*E) :
    (∑ j : Fin (U+1), z j.val*(H j.val-
      (∑ k : Fin (U+1), z k.val*H k.val)/(∑ k : Fin (U+1), z k.val))^2) ≤
      ((U:ℝ)+1)^4*A*E := by
  have hzZ (j : ℕ) (hj : j ≤ U) : z j ≤ ∑ k : Fin (U+1), z k.val := by
    exact Finset.single_le_sum (fun k _ => hz k.val (by omega))
      (Finset.mem_univ (⟨j,by omega⟩ : Fin (U+1)))
  rw [finite_weighted_variance_pair _ _ hZ]
  have hp (a b : Fin (U+1)) := child_pair_path_bound z H U a.val b.val _ A E hz hZ hzZ
    hA hE hminimum hadj (by omega) (by omega)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun b _ => hp a b))
  have hsum' : (∑ a : Fin (U+1), ∑ b : Fin (U+1),
      z a.val*z b.val/(∑ k : Fin (U+1), z k.val)*(H a.val-H b.val)^2) ≤
      ((U:ℝ)+1)^2*(U:ℝ)^2*A*E := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_one] at hsum
    convert hsum using 1 <;> first | rfl | ring
  have hAE : 0 ≤ A*E := mul_nonneg hA hE
  have hU : 0 ≤ (U:ℝ) := Nat.cast_nonneg _
  have hpow : ((U:ℝ)+1)^2*(U:ℝ)^2 ≤ ((U:ℝ)+1)^4 := by
    have hsq : (U:ℝ)^2 ≤ ((U:ℝ)+1)^2 := by nlinarith
    convert mul_le_mul_of_nonneg_left hsq (sq_nonneg ((U:ℝ)+1)) using 1 <;> first | rfl | ring
  have hb := mul_le_mul_of_nonneg_right hpow hAE
  nlinarith

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteExposureVariance
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite exposure variance with zero-mass children

The exact variance decomposition uses only finite nonnegative weights.
A child of mass zero has zero moment, so its mean can be set to zero.
This is the algebraic decomposition iterated by the small-slot exposure.
-/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical
open CommonBasesFPRAS

variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype Y] in
/-- The second-moment identity also holds at mass zero. -/
lemma variance_formula (w H : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    variance w H=(∑ x, w x*(H x)^2)-(∑ x, w x*H x)^2/(∑ x, w x) := by
  by_cases hz : (∑ x, w x)=0
  · have h := zero_mass_weights w hw hz
    simp only [variance,h,zero_mul,Finset.sum_const_zero,zero_pow,ne_eq,
      OfNat.ofNat_ne_zero,not_false_eq_true,div_zero,sub_zero]
  · exact finite_center_at_mean Finset.univ w H hz

/-- Exact conditional variance decomposition, allowing arbitrary
zero-mass child fibres and a zero-mass whole space. -/
theorem variance_split (w H : Y → X → ℝ) (hw : ∀ y x, 0 ≤ w y x) :
    variance (fun p : X×Y => w p.2 p.1) (fun p => H p.2 p.1)=
      (∑ y, variance (w y) (H y))+
        variance (fun y => ∑ x, w y x) (fun y => mean (w y) (H y)) := by
  have hmass : (∑ y, ∑ x, w y x)=(∑ p : X×Y, w p.2 p.1) := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
  have hmoment : (∑ y, (∑ x, w y x)*mean (w y) (H y))=
      ∑ p : X×Y, w p.2 p.1*H p.2 p.1 := by
    simp_rw [mean_moment _ _ (hw _)]
    rw [Fintype.sum_prod_type,Finset.sum_comm]
  have hsecond : (∑ y, (∑ x, w y x)*(mean (w y) (H y))^2)=
      ∑ y, (∑ x, w y x*H y x)^2/(∑ x, w y x) := by
    simp_rw [mean_second]
  have hsquares : (∑ y, ∑ x, w y x*(H y x)^2)=
      ∑ p : X×Y, w p.2 p.1*(H p.2 p.1)^2 := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
  rw [variance_formula (fun p : X×Y => w p.2 p.1) (fun p => H p.2 p.1) (fun p => hw p.2 p.1),
    variance_formula (fun y : Y => ∑ x, w y x) (fun y => mean (w y) (H y))
      (fun y => Finset.sum_nonneg (fun x _ => hw y x))]
  have hchild (y : Y) := variance_formula (w y) (H y) (hw y)
  simp_rw [hchild]
  rw [Finset.sum_sub_distrib,hmass,hmoment,hsecond,hsquares]
  ring

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ContextChildVariance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Between-child variance for actual physical exposure contexts -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u

noncomputable def contextVertices (U n : ℕ) :
    Finset (Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ) :=
  Finset.univ.biUnion (fun l : Fin (U+1) => leafVertices _ (rootDisplay U l.val))

lemma leafVertices_subset_context (U n l : ℕ) (hl : l ≤ U) :
    leafVertices (widths (fun _ : Fin n => U)) (rootDisplay U l) ⊆ contextVertices U n := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨⟨l,Nat.lt_succ_of_le hl⟩,Finset.mem_univ _,hx⟩

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ContextGraphMembership
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Context leaf vertices are actual balanced or single-defect states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport ExcessContextProfiles FactorialSignatures

universe u

lemma pair_total_removeOne {C : Type*} [DecidableEq C]
    (D : C×Bool → ℕ) (c a : C) (b : Bool) (hd : 0 < D (c,b)) :
    removeOne D (c,b) (a,false)+removeOne D (c,b) (a,true)=
      D (a,false)+D (a,true)-(if a=c then 1 else 0) := by
  by_cases ha : a=c
  · subst a
    cases b <;> simp only [removeOne,Prod.mk.injEq,Bool.false_eq_true,
      Bool.true_eq_false,↓reduceIte,and_false,Nat.sub_zero] at hd ⊢ <;> omega
  · simp only [removeOne,Prod.mk.injEq,ha,false_and,↓reduceIte,Nat.sub_zero]

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileRepairProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for the literal small-profile repair -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma listDifference_ofFn {n : ℕ} (b v : Fin n → ℕ) :
    listDifference (List.ofFn b,List.ofFn v)=List.ofFn (fun i => b i-v i) := by
  apply List.ext_getElem
  · simp only [listDifference,List.length_map,List.length_range,List.length_ofFn]
  · intro a ha _
    have han : a<n := by
      simpa only [listDifference,List.length_map,List.length_range,List.length_ofFn] using ha
    simp only [listDifference,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      differenceEntry,List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using han),
      List.getElem?_eq_getElem (by simpa using han)]
    simp only [Option.getD_some,List.getElem_ofFn]

/-- Natural indices permit the receiver to be absent from the list. -/
lemma listExchange_ofFn_nat {n : ℕ} (v : Fin n → ℕ) (i j : ℕ) :
    listExchange (List.ofFn v,(i,j))=
      List.ofFn (fun a => v a+(if a.val=i then 1 else 0)-(if a.val=j then 1 else 0)) := by
  apply List.ext_getElem
  · simp only [listExchange,List.length_map,List.length_range,List.length_ofFn]
  · intro a ha _
    have han : a<n := by
      simpa only [listExchange,List.length_map,List.length_range,List.length_ofFn] using ha
    simp only [listExchange,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      exchangeEntry,List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using han)]
    simp only [Option.getD_some,List.getElem_ofFn]

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates
open ProfilePrograms

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]
variable (small : I → J → Bool) {n : ℕ} (e : Fin n ≃ Cells small)

/-- An absent large cell receives the out-of-range code `n`. -/
def cellIndex (t : I×J) : ℕ :=
  if h : small t.1 t.2=true then (e.symm ⟨t,h⟩).val else n

omit [LinearOrder I] [LinearOrder J] in
lemma cellIndex_eq (i : Fin n) (t : I×J) :
    i.val=cellIndex small e t ↔ (e i).val=t := by
  unfold cellIndex
  split_ifs with ht
  · constructor
    · intro h
      have hi : i=e.symm ⟨t,ht⟩ := Fin.ext h
      rw [hi,Equiv.apply_symm_apply]
    · intro h
      have he : e i=⟨t,ht⟩ := Subtype.ext h
      have hi := congrArg e.symm he
      simpa only [Equiv.symm_apply_apply] using congrArg Fin.val hi
  · constructor
    · intro h
      exact False.elim (Nat.ne_of_lt i.isLt h)
    · intro h
      exact False.elim (ht (h ▸ (e i).property))

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallCellIndexProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable indices for small cells and their crossing cells -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

lemma cellCatalog_nodup : (cellCatalog small e).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  apply e.injective
  apply Subtype.ext
  exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

lemma mem_cellCatalog (t : Fin m×Fin n) :
    (t.1.val,t.2.val)∈cellCatalog small e ↔ small t.1 t.2=true := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
    have he : (e i).val=t := Prod.ext (Fin.ext (congrArg Prod.fst hi))
      (Fin.ext (congrArg Prod.snd hi))
    exact he ▸ (e i).property
  · intro h
    apply List.mem_ofFn.mpr
    exact ⟨e.symm ⟨t,h⟩,by simp only [Equiv.apply_symm_apply]⟩

/-- Ordinary list search gives precisely the semantic small-cell index;
large crossing cells get the out-of-range index without extra cases. -/
theorem cellCatalog_index (t : Fin m×Fin n) :
    (cellCatalog small e).idxOf (t.1.val,t.2.val)=cellIndex small e t := by
  by_cases ht : small t.1 t.2=true
  · let i := e.symm ⟨t,ht⟩
    have hi : (cellCatalog small e)[i.val]'(by simp only [cellCatalog,List.length_ofFn]; exact i.isLt)=
        (t.1.val,t.2.val) := by
      simp only [cellCatalog,List.getElem_ofFn]
      change ((e i).val.1.val,(e i).val.2.val)=(t.1.val,t.2.val)
      simp only [i,Equiv.apply_symm_apply]
    rw [←hi]
    rw [(cellCatalog_nodup small e).idxOf_getElem]
    exact (cellIndex_eq small e i t).mpr (by simp only [i,Equiv.apply_symm_apply])
  · rw [List.idxOf_eq_length ((mem_cellCatalog small e t).not.mpr ht)]
    simp only [cellCatalog,List.length_ofFn,cellIndex,dite_eq_right ht]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RowMajorEnumeration
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

omit [LinearOrder I] [LinearOrder J] in
lemma small_card_le_dimension (small : I → J → Bool) :
    Fintype.card (Cells small) ≤ Fintype.card I*Fintype.card J := by
  exact (Fintype.card_le_of_injective (fun a : Cells small => a.val) Subtype.val_injective).trans_eq
    (Fintype.card_prod I J)

end ContingencyTables.RowMajorEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperExposureVariance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual first-paper per-context exposure variance bound -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open LargePairEnumeration BalancedFamily BalancedBox IntegerWeightedTransport
open FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma later_card_le_allowance (small : I → J → Bool) (s : I×J) {n : ℕ}
    (e : Fin n ≃ Later small s) : n ≤ dimensionAllowance (I := I) (J := J) := by
  have hn : n=Fintype.card (Later small s) := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  rw [hn]
  exact (Fintype.card_le_of_injective (fun a : Later small s => a.val) Subtype.val_injective).trans
    ((RowMajorEnumeration.small_card_le_dimension small).trans dimension_le_allowance)

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FinitePartitionVariance
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact variance decomposition for finite physical prefix partitions -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

variable {X C D : Type*} [Fintype X] [Fintype C] [Fintype D]

omit [Fintype D] in
theorem variance_partition (w H : X → ℝ) (hw : ∀ x,0 ≤ w x) (π : X → C) :
    variance w H=(∑ c,variance (fibreWeight w π c) H)+
      variance (fun c => ∑ x,fibreWeight w π c x)
        (fun c => mean (fibreWeight w π c) H) := by
  have hw' : ∀ c x,0 ≤ fibreWeight w π c x := fibreWeight_nonnegative w hw π
  have hsplit := variance_split (fibreWeight w π) (fun _ => H) hw'
  have he : variance (fun p : X×C => fibreWeight w π p.2 p.1) (fun p => H p.1)=variance w H := by
    rw [variance_formula (fun p : X×C => fibreWeight w π p.2 p.1)
      (fun p => H p.1) (fun p => hw' p.2 p.1),variance_formula w H hw]
    simp only [Fintype.sum_prod_type,fibreWeight,ite_mul,zero_mul,
      Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]
  rw [he] at hsplit
  exact hsplit

/-- Refining a physical prefix adds exactly its between-child variance.
All zero fibres are retained and contribute zero. -/
theorem partition_refinement (w H : X → ℝ) (hw : ∀ x,0 ≤ w x)
    (π : X → C) (ρ : X → D) :
    partitionVariance w H π=partitionVariance w H (fun x => (π x,ρ x))+
      partitionContribution w H π ρ := by
  have h (c : C) := variance_partition (fibreWeight w π c) H
    (fibreWeight_nonnegative w hw π c) ρ
  unfold partitionVariance partitionContribution
  simp_rw [h]
  rw [Finset.sum_add_distrib,Fintype.sum_prod_type]
  simp_rw [fibreWeight_pair]

omit [Fintype C] [Fintype D] in
lemma variance_singleton_fibre (w H : X → ℝ) (hw : ∀ x,0 ≤ w x) (a : X) :
    variance (fibreWeight w id a) H=0 := by
  rw [variance_formula _ H (fibreWeight_nonnegative w hw id a)]
  simp only [fibreWeight,id_eq,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  by_cases hz : w a=0
  · simp only [hz,zero_mul,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,div_zero,sub_zero]
  · field_simp
    ring

omit [Fintype C] [Fintype D] in
lemma partitionVariance_identity (w H : X → ℝ) (hw : ∀ x,0 ≤ w x) :
    partitionVariance w H id=0 := by
  unfold partitionVariance
  simp only [variance_singleton_fibre w H hw,Finset.sum_const_zero]

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FinitePrefixVariance
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Variance telescoping for literal finite coordinate prefixes -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

variable {A : Type*} [Fintype A] {q : ℕ}

theorem prefixVariance_step (w H : (Fin q → A) → ℝ) (hw : ∀ a,0 ≤ w a) (k : Fin q) :
    prefixVariance w H k.val (Nat.le_of_lt k.isLt)=
      prefixVariance w H (k.val+1) k.isLt+prefixContribution w H k := by
  have hp := partition_refinement w H hw (restriction k.val (Nat.le_of_lt k.isLt)) (fun a => a k)
  have he := partitionVariance_reindex (prefixSnocEquiv A k.val) w H
    (fun a => (restriction k.val (Nat.le_of_lt k.isLt) a,a k))
  have hfun : (fun a => prefixSnocEquiv A k.val (restriction k.val (Nat.le_of_lt k.isLt) a,a k))=
      restriction (k.val+1) k.isLt := by
    funext a
    exact restriction_snoc k.isLt a
  rw [hfun] at he
  rw [← he] at hp
  exact hp

lemma prefixVariance_zero (w H : (Fin q → A) → ℝ) : prefixVariance w H 0 (Nat.zero_le q)=variance w H := by
  unfold prefixVariance partitionVariance
  rw [Fintype.sum_unique]
  congr 1
  funext a
  unfold fibreWeight
  rw [ite_eq_left (Subsingleton.elim _ _)]

lemma prefixVariance_final (w H : (Fin q → A) → ℝ) (hw : ∀ a,0 ≤ w a) :
    prefixVariance w H q le_rfl=0 := by
  change partitionVariance w H id=0
  exact partitionVariance_identity w H hw

/-- Each physical exposure depth incurs its own budget once. -/
theorem variance_le_prefix_budget (w H : (Fin q → A) → ℝ) (hw : ∀ a,0 ≤ w a)
    (B : ℝ) (hb : ∀ k : Fin q,prefixContribution w H k ≤ B) :
    variance w H ≤ q*B := by
  have hacc : ∀ k (hk : k ≤ q),variance w H ≤ prefixVariance w H k hk+k*B := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [prefixVariance_zero]
      simp only [Nat.cast_zero,zero_mul,add_zero,le_refl]
    | succ k ih =>
      intro hk
      have hkl : k < q := by omega
      have hstep := prefixVariance_step w H hw ⟨k,hkl⟩
      have hprevious := ih (Nat.le_of_lt hkl)
      have hbound := hb ⟨k,hkl⟩
      dsimp only at hstep hbound
      rw [hstep] at hprevious
      rw [Nat.cast_succ]
      linarith
  have h := hacc q le_rfl
  rw [prefixVariance_final w H hw,zero_add] at h
  exact h

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteExposureBudget
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite exposure depth and polynomial coefficient -/

namespace ContingencyTables.FiniteExposureVariance

open scoped Classical

theorem variance_le_polynomial_budget {A : Type*} [Fintype A] {q : ℕ}
    (w H : (Fin q → A) → ℝ) (hw : ∀ a,0 ≤ w a) (d U : ℕ) (hq : q ≤ d)
    (E : ℝ) (hE : 0 ≤ E)
    (hb : ∀ k : Fin q,prefixContribution w H k ≤ 4*d*((U:ℝ)+1)^6*E) :
    variance w H ≤ 4*(d:ℝ)^2*((U:ℝ)+1)^6*E := by
  have hv := variance_le_prefix_budget w H hw (4*d*((U:ℝ)+1)^6*E) hb
  have hq' : (q:ℝ) ≤ d := by exact_mod_cast hq
  have hcoef : 0 ≤ 4*(d:ℝ)*((U:ℝ)+1)^6 := by positivity
  calc
    _ ≤ q*(4*d*((U:ℝ)+1)^6*E) := hv
    _ ≤ (d:ℝ)*(4*d*((U:ℝ)+1)^6*E) := mul_le_mul_of_nonneg_right hq' (mul_nonneg hcoef hE)
    _ = _ := by ring

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalPrefixEnergies
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical prefix contexts use each exchange edge at most once -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open LargePairEnumeration IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def prefixExtension (small : I → J → Bool) (s : I×J) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) : I×J → ℕ := fun a =>
  if h : small a.1 a.2=true ∧ RowMajorBefore a s then (τ ⟨⟨a,h.1⟩,h.2⟩).val else 0

omit [Fintype I] [Fintype J] in
lemma prefixExtension_at (small : I → J → Bool) (s : I×J) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (a : Earlier small s) :
    prefixExtension small s U τ a.val.val=(τ a).val := by
  unfold prefixExtension
  rw [dite_eq_left ⟨a.val.property,a.property⟩]
  exact congrArg (fun b : Earlier small s => (τ b).val) (Subtype.ext (Subtype.ext rfl))

omit [Fintype I] [Fintype J] in
lemma prefixExtension_bounded (small : I → J → Bool) (s : I×J) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (a : Earlier small s) :
    prefixExtension small s U τ a.val.val ≤ U := by
  rw [prefixExtension_at]
  exact Nat.le_of_lt_succ (τ a).isLt

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ChoiceContextEnumeration
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal finite choice fibres equal the transport child sums -/

namespace ContingencyTables.SmallContextEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres
open LargePairEnumeration BalancedEnumeration BalancedFamily
open FirstPaperPhysicalMarginal ExcessContextProfiles SmallGraphProfiles
open FiniteExposureVariance
open IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

def earlierChoices (small : I → J → Bool) (s : I×J) (U : ℕ)
    (x : Cells small → Fin (U+1)) : Earlier small s → Fin (U+1) := fun a => x a.val

def ChoiceContext (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1)) :=
  {x : Cells small → Fin (U+1) // earlierChoices small s U x=τ ∧ x ⟨s,hs⟩=k}

noncomputable instance choiceContextFintype (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) (U : ℕ) (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1)) :
    Fintype (ChoiceContext small s hs U τ k) := by unfold ChoiceContext; infer_instance

noncomputable def choiceContextEquiv (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) (U : ℕ) (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1)) :
    (Later small s → Fin (U+1)) ≃ ChoiceContext small s hs U τ k where
  toFun y := ⟨splitChoices small s hs U τ k y,funext (splitChoices_prefix small s hs U τ k y),
    splitChoices_special small s hs U τ k y⟩
  invFun x := fun a => x.val a.val
  left_inv y := by funext a; exact splitChoices_later small s hs U τ k y a
  right_inv x := by
    apply Subtype.ext
    funext a
    obtain ⟨v,rfl⟩ := (cellSplitEquiv small s hs).surjective a
    rcases v with p|(_|t)
    · exact (splitChoices_prefix small s hs U τ k _ p).trans (congrFun x.property.1 p).symm
    · exact (splitChoices_special small s hs U τ k _).trans x.property.2.symm
    · exact splitChoices_later small s hs U τ k _ t

lemma choice_fibre_sum (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (U : ℕ) (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1))
    (F : (Cells small → Fin (U+1)) → ℝ) :
    (∑ x,fibreWeight (fibreWeight F (earlierChoices small s U) τ) (fun x => x ⟨s,hs⟩) k x)=
      ∑ x : ChoiceContext small s hs U τ k,F x.val := by
  exact double_fibre_sum F (earlierChoices small s U) (fun x => x ⟨s,hs⟩) τ k

omit [Fintype I] [Fintype J] in
lemma prefixChoices_extension (small : I → J → Bool) (s : I×J) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) :
    prefixChoices small s (prefixExtension small s U τ) U (prefixExtension_bounded small s U τ)=τ := by
  funext a
  apply Fin.ext
  exact prefixExtension_at small s U τ a

end ContingencyTables.SmallContextEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteRepairVariance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite variance extension along completion-retaining repairs -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical
open CommonBasesFPRAS

variable {X : Type*} [Fintype X]

lemma variance_le_center (w H : X → ℝ) (hw : ∀ x,0 ≤ w x) (a : ℝ) :
    variance w H ≤ ∑ x,w x*(H x-a)^2 := by
  by_cases hz : 0 < ∑ x,w x
  · exact finite_center_min Finset.univ w H a hz
  · have hz' : (∑ x,w x)=0 :=
      le_antisymm (le_of_not_gt hz) (Finset.sum_nonneg (fun x _ => hw x))
    have hzero := zero_mass_weights w hw hz'
    simp only [variance,hzero,zero_mul,Finset.sum_const_zero,le_refl]

omit [Fintype X] in
/-- The actual typewise repair injection extends a transversal variance
bound to all states, charging each defect-to-repair difference once. -/
theorem variance_sum_repair {B D T : Type*} [Fintype B] [Fintype D] [Fintype T]
    (w : B → ℝ) (v : D → ℝ) (H : B → ℝ) (K : D → ℝ)
    (R : D → B) (label : D → T) (hw : ∀ b,0 ≤ w b) (hv : ∀ d,0 ≤ v d)
    (hdom : ∀ d,v d ≤ w (R d)) (hinj : Function.Injective (fun d => (label d,R d))) :
    variance (Sum.elim w v) (Sum.elim H K) ≤
      (1+2*(Fintype.card T:ℝ))*variance w H+2*∑ d,v d*(K d-H (R d))^2 := by
  have hcenter := variance_le_center (Sum.elim w v) (Sum.elim H K)
    (fun x => Sum.rec hw hv x) (mean w H)
  have hdefect : (∑ d,v d*(K d-mean w H)^2) ≤
      2*(∑ d,v d*(K d-H (R d))^2)+2*(∑ d,v d*(H (R d)-mean w H)^2) := by
    calc
      _ ≤ ∑ d,v d*(2*(K d-H (R d))^2+2*(H (R d)-mean w H)^2) :=
        Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left
          (square_repair_split (K d) (H (R d)) (mean w H)) (hv d))
      _ = _ := by
        have he (d : D) : v d*(2*(K d-H (R d))^2+2*(H (R d)-mean w H)^2)=
            2*(v d*(K d-H (R d))^2)+2*(v d*(H (R d)-mean w H)^2) := by ring
        simp_rw [he]
        rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  have hmass := repair_center_mass w v H R label hw hdom hinj (mean w H)
  change (∑ d,v d*(H (R d)-mean w H)^2) ≤ Fintype.card T*variance w H at hmass
  rw [Fintype.sum_sum_type] at hcenter
  change variance (Sum.elim w v) (Sum.elim H K) ≤ variance w H+(∑ d,v d*(K d-mean w H)^2) at hcenter
  nlinarith

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteGraphPoincareBudget
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The source polynomial coefficient for the repaired graph -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

theorem variance_repaired_graph_budget {B D T : Type*} [Fintype B] [Fintype D] [Fintype T]
    (w : B → ℝ) (v : D → ℝ) (H : B → ℝ) (K : D → ℝ) (R : D → B) (label : D → T)
    (hw : ∀ b,0 ≤ w b) (hv : ∀ d,0 ≤ v d) (hdom : ∀ d,v d ≤ w (R d))
    (hinj : Function.Injective (fun d => (label d,R d))) (d U : ℕ) (hd : 1 ≤ d) (hU : 1 ≤ U)
    (hT : Fintype.card T ≤ d^2) (E : ℝ) (hE : 0 ≤ E)
    (hvar : variance w H ≤ 4*(d:ℝ)^2*((U:ℝ)+1)^6*E)
    (hrepair : (∑ x,v x*(K x-H (R x))^2) ≤ E) :
    variance (Sum.elim w v) (Sum.elim H K) ≤ 770*(d:ℝ)^4*(U:ℝ)^6*E := by
  have hcoef : (1+2*(Fintype.card T:ℝ)) ≤ 1+2*(d:ℝ)^2 := by
    have hT' : (Fintype.card T:ℝ) ≤ (d:ℝ)^2 := by exact_mod_cast hT
    linarith
  have hvar0 : 0 ≤ variance w H := Finset.sum_nonneg (fun b _ => mul_nonneg (hw _) (sq_nonneg _))
  calc
    _ ≤ (1+2*(Fintype.card T:ℝ))*variance w H+2*∑ x,v x*(K x-H (R x))^2 :=
      variance_sum_repair w v H K R label hw hv hdom hinj
    _ ≤ (1+2*(d:ℝ)^2)*variance w H+2*E :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef hvar0) (mul_le_mul_of_nonneg_left hrepair (by norm_num))
    _ ≤ (1+2*(d:ℝ)^2)*(4*(d:ℝ)^2*((U:ℝ)+1)^6*E)+2*E :=
      add_le_add (mul_le_mul_of_nonneg_left hvar (show 0 ≤ 1+2*(d:ℝ)^2 by positivity)) le_rfl
    _ = ((1+2*(d:ℝ)^2)*4*(d:ℝ)^2*((U:ℝ)+1)^6+2)*E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (graph_poincare_coefficient d U hd hU) hE

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteChainWeightVariance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalizing a finite weighted variance -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators
open CommonBasesFPRAS

variable {X : Type*} [Fintype X]

lemma chain_variance_eq (C : FiniteChain X) (w H : X → ℝ)
    (hπ : ∀ x,C.π x=w x/(∑ y,w y)) :
    C.variance H=variance w H/(∑ x,w x) := by
  have hm : C.mean H=mean w H := by
    unfold FiniteChain.mean mean
    simp_rw [hπ,div_mul_eq_mul_div]
    rw [← Finset.sum_div]
  unfold FiniteChain.variance FiniteChain.inner variance
  rw [hm]
  simp_rw [hπ]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteChainGraphComparison
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalize a weighted graph inequality for its reversible chain -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators
open CommonBasesFPRAS

variable {X : Type*} [Fintype X] [Nonempty X]

lemma chain_poincare_of_weighted_graph (C : FiniteChain X) (w H : X → ℝ)
    (hw : ∀ x,0 < w x) (hπ : ∀ x,C.π x=w x/(∑ y,w y))
    (E K β : ℝ) (hK : 0 ≤ K) (hβ : 0 < β)
    (hv : variance w H ≤ K*E)
    (he : β/(2*(∑ x,w x))*E ≤ C.energy H) :
    C.variance H ≤ (2*K/β)*C.energy H := by
  have hZ : 0 < ∑ x,w x := Finset.sum_pos (fun x _ => hw x) Finset.univ_nonempty
  rw [chain_variance_eq C w H hπ]
  calc
    _ ≤ K*E/(∑ x,w x) := div_le_div_of_nonneg_right hv (le_of_lt hZ)
    _ = (2*K/β)*(β/(2*(∑ x,w x))*E) := by
      field_simp [ne_of_gt hβ,ne_of_gt hZ]
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteExchangeObservables
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit exchanges change each selected coordinate sum by at most two -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open FactorialSignatures

variable {C : Type*} [Fintype C] [DecidableEq C]

lemma linearObservable_removeOne (a : C → ℤ) (D : C → ℕ) (i : C) (hi : 0 < D i) :
    linearObservable a (removeOne D i)=linearObservable a D-a i := by
  have ht (k : C) : (removeOne D i k:ℤ)=(D k:ℤ)-(if k=i then 1 else 0) := by
    by_cases hk : k=i
    · subst k
      simp only [removeOne,ite_true, if_true]
      omega
    · simp only [removeOne,hk,ite_false,Nat.sub_zero,sub_zero]
  unfold linearObservable
  simp_rw [ht,mul_sub]
  rw [Finset.sum_sub_distrib]
  simp

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ReferenceCompletionBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Padding and dimension bounds for the actual reference completion block -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma reference_block_dimensions (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) :
    Fintype.card (Option {i : LargeRows r U // i≠i₀}) ≤ dimensionAllowance (I := I) (J := J) ∧
    Fintype.card (Option {j : LargeColumns c U // j≠j₀}) ≤ dimensionAllowance (I := I) (J := J) ∧
    Fintype.card {i : LargeRows r U // i≠i₀}+Fintype.card {j : LargeColumns c U // j≠j₀}+1 ≤
      dimensionAllowance (I := I) (J := J) := by
  have hri := Fintype.card_congr (Equiv.optionSubtypeNe i₀)
  have hcj := Fintype.card_congr (Equiv.optionSubtypeNe j₀)
  have hr : Fintype.card (LargeRows r U) ≤ Fintype.card I := Fintype.card_subtype_le _
  have hc : Fintype.card (LargeColumns c U) ≤ Fintype.card J := Fintype.card_subtype_le _
  rw [Fintype.card_option] at hri hcj
  simp only [Fintype.card_option]
  unfold dimensionAllowance
  constructor
  · nlinarith
  constructor <;> nlinarith

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ReferenceEdgeAcceptance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Half of every physical completion block accepts an adjacent translation -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open CompletionTranslation

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [LinearOrder I] [LinearOrder J] in
lemma reference_dimension_ge_fourteen (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) :
    14 ≤ dimensionAllowance (I := I) (J := J) := by
  have hi : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i₀.val⟩
  have hj : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨j₀.val⟩
  unfold dimensionAllowance
  nlinarith

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalMassBound
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Count the small state and its large completion jointly -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalLargeProfiles FirstPaperPhysicalMarginal
open SmallContextFibres LargePairEnumeration CompletionCounts NestedPenaltyApplication

universe u
variable {I J : Type u} [Fintype I] [Fintype J]

lemma physicalAssignments_card_le (small : I → J → Bool) (B : I → J → ℕ)
    (C : ℕ) (hB : ∀ i j,B i j ≤ C) :
    Fintype.card (PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2)) ≤
      (C+1)^Fintype.card (LargeCell (fun a : I×J => small a.1 a.2)) := by
  unfold PhysicalAssignments
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∏ _a : LargeCell (fun a : I×J => small a.1 a.2),(C+1) :=
      Finset.prod_le_prod' (fun a _ => Nat.add_le_add_right (hB _ _) 1)
    _ = _ := by simp

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteDependentLaw
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact joint laws with a finite state-dependent completion space -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

variable {X : Type*} {Y : X → Type*} [Fintype X] [∀ x,Fintype (Y x)]

variable [Nonempty X] [∀ x,Nonempty (Y x)]

/-- A state chosen in proportion to its completion count, followed by a
uniform completion, gives exactly the uniform law on all joint pairs. -/
theorem dependentJointLaw_uniform (p : RationalLaw X)
    (hp : ∀ x,p.mass x=(Fintype.card (Y x):ℚ)/(∑ z : X,(Fintype.card (Y z):ℚ))) :
    dependentJointLaw p (fun x => uniformLaw (α := Y x))=
      uniformLaw (α := (x : X) × Y x) := by
  apply RationalLaw.ext
  funext a
  have hcard : (Fintype.card (Y a.1):ℚ)≠0 := by
    exact_mod_cast (Fintype.card_pos (α := Y a.1)).ne'
  change p.mass a.1*(1/(Fintype.card (Y a.1):ℚ))=1/(Fintype.card ((x : X) × Y x):ℚ)
  rw [hp,Fintype.card_sigma,Nat.cast_sum]
  field_simp

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallDefectLabels
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The defect coordinates are determined by the two integer views -/

namespace ContingencyTables

variable {I J : Type*} [DecidableEq I] [DecidableEq J]

theorem IsDefect.labels_unique {x q : I → J → ℕ} {s t s' t' : I×J}
    (h : IsDefect x q s t) (h' : IsDefect x q s' t') : s=s' ∧ t=t' := by
  have hst : ¬(s.1=t.1 ∧ s.2=t.2) := fun he => h.1 (Prod.ext he.1 he.2)
  have hs := h.2 s.1 s.2
  simp only [transferInt,hst,ite_false,and_self,ite_true, if_true,sub_zero] at hs
  have hss : s=s' := by
    by_contra he
    have hss' : ¬(s.1=s'.1 ∧ s.2=s'.2) := fun hh => he (Prod.ext hh.1 hh.2)
    have hs' := h'.2 s.1 s.2
    simp only [transferInt,hss',ite_false,add_zero] at hs'
    split_ifs at hs' <;> omega
  subst s'
  refine ⟨rfl,?_⟩
  by_contra he
  have htt : ¬(t.1=t'.1 ∧ t.2=t'.2) := fun hh => he (Prod.ext hh.1 hh.2)
  have hts : ¬(t.1=s.1 ∧ t.2=s.2) := fun hh => h.1 (Prod.ext hh.1.symm hh.2.symm)
  have ht := h.2 t.1 t.2
  have ht' := h'.2 t.1 t.2
  simp only [transferInt,htt,hts,ite_false,and_self,ite_true, if_true,sub_zero,add_zero] at ht ht'
  omega

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallPatternArithmetic
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer tests for balanced and single-defect small profiles -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates SmallContextFibres

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]
variable (small : I → J → Bool)
  (B : I → J → ℕ)

omit [LinearOrder I] [LinearOrder J] in
lemma cell_eq_coordinates (a b : Cells small) :
    a=b ↔ a.val.1=b.val.1 ∧ a.val.2=b.val.2 := by
  simp only [Subtype.ext_iff,Prod.ext_iff]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallPatternProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial tests for the two allowed small-profile patterns -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma pairSum_ofFn {n : ℕ} (x y : Fin n → ℕ) (U : ℕ) (i : Fin n) :
    pairSum (((List.ofFn x,List.ofFn y),U),i.val)=x i+y i := by
  simp only [pairSum,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp only [i.isLt,dite_true,Option.getD_some]

theorem balancedTest_ofFn {n : ℕ} (x y : Fin n → ℕ) (U : ℕ) :
    balancedTest ((List.ofFn x,List.ofFn y),U)=true ↔ ∀ i,x i+y i=U := by
  simp only [balancedTest,List.all_eq_true,List.mem_range,List.length_ofFn,balancedAt,
    decide_eq_true_eq]
  constructor
  · intro h i
    simpa only [pairSum_ofFn] using h i.val i.isLt
  · intro h i hi
    exact (pairSum_ofFn x y U ⟨i,hi⟩).trans (h ⟨i,hi⟩)

theorem defectTest_ofFn {n : ℕ} (x y : Fin n → ℕ) (U : ℕ) (s t : Fin n) :
    defectTest (((List.ofFn x,List.ofFn y),U),(s.val,t.val))=true ↔
      s≠t ∧ ∀ i,x i+y i+(if i=s then 1 else 0)=U+(if i=t then 1 else 0) := by
  simp only [defectTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,
    List.mem_range,List.length_ofFn,defectAt]
  constructor
  · rintro ⟨hne,h⟩
    refine ⟨fun he => hne (congrArg Fin.val he),fun i => ?_⟩
    simpa only [pairSum_ofFn,Fin.ext_iff] using h i.val i.isLt
  · rintro ⟨hne,h⟩
    refine ⟨fun he => hne (Fin.ext he),fun i hi => ?_⟩
    rw [show pairSum (((List.ofFn x,List.ofFn y),U),i)=x ⟨i,hi⟩+y ⟨i,hi⟩ from
      pairSum_ofFn x y U ⟨i,hi⟩]
    simpa only [Fin.ext_iff] using h ⟨i,hi⟩

theorem patternTest_ofFn {n : ℕ} (x y : Fin n → ℕ) (U : ℕ) :
    patternTest ((List.ofFn x,List.ofFn y),U)=true ↔
      (∀ i,x i+y i=U) ∨ ∃ s t : Fin n,s≠t ∧
        ∀ i,x i+y i+(if i=s then 1 else 0)=U+(if i=t then 1 else 0) := by
  simp only [patternTest,Bool.or_eq_true,balancedTest_ofFn,List.any_eq_true]
  constructor
  · rintro (h|⟨⟨s,t⟩,hst,h⟩)
    · exact Or.inl h
    · have hb := (mem_cellPairs (List.ofFn x) (List.ofFn x) s t).mp hst
      simp only [List.length_ofFn] at hb
      exact Or.inr ⟨⟨s,hb.1⟩,⟨t,hb.2⟩,(defectTest_ofFn x y U _ _).mp h⟩
  · rintro (h|⟨s,t,h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨(s.val,t.val),?_,(defectTest_ofFn x y U s t).mpr h⟩
      apply (mem_cellPairs (List.ofFn x) (List.ofFn x) _ _).mpr
      simpa only [List.length_ofFn] using And.intro s.isLt t.isLt

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallBoundsProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary program checking every stored coordinate bound -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma boundedValues_ofFn {n : ℕ} (U : ℕ) (v : Fin n → ℕ) :
    boundedValues (U,List.ofFn v)=true ↔ ∀ i,v i≤U := by
  simp only [boundedValues,List.all_eq_true,List.mem_ofFn,decide_eq_true_eq]
  constructor
  · intro h i
    exact h (v i) ⟨i,rfl⟩
  · intro h a ha
    obtain ⟨i,rfl⟩ := ha
    exact h i

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallLineSumProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary row and column sums of the sparse stored view -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators

lemma lineSum_eq_sum {n : ℕ} (row : Bool) (z : LineData) (hsize : z.1.2.length=n)
    (f : Fin n → ℕ) (hf : ∀ i,lineEntry row (z,i.val)=f i) :
    lineSum row z=∑ i,f i := by
  unfold lineSum
  have he : (List.range z.1.2.length).map (fun i => lineEntry row (z,i))=List.ofFn f := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_range,List.length_ofFn,hsize]
    · intro i hi _
      have hin : i<n := by simpa only [List.length_map,List.length_range,hsize] using hi
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      exact hf ⟨i,hin⟩
  rw [he,List.sum_ofFn]

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallComplementProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the complemented small column view -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma complementValues_ofFn {n : ℕ} (U : ℕ) (v : Fin n → ℕ) :
    complementValues (U,List.ofFn v)=List.ofFn (fun i => U-v i) := by
  simp only [complementValues,List.map_ofFn,Function.comp_def]

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallMarginTestProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial residual-margin inequality and equality tests -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

theorem validMargins_iff (row : Bool) (z : MarginCheckData) :
    validMargins row z=true ↔ ∀ i,i<(marginList row z).length →
      lineSum row (lineArgument row (z,i))≤(marginList row z).getD i 0 ∧
      ((marginList row z).getD i 0<z.2 →
        lineSum row (lineArgument row (z,i))=(marginList row z).getD i 0) := by
  simp only [validMargins,List.all_eq_true,List.mem_range,validMarginAt,decide_eq_true_eq]

end ContingencyTables.ProfilePrograms

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

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma split_flattenViews (v : List ℕ×List ℕ) :
    splitViews (v.1.length,flattenViews v)=v := by
  simp only [splitViews,flattenViews,List.take_left,List.drop_left,Prod.mk.eta]

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallExchangeListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating all directed unit exchanges of a stored profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma mem_positiveExchangeIndices (xs : List ℕ) (i j : ℕ) :
    (i,j)∈positiveExchangeIndices xs ↔
      i<xs.length ∧ j<xs.length ∧ i≠j ∧ 0<xs.getD j 0 := by
  simp only [positiveExchangeIndices,List.mem_filter,mem_cellPairs,positiveExchangeTest,
    decide_eq_true_eq]
  tauto

lemma codeExchangeList_length (v : List ℕ×List ℕ) :
    (codeExchangeList v).length≤(v.1.length+v.2.length)^2 := by
  have h := List.length_filter_le (fun ij => positiveExchangeTest (flattenViews v,ij))
    (cellPairs (flattenViews v,flattenViews v))
  simpa only [codeExchangeList,List.length_map,positiveExchangeIndices,cellPairs,
    List.length_range,flattenViews,List.length_append,pow_two] using h

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileInverseRepairProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for each labelled inverse repair -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates
open ProfilePrograms

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]
variable (small : I → J → Bool) {n : ℕ} (e : Fin n ≃ Cells small)

lemma transfer_at_index (X : I → J → ℕ) (s t : I×J) (i : Fin n) :
    (transferInt X s t (e i).val.1 (e i).val.2).toNat=
      X (e i).val.1 (e i).val.2+(if i.val=cellIndex small e t then 1 else 0)-
        (if i.val=cellIndex small e s then 1 else 0) := by
  simp only [cellIndex_eq,Prod.ext_iff,transferInt]
  split_ifs <;> omega

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairGeometryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary computation of repair crossing cells and capacities -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma capacityList_ofFn {q : ℕ} (U : ℕ) (v : Fin q → ℕ) :
    capacityList (U,List.ofFn v)=List.ofFn (fun _ : Fin q => U) := by
  simp only [capacityList,List.map_ofFn,Function.comp_def]

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

lemma catalog_getD (i : Fin q) :
    (cellCatalog small e).getD i.val (0,0)=((e i).val.1.val,(e i).val.2.val) := by
  simp only [cellCatalog,List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,
    dite_true,Option.getD_some,Fin.eta]

/-- Large crossing cells use the out-of-range index in both the
forward and inverse arithmetic repairs. -/
theorem crossingIndex_eq (s t : Cells small) :
    crossingIndex (cellCatalog small e,((e.symm s).val,(e.symm t).val))=
      cellIndex small e (t.val.1,s.val.2) := by
  unfold crossingIndex
  rw [catalog_getD,catalog_getD]
  simp only [Equiv.apply_symm_apply]
  exact cellCatalog_index small e (t.val.1,s.val.2)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial lists of encoded forward and inverse repairs -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma repairPairs_length (z : RepairData) : (repairPairs z).length=z.1.2.1.length^2 := by
  simp only [repairPairs,cellPairs,List.length_map,List.length_range,pow_two]

theorem forwardRepairList_length (z : RepairData) :
    (forwardRepairList z).length≤z.1.2.1.length^2 := by
  simpa only [forwardRepairList,List.length_map,forwardRepairLabels,repairPairs_length]
    using List.length_filter_le (fun st => repairLabelTest (z,st)) (repairPairs z)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallInverseRepairList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Checking inverse repair candidates against their forward image -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

theorem checkedInverseRepairList_length (z : RepairData) :
    (checkedInverseRepairList z).length≤z.1.2.1.length^2 := by
  simpa only [checkedInverseRepairList,List.length_map,inverseRepairLabels,repairPairs_length]
    using List.length_filter_le (fun st => inverseLabelTest (z,st)) (repairPairs z)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCodeNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary program for the full physical neighbor list -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma codeNeighbors_nodup (z : ProfileCheckData) : (codeNeighbors z).Nodup :=
  List.nodup_dedup _

theorem codeNeighbors_length (z : ProfileCheckData) (q : ℕ)
    (hx : z.1.1.2.1.length=q) (hy : z.1.1.2.2.length=q) :
    (codeNeighbors z).length≤6*q^2 := by
  have h0 := ((rawCodeNeighbors z).filter
    (fun v => profileTest (candidateData (z,v)))).dedup_sublist.length_le
  have h1 := List.length_filter_le (fun v => profileTest (candidateData (z,v))) (rawCodeNeighbors z)
  have he := codeExchangeList_length z.1.1.2
  have hf := forwardRepairList_length (z.1.1,z.2)
  have hb := checkedInverseRepairList_length (z.1.1,z.2)
  change (codeNeighbors z).length≤_ at h0
  simp only [rawCodeNeighbors,List.length_append] at h1
  simp only [hx,hy] at he hf hb
  have ht := h0.trans h1
  nlinarith [ht]

end ContingencyTables.ProfilePrograms

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

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma marginThreshold_ofFn :
    marginThreshold (List.ofFn r,List.ofFn c)=
      (dimensionAllowance (I := Fin m) (J := Fin n))^20 := by
  simp only [marginThreshold,marginDimension,List.length_ofFn,dimensionAllowance,Fintype.card_fin]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_EstimatorWordBanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact disjoint word layout of one weight estimator

There is one bank of ratio samples for every phase, followed by one bank
of correction samples. Each correction sample has its own walk and bin
words. This is the literal layout used by the executable allocator.
-/

namespace ContingencyTables.EstimatorWordBanks

open DensePrograms GridBoundary FairBits
open scoped Classical

def wordEquiv (j S r t b : ℕ) :
    (Fin (j*(S*r)+S*(t+b)) → Bool) ≃ Banks j S r t b :=
  (splitWordEquiv _ _).trans (Equiv.prodCongr
    ((gridWordEquiv j (S*r)).trans
      (Equiv.piCongrRight (fun _ => gridWordEquiv S r)))
    ((gridWordEquiv S (t+b)).trans
      (Equiv.piCongrRight (fun _ => splitWordEquiv t b))))

end ContingencyTables.EstimatorWordBanks

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteChainSlowdown
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact holding slowdown of finite reversible chains -/

namespace ContingencyTables.FiniteChainSlowdown

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {X : Type*} [Fintype X]

def slow (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : FiniteChain X where
  P x y := a*C.P x y+if x=y then 1-a else 0
  π := C.π
  positive := C.positive
  normalized := C.normalized
  nonnegative x y := by
    apply add_nonneg (mul_nonneg ha0 (C.nonnegative x y))
    split_ifs
    · linarith
    · rfl
  stochastic x := by
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,C.stochastic,mul_one]
    simp
  reversible x y := by
    by_cases h : x=y
    · subst y
      rfl
    · simp only [h,Ne.symm h,ite_false,add_zero]
      nlinarith [C.reversible x y]
  lazy x := by
    simp only [ite_true, if_true]
    have hm := mul_le_mul_of_nonneg_left (C.lazy x) ha0
    linarith

end

end ContingencyTables.FiniteChainSlowdown

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteTraceSlowdown
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Trace transition matrices under an exact holding slowdown -/

namespace ContingencyTables.FiniteChainSlowdown

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {Y : Type*} [Fintype Y]

def slowKilled (Q : KilledKernel Y) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) : KilledKernel Y where
  Q x y := a*Q.Q x y+if x=y then 1-a else 0
  r := a*Q.r+(1-a)
  nonnegative x y := by
    apply add_nonneg (mul_nonneg ha0.le (Q.nonnegative x y))
    split_ifs
    · linarith
    · rfl
  rnonneg := add_nonneg (mul_nonneg ha0.le Q.rnonneg) (sub_nonneg.mpr ha1)
  rlt := by nlinarith [mul_pos ha0 (sub_pos.mpr Q.rlt)]
  rowbound x := by
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left (Q.rowbound x) ha0.le
    simpa using add_le_add_right hh (1-a)

variable {X : Type*} [Fintype X]

lemma slowKilled_matches (C : FiniteChain X) (A : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside A))
    (hQ : ∀ x y : FiniteChain.Outside A,Q.Q x y=C.P x.val y.val)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∀ x y : FiniteChain.Outside A,(slowKilled Q a ha0 ha1).Q x y=
      (slow C a ha0.le ha1).P x.val y.val := by
  intro x y
  simp only [slowKilled,slow]
  rw [hQ]
  by_cases h : x=y
  · subst y
    simp
  · have hv : x.val≠y.val := fun hv => h (Subtype.ext hv)
    simp only [h,hv,ite_false]

end

end ContingencyTables.FiniteChainSlowdown

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordDependent
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent words with a state-dependent second output -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture FairBits

noncomputable section

variable {A B X Z : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Z]

omit [Fintype Z] in
/-- Fresh terminal bits are independent of the bits used to obtain the
state, even though the completion space depends on that state. -/
theorem mapLaw_dependent_product {Y : X → Type*} [∀ x,Fintype (Y x)]
    [DecidableEq X] [∀ x,DecidableEq (Y x)]
    (p : RationalLaw A) (q : RationalLaw B) (f : A → X) (g : (x : X) → B → Y x) :
    mapLaw (productLaw p q) (fun ab => (⟨f ab.1,g (f ab.1) ab.2⟩ : Sigma Y))=
      dependentJointLaw (mapLaw p f) (fun x => mapLaw q (g x)) := by
  apply RationalLaw.ext
  funext z
  rcases z with ⟨x,y⟩
  simp only [mapLaw,productLaw,dependentJointLaw,Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a=x
  · subst x
    simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and,ite_true, if_true,Finset.mul_sum,mul_ite,mul_zero]
  · have hn (b : B) : (⟨f a,g (f a) b⟩ : Sigma Y)≠⟨x,y⟩ :=
      fun hh => h (congrArg Sigma.fst hh)
    simp only [hn,ite_false,h,Finset.sum_const_zero,zero_mul]


end
end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteVaryingWordWalk
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent words for successive draws with varying widths -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture FairBits
noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

def varyingLaw (width : ℕ → ℕ)
    (step : (i : ℕ) → X → (Fin (width i) → Bool) → X)
    (p : RationalLaw X) : ℕ → RationalLaw X
  | 0 => p
  | n+1 => bindLaw (varyingLaw width step p n)
      (fun x => mapLaw (uniformLaw (α := Fin (width n) → Bool)) (step n x))

end
end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact bounded list slices of a finite Boolean word -/

namespace ContingencyTables.FiniteWordSlices

open FairBits

def split (p q k : ℕ) : (Fin (1+(p+((q+q)+k))) → Bool) ≃ Fields p q k :=
  (splitWordEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
    ((splitWordEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
      ((splitWordEquiv _ _).trans (Equiv.prodCongr (splitWordEquiv _ _) (Equiv.refl _))))))

end ContingencyTables.FiniteWordSlices

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteDependentApproximation
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Total variation for state-dependent finite completion laws -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {X : Type*} {Y : X → Type*} [Fintype X] [∀ x,Fintype (Y x)]

theorem variation_dependentJoint (p q : RationalLaw X)
    (K L : (x : X) → RationalLaw (Y x)) :
    variation (dependentJointLaw p K) (dependentJointLaw q L) ≤
      variation p q+∑ x,p.mass x*variation (K x) (L x) := by
  have hpoint (x : X) (y : Y x) :
      |p.mass x*(K x).mass y-q.mass x*(L x).mass y| ≤
      p.mass x*|(K x).mass y-(L x).mass y|+|p.mass x-q.mass x| *(L x).mass y := by
    calc
      _ = |p.mass x*((K x).mass y-(L x).mass y)+(p.mass x-q.mass x)*(L x).mass y| := by
        congr 1
        ring
      _ ≤ |p.mass x*((K x).mass y-(L x).mass y)|+|(p.mass x-q.mass x)*(L x).mass y| :=
        abs_add_le _ _
      _ = _ := by
        rw [abs_mul,abs_mul,abs_of_nonneg (p.nonnegative x),abs_of_nonneg ((L x).nonnegative y)]
  have hsum := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) =>
    Finset.sum_le_sum (fun y (_ : y∈Finset.univ) => hpoint x y))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,(L _).total,mul_one] at hsum
  unfold variation
  change (∑ a : (x : X) × Y x,|p.mass a.1*(K a.1).mass a.2-q.mass a.1*(L a.1).mass a.2|)/2 ≤ _
  rw [Fintype.sum_sigma]
  have hh := div_le_div_of_nonneg_right hsum (show (0:ℚ) ≤ 2 by norm_num)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [add_div,Finset.sum_div,mul_div_assoc]
  ring

theorem variation_dependentJoint_uniform (p q : RationalLaw X)
    (K L : (x : X) → RationalLaw (Y x)) (η : ℚ)
    (hη : ∀ x,variation (K x) (L x) ≤ η) :
    variation (dependentJointLaw p K) (dependentJointLaw q L) ≤ variation p q+η := by
  calc
    _ ≤ variation p q+∑ x,p.mass x*variation (K x) (L x) := variation_dependentJoint p q K L
    _ ≤ variation p q+∑ x,p.mass x*η := by
      apply add_le_add_right
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hη x) (p.nonnegative x))
    _ = _ := by rw [←Finset.sum_mul,p.total,one_mul]

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteLawMoments
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expectations of concrete finite-word output laws -/

namespace ContingencyTables.FiniteLawMoments

open CommonBasesFPRAS ResidualMixture FirstSuccess
open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

def expectation (p : RationalLaw X) (g : X → ℝ) : ℝ := ∑ x,(p.mass x:ℝ)*g x

end ContingencyTables.FiniteLawMoments

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteRationalThreshold
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded dyadic comparison with a rational acceptance probability -/

namespace ContingencyTables.FairBits

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

def rationalThresholdMass (k : ℕ) (q : ℚ) : ℚ := rationalThreshold k q/(2:ℚ)^k

end

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityBits
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded Boolean implementation of fixed-cardinality subset draws -/

namespace ContingencyTables.FixedCardinalityBits

open CommonBasesFPRAS ResidualMixture FirstSuccess FairBits FixedCardinalityLaw
open scoped BigOperators Classical
noncomputable section

def roundedHeadLaw (B n k : ℕ) : RationalLaw Bool :=
  mapLaw (uniformLaw (α := Fin B → Bool)) (headDraw B n k)

def roundedFixedLaw (B : ℕ) : (n k : ℕ) → RationalLaw (Fin n → Bool)
  | 0, _ => pointLaw (fun i => Fin.elim0 i)
  | n+1, k => consLaw (roundedHeadLaw B n k)
      (fun b => roundedFixedLaw B n (remaining n k b))

end
end ContingencyTables.FixedCardinalityBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityMixture
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform-size mixture realizes the initial factorial weights

A size is drawn uniformly from 0,...,n, followed by the sequential
fixed-cardinality draw. Its subset mass is the literal local factorial
weight divided by n+1. The bounded Boolean implementation uses a fresh
word for the size and for each inclusion decision.
-/

namespace ContingencyTables.FixedCardinalityMixture

open ResidualMixture FirstSuccess FairBits FixedCardinalityLaw FixedCardinalityBits
open scoped BigOperators Classical
noncomputable section

def roundedSizeMixture (B n : ℕ) : RationalLaw (Fin n → Bool) :=
  bindLaw (scaledLaw (n+1) B (Nat.succ_pos n))
    (fun k => roundedFixedLaw B n k.val)

end
end ContingencyTables.FixedCardinalityMixture

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_MaximumForest
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The companion's maximum-capacity forest

Among finite acyclic subgraphs choose one of maximum total capacity.
Positive capacities make it spanning in each large-cell component. A
free edge can replace every tree edge on its path; optimality therefore
gives the exact path-capacity inequality used in the forest estimates.
-/

namespace ContingencyTables.MaximumForest

open scoped BigOperators Classical
open SimpleGraph

variable {V : Type*} [Fintype V]

/-- The same exchange argument applies directly to a separating cut;
this avoids choosing a path when using the forest's component cuts. -/
theorem free_edge_le_separating_edge (G T : SimpleGraph V) (b : Sym2 V → ℕ)
    (hTG : T ≤ G) (hT : T.IsAcyclic)
    (hmax : ∀ F : SimpleGraph V, F ≤ G → F.IsAcyclic → weight F b ≤ weight T b)
    (t : Sym2 V) (ht : t∈T.edgeSet) {u v : V}
    (hG : G.Adj u v) (hfree : ¬T.Adj u v)
    (hcut : ¬(T.deleteEdges {t}).Reachable u v) : b s(u,v) ≤ b t := by
  let D := T.deleteEdges {t}
  have hDT : D ≤ T := T.deleteEdges_le {t}
  have hDfree : ¬D.Adj u v := fun h => hfree (hDT h)
  have hnew : (D ⊔ edge u v).IsAcyclic := (hT.anti hDT).sup_edge_of_not_reachable hcut
  have hnewG : D ⊔ edge u v ≤ G := sup_le (hDT.trans hTG) ((G.edge_le_iff).mpr (Or.inr hG))
  have hopt := hmax (D ⊔ edge u v) hnewG hnew
  have hsum := weight_sup_edge D b u v hDfree hG.ne
  have hmem : t∈T.edgeFinset := by simpa using ht
  have hdelete : D.edgeFinset=T.edgeFinset.erase t := by
    ext e
    simp [D,edgeSet_deleteEdges,and_comm]
  have hsumDelete : weight D b+b t=weight T b := by
    rw [weight_eq D,weight_eq T,hdelete]
    exact Finset.sum_erase_add (s := T.edgeFinset) (a := t) b hmem
  omega

omit [Fintype V] in
lemma side_eq_of_reachable (D : SimpleGraph V) (u : V) {v w : V}
    (h : D.Reachable v w) : side D u v=side D u w := by
  apply Bool.eq_iff_iff.mpr
  simp only [side,decide_eq_true_eq]
  exact ⟨fun hv => hv.trans h,fun hw => hw.trans h.symm⟩

omit [Fintype V] in
lemma not_reachable_of_side_ne (D : SimpleGraph V) (u : V) {v w : V}
    (h : side D u v≠side D u w) : ¬D.Reachable v w := by
  exact fun hr => h (side_eq_of_reachable D u hr)

omit [Fintype V] in
/-- Every other tree edge is internal to a deletion component. -/
lemma side_eq_of_tree_edge (T : SimpleGraph V) (t : Sym2 V) (u : V) {v w : V}
    (h : T.Adj v w) (hne : s(v,w)≠t) :
    side (T.deleteEdges {t}) u v=side (T.deleteEdges {t}) u w := by
  apply side_eq_of_reachable
  exact (show (T.deleteEdges {t}).Adj v w by simp [h,hne]).reachable

/-- Capacities of actual free edges crossing a deletion component are
bounded by the capacity of its unique deleted tree edge. -/
theorem crossing_free_edge_le (G T : SimpleGraph V) (b : Sym2 V → ℕ)
    (hTG : T ≤ G) (hT : T.IsAcyclic)
    (hmax : ∀ F : SimpleGraph V, F ≤ G → F.IsAcyclic → weight F b ≤ weight T b)
    (t : Sym2 V) (ht : t∈T.edgeSet) (r : V) {u v : V}
    (hG : G.Adj u v) (hfree : ¬T.Adj u v)
    (hcross : side (T.deleteEdges {t}) r u≠side (T.deleteEdges {t}) r v) :
    b s(u,v) ≤ b t :=
  free_edge_le_separating_edge G T b hTG hT hmax t ht hG hfree
    (not_reachable_of_side_ne _ r hcross)

end ContingencyTables.MaximumForest

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestCut
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Signed cut equations for the actual physical table views

Small row and column views may disagree. Their two incidences therefore
remain separate in the cut formula. Large cells have a single physical
value at both endpoints, so every internal large-cell contribution cancels.
-/

namespace ContingencyTables.ForestCut

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] [Fintype J] in
lemma abs_indicator_sub {a b : Bool} (h : a≠b) : |indicator a-indicator b|=1 := by
  cases a <;> cases b <;> simp_all [indicator]

noncomputable def cutTerm (small : I → J → Bool) (rowU : I → Bool) (colU : J → Bool)
    (x q z X : I → J → ℝ) (i : I) (j : J) : ℝ :=
  if small i j then indicator (rowU i)*(x i j-X i j)-indicator (colU j)*(q i j-X i j)
  else (indicator (rowU i)-indicator (colU j))*(z i j-X i j)

/-- Literal signed summation of the nonroot margin differences. -/
theorem signed_cut_identity (small : I → J → Bool) (rowU : I → Bool) (colU : J → Bool)
    (x q z X : I → J → ℝ) :
    (∑ i, indicator (rowU i)*rowDifference small x z X i)-
      (∑ j, indicator (colU j)*columnDifference small q z X j) =
      ∑ i, ∑ j, cutTerm small rowU colU x q z X i j := by
  unfold rowDifference columnDifference cutTerm
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => indicator (colU j)*
    (if small i j then q i j-X i j else z i j-X i j))]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases small i j <;> simp [sub_mul]

/-- When U avoids roots, all selected nonroot equations hold, giving
the source's cut cancellation even on unbalanced small profiles. -/
theorem cut_sum_zero (small : I → J → Bool) (rowU : I → Bool) (colU : J → Bool)
    (x q z X : I → J → ℝ)
    (hr : ∀ i, rowU i=true → rowDifference small x z X i=0)
    (hc : ∀ j, colU j=true → columnDifference small q z X j=0) :
    (∑ i, ∑ j, cutTerm small rowU colU x q z X i j)=0 := by
  rw [← signed_cut_identity]
  have hrow : ∀ i, indicator (rowU i)*rowDifference small x z X i=0 := by
    intro i
    cases hi : rowU i
    · simp [indicator]
    · simp [indicator,hr i hi]
  have hcol : ∀ j, indicator (colU j)*columnDifference small q z X j=0 := by
    intro j
    cases hj : colU j
    · simp [indicator]
    · simp [indicator,hc j hj]
  simp only [hrow,hcol,Finset.sum_const_zero,sub_self]

omit [Fintype I] [Fintype J] in
lemma small_term_bound (small : I → J → Bool) (rowU : I → Bool) (colU : J → Bool)
    (x q z X : I → J → ℝ) (i : I) (j : J) (b B : ℝ)
    (hs : small i j=true) (hb : b≤B)
    (hx : 0≤x i j ∧ x i j≤b) (hq : 0≤q i j ∧ q i j≤b)
    (hX : 0≤X i j ∧ X i j≤b) :
    |cutTerm small rowU colU x q z X i j|≤2*B := by
  simp only [cutTerm,hs,ite_true, if_true]
  have hmul : ∀ s : Bool, ∀ a : ℝ, |indicator s*a|≤|a| := by
    intro s a
    cases s <;> simp [indicator]
  have hx' : |x i j-X i j|≤b := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1,hx.2,hX.1,hX.2]
  have hq' : |q i j-X i j|≤b := by
    apply abs_le.mpr
    constructor <;> linarith [hq.1,hq.2,hX.1,hX.2]
  calc
    _≤|indicator (rowU i)*(x i j-X i j)|+|indicator (colU j)*(q i j-X i j)| := abs_sub _ _
    _≤|x i j-X i j|+|q i j-X i j| := add_le_add (hmul _ _) (hmul _ _)
    _≤2*B := by linarith

omit [Fintype I] [Fintype J] in
lemma free_term_bound (small : I → J → Bool) (rowU : I → Bool) (colU : J → Bool)
    (x q z X : I → J → ℝ) (i : I) (j : J) (b B : ℝ)
    (hs : small i j=false) (hB : 1≤B)
    (hcap : rowU i≠colU j → b≤B)
    (hz : 0≤z i j ∧ z i j≤b+1) (hX : 0≤X i j ∧ X i j≤b) :
    |cutTerm small rowU colU x q z X i j|≤2*B := by
  by_cases hc : rowU i=colU j
  · simp [cutTerm,hs,hc]
    linarith
  · have hb := hcap hc
    have hdiff : |z i j-X i j|≤2*B := by
      apply abs_le.mpr
      constructor <;> linarith [hz.1,hz.2,hX.1,hX.2]
    simp only [cutTerm,hs,Bool.false_eq_true,ite_false,abs_mul,abs_indicator_sub hc,one_mul]
    exact hdiff

/-- Isolating the sole crossing tree edge in the actual signed cut
equations gives the forest displacement bound. Small cells retain both
incidences, so the statement covers every unbalanced small profile. -/
theorem displacement_bound (small tree : I → J → Bool)
    (rowU : I → Bool) (colU : J → Bool) (x q z X b : I → J → ℝ)
    (i₀ : I) (j₀ : J) (d : ℝ)
    (hd : (Fintype.card I*Fintype.card J : ℕ)≤d)
    (hB : 1≤b i₀ j₀) (hs₀ : small i₀ j₀=false)
    (hcross : rowU i₀≠colU j₀)
    (hr : ∀ i, rowU i=true → rowDifference small x z X i=0)
    (hc : ∀ j, colU j=true → columnDifference small q z X j=0)
    (hX : ∀ i j, 0≤X i j ∧ X i j≤b i j)
    (hsmall : ∀ i j, small i j=true →
      b i j≤b i₀ j₀ ∧ (0≤x i j ∧ x i j≤b i j) ∧ (0≤q i j ∧ q i j≤b i j))
    (htree : ∀ i j, tree i j=true → (i,j)≠(i₀,j₀) → rowU i=colU j)
    (hfree : ∀ i j, small i j=false → tree i j=false →
      (0≤z i j ∧ z i j≤b i j+1) ∧ (rowU i≠colU j → b i j≤b i₀ j₀)) :
    |z i₀ j₀-X i₀ j₀|≤4*d*b i₀ j₀ := by
  let f : I×J → ℝ := fun a => cutTerm small rowU colU x q z X a.1 a.2
  have hsum : (∑ a, f a)=0 := by
    simpa only [Fintype.sum_prod_type,f] using cut_sum_zero small rowU colU x q z X hr hc
  have hrest : ∀ a∈(Finset.univ.erase (i₀,j₀) : Finset (I×J)), |f a|≤2*b i₀ j₀ := by
    rintro ⟨i,j⟩ ha
    have hne : (i,j)≠(i₀,j₀) := (Finset.mem_erase.mp ha).1
    by_cases hs : small i j=true
    · exact small_term_bound small rowU colU x q z X i j (b i j) (b i₀ j₀)
        hs (hsmall i j hs).1 (hsmall i j hs).2.1 (hsmall i j hs).2.2 (hX i j)
    · have hs' : small i j=false := Bool.eq_false_iff.mpr hs
      by_cases ht : tree i j=true
      · have he := htree i j ht hne
        simp [f,cutTerm,hs',he]
        linarith
      · have ht' : tree i j=false := Bool.eq_false_iff.mpr ht
        exact free_term_bound small rowU colU x q z X i j (b i j) (b i₀ j₀)
          hs' hB (hfree i j hs' ht').2 (hfree i j hs' ht').1 (hX i j)
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (I×J)))
    (a := (i₀,j₀)) f (Finset.mem_univ _)
  have hisolate : f (i₀,j₀)=-(∑ a∈Finset.univ.erase (i₀,j₀), f a) := by
    rw [hsum] at hsplit
    linarith
  have htarget : |f (i₀,j₀)|=|z i₀ j₀-X i₀ j₀| := by
    simp only [f,cutTerm,hs₀,Bool.false_eq_true,ite_false,abs_mul,
      abs_indicator_sub hcross,one_mul]
  have hbound : |f (i₀,j₀)|≤(Fintype.card I*Fintype.card J:ℕ)*(2*b i₀ j₀) := by
    rw [hisolate,abs_neg]
    calc
      |∑ a∈Finset.univ.erase (i₀,j₀), f a|≤
        ∑ a∈Finset.univ.erase (i₀,j₀), |f a| := Finset.abs_sum_le_sum_abs _ _
      _≤∑ _a∈(Finset.univ.erase (i₀,j₀) : Finset (I×J)), 2*b i₀ j₀ :=
        Finset.sum_le_sum hrest
      _≤(Fintype.card I*Fintype.card J:ℕ)*(2*b i₀ j₀) := by
        simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ,Fintype.card_prod,nsmul_eq_mul]
        have hn : (Fintype.card I*Fintype.card J-1:ℕ)≤Fintype.card I*Fintype.card J := Nat.sub_le _ _
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by linarith)
  rw [htarget] at hbound
  have hdb : 0≤d := le_trans (Nat.cast_nonneg _) hd
  have hn : (Fintype.card I*Fintype.card J:ℕ)* (2*b i₀ j₀)≤2*d*b i₀ j₀ := by
    nlinarith
  exact hbound.trans (hn.trans (by nlinarith))

end ContingencyTables.ForestCut

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestCapacity
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual bipartite cell forests and their completion intervals

The graph vertices are the original row and column labels. Capacities
are attached to unordered row-column edges. The deletion-component cut
is constructed from the maximizing forest, so the hypotheses of the
physical cut estimate follow from actual graph properties.
-/

namespace ContingencyTables.ForestCapacity

open scoped BigOperators Classical
open SimpleGraph
open MaximumForest ForestCut

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The actual maximum-forest cut gives the source's displacement and
interval bounds for every solution of the selected nonroot equations. -/
theorem completion_interval (small : I → J → Bool) (b : I → J → ℕ)
    (T : SimpleGraph (I⊕J)) (hTG : T ≤ cellGraph small) (hT : T.IsAcyclic)
    (hmax : ∀ F : SimpleGraph (I⊕J), F ≤ cellGraph small → F.IsAcyclic →
      weight F (capacity b)≤weight T (capacity b))
    (i₀ : I) (j₀ : J) (ht : T.Adj (.inl i₀) (.inr j₀)) (root : I⊕J)
    (hroot : T.Reachable root (.inl i₀))
    (x q z X : I → J → ℝ) (d : ℝ) (W : ℕ)
    (hd : 1≤d) (hcard : (Fintype.card I*Fintype.card J:ℕ)≤d)
    (hlarge : ∀ i j, small i j=false → W≤b i j ∧ 1≤b i j)
    (hsmall : ∀ i j, small i j=true → b i j<W ∧
      (0≤x i j ∧ x i j≤b i j) ∧ (0≤q i j ∧ q i j≤b i j))
    (hX : ∀ i j, 0≤X i j ∧ X i j≤b i j)
    (hfree : ∀ i j, small i j=false → treeCell T i j=false →
      0≤z i j ∧ z i j≤b i j+1)
    (hr : ∀ i, T.Reachable root (.inl i) → Sum.inl i≠root → rowDifference small x z X i=0)
    (hc : ∀ j, T.Reachable root (.inr j) → Sum.inr j≠root → columnDifference small q z X j=0) :
    -10*d*b i₀ j₀≤z i₀ j₀ ∧ z i₀ j₀≤10*d*b i₀ j₀ := by
  let t : Sym2 (I⊕J) := s(Sum.inl i₀,Sum.inr j₀)
  let D := T.deleteEdges {t}
  obtain ⟨r,hrr,hrootSide,hcross⟩ := exists_root_avoiding_side T hT ht root hroot
  let rowU : I → Bool := fun i => side D r (.inl i)
  let colU : J → Bool := fun j => side D r (.inr j)
  have hs₀ : small i₀ j₀=false := hTG ht
  have hB : (1:ℝ)≤b i₀ j₀ := by exact_mod_cast (hlarge i₀ j₀ hs₀).2
  have hdisp : |z i₀ j₀-X i₀ j₀|≤4*d*b i₀ j₀ := by
    apply displacement_bound small (treeCell T) rowU colU x q z X
      (fun i j => (b i j:ℝ)) i₀ j₀ d hcard hB hs₀ hcross
    · intro i hi
      change side D r (.inl i)=true at hi
      apply hr i
      · have hri : D.Reachable r (.inl i) := by
          simpa only [side,decide_eq_true_eq] using hi
        exact hrr.trans (hri.mono
          (T.deleteEdges_le {t}))
      · intro he
        have hbad : side D r root=true := by simpa only [he] using hi
        exact Bool.false_ne_true (hrootSide.symm.trans hbad)
    · intro j hj
      change side D r (.inr j)=true at hj
      apply hc j
      · have hrj : D.Reachable r (.inr j) := by
          simpa only [side,decide_eq_true_eq] using hj
        exact hrr.trans (hrj.mono
          (T.deleteEdges_le {t}))
      · intro he
        have hbad : side D r root=true := by simpa only [he] using hj
        exact Bool.false_ne_true (hrootSide.symm.trans hbad)
    · exact hX
    · intro i j hs
      have hcap : b i j≤b i₀ j₀ := (Nat.le_of_lt (hsmall i j hs).1).trans
        (hlarge i₀ j₀ hs₀).1
      exact ⟨by exact_mod_cast hcap,(hsmall i j hs).2⟩
    · intro i j htree hne
      apply side_eq_of_tree_edge T t r
      · exact of_decide_eq_true htree
      · exact fun he => hne (cell_edge_injective he)
    · intro i j hs htree
      refine ⟨hfree i j hs htree,?_⟩
      intro hcut
      have hgraph : (cellGraph small).Adj (.inl i) (.inr j) := hs
      have hcap := crossing_free_edge_le (cellGraph small) T (capacity b)
        hTG hT hmax t (by simpa [t] using ht) r hgraph
        (by simpa only [treeCell,decide_eq_false_iff_not] using htree) hcut
      exact_mod_cast hcap
  exact physical_interval_of_displacement d (b i₀ j₀) (X i₀ j₀) (z i₀ j₀)
    hd (Nat.cast_nonneg _) (hX i₀ j₀) hdisp

end ContingencyTables.ForestCapacity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_GraphIntegralCompletion
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integral completion of actual graph incidence equations

Integral root-path flows give an explicit solution of every nonroot
incidence equation. This works directly on the finite row/column graph,
including disconnected components and singleton components.
-/

namespace ContingencyTables.GraphIntegralCompletion

open scoped BigOperators Classical
open SimpleGraph

variable {V : Type*} [Fintype V]

omit [Fintype V] in
lemma edgeFlow_skew (u v a b : V) : edgeFlow u v a b= -edgeFlow u v b a := by
  unfold edgeFlow
  ring

omit [Fintype V] in
lemma edgeFlow_nonadj (G : SimpleGraph V) {u v a b : V}
    (h : G.Adj u v) (hab : ¬G.Adj a b) : edgeFlow u v a b=0 := by
  have hf : ¬(u=a ∧ v=b) := by rintro ⟨rfl,rfl⟩; exact hab h
  have hr : ¬(u=b ∧ v=a) := by rintro ⟨rfl,rfl⟩; exact hab h.symm
  simp only [edgeFlow,hf,hr,ite_false,sub_self]

lemma edgeFlow_sum (u v a : V) :
    (∑ b, edgeFlow u v a b)=(if u=a then (1:ℤ) else 0)-(if v=a then 1 else 0) := by
  simp [edgeFlow,Finset.sum_sub_distrib,ite_and]

omit [Fintype V] in
lemma walkFlow_cons {G : SimpleGraph V} {u v w : V} (h : G.Adj u v)
    (p : G.Walk v w) (a b : V) :
    walkFlow (Walk.cons h p) a b=edgeFlow u v a b+walkFlow p a b := by
  simp only [walkFlow,Walk.darts_cons,List.map_cons,List.sum_cons]

omit [Fintype V] in
lemma walkFlow_skew {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (a b : V) :
    walkFlow p a b= -walkFlow p b a := by
  induction p with
  | nil => simp only [walkFlow_nil,neg_zero]
  | cons h p ih => rw [walkFlow_cons,walkFlow_cons,edgeFlow_skew,ih]; ring

omit [Fintype V] in
lemma walkFlow_supported {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (a b : V) (hab : ¬G.Adj a b) : walkFlow p a b=0 := by
  induction p with
  | nil => rfl
  | cons h p ih => rw [walkFlow_cons,edgeFlow_nonadj G h hab,ih,zero_add]

lemma walkFlow_sum {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (a : V) :
    (∑ b, walkFlow p a b)=(if u=a then (1:ℤ) else 0)-(if v=a then 1 else 0) := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp_rw [walkFlow_cons]
    rw [Finset.sum_add_distrib,edgeFlow_sum,ih]
    ring

end ContingencyTables.GraphIntegralCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_GraphCompletionCounts
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Multiplicity-one forest-coordinate sums

The finite coordinates are the actual tree cells of the row/column
forest, with physical intervals [-10 d b,10 d b]. A solution of the
nonroot equations contributes exactly once, with its original weight.
-/

namespace ContingencyTables.GraphCompletionCounts

open scoped BigOperators Classical
open SimpleGraph
open ForestCapacity GraphIntegralCompletion

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev TreeIndex (T : SimpleGraph (I⊕J)) (d : ℕ) (b : I → J → ℕ) :=
  (e : TreeCell T) → Fin (20*d*b e.val.1 e.val.2+1)

noncomputable def physical (T : SimpleGraph (I⊕J)) (d : ℕ) (b : I → J → ℕ)
    (a : TreeIndex T d b) (i : I) (j : J) : ℤ :=
  if h : T.Adj (.inl i) (.inr j) then
    -((10*d*b i j:ℕ):ℤ)+(a ⟨(i,j),h⟩).val else 0

omit [Fintype I] [Fintype J] in
lemma physical_supported (T : SimpleGraph (I⊕J)) (d : ℕ) (b : I → J → ℕ)
    (a : TreeIndex T d b) (i : I) (j : J) (h : ¬T.Adj (.inl i) (.inr j)) :
    physical T d b a i j=0 := by simp only [physical,h,not_false_eq_true,dite_eq_right]

omit [Fintype I] [Fintype J] in
lemma physical_injective (T : SimpleGraph (I⊕J)) (d : ℕ) (b : I → J → ℕ) :
    Function.Injective (physical T d b) := by
  intro a a' h
  funext e
  apply Fin.ext
  have he := congrFun (congrFun h e.val.1) e.val.2
  simp only [physical,e.property,dite_eq_left] at he
  exact_mod_cast (add_left_cancel he : ((a e).val:ℤ)=((a' e).val:ℤ))

end ContingencyTables.GraphCompletionCounts

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestPenaltyApplication
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Literal companion row/column and unary tree penalties

The physical row view is ell+x; the physical column view is ell+M-y.
The line groups are the disjoint original row and column coordinates.
Roots are the actual chosen component roots of the large-cell forest.
Only the false (row) coordinate of each tree cell carries its interval
penalty. Thus the concrete exact factor family is precisely the source's
nonroot indicator times its root/tree penalty weight.
-/

namespace ContingencyTables.ForestPenaltyApplication

open scoped BigOperators Classical Matrix
open SimpleGraph CommonBasesFPRAS
open EqualitySoftening ProductIntegerSignature ScalarPenalty
open ForestCapacity GraphIntegralCompletion RowColumnPenalties

variable {I J : Type*} [Fintype I] [Fintype J]

lemma line_affine (ell : I → J → ℤ) (M : I → J → ℕ) (r : I → ℤ) (c : J → ℤ)
    (z : ((I×J)×Bool) → ℕ) (g : I⊕J) :
    lineOffset ell M r c g+(lineTotal cellLine z g:ℝ)*viewSlope (I := I) (J := J) g=
      deviation ell M r c z g := by
  cases g with
  | inl i =>
    rw [lineTotal_row]
    simp only [lineOffset,deviation,Sum.elim_inl,viewSlope,mul_one,physicalRow,rowView]
    push_cast
    rw [Finset.sum_add_distrib]
    ring
  | inr j =>
    rw [lineTotal_column]
    simp only [lineOffset,deviation,Sum.elim_inr,viewSlope,mul_neg_one,physicalColumn]
    push_cast
    rw [Finset.sum_sub_distrib]
    ring

end ContingencyTables.ForestPenaltyApplication

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestLiteralCount
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Literal doubled-coordinate profiles for companion completion counts

Small views are retained separately. Every large pair is balanced, with
its physical tree or free-cell value represented in the prescribed finite
interval. These identities connect the concrete laminar factor family to
the actual graph completion sum.
-/

namespace ContingencyTables.ForestLiteralCount

open scoped BigOperators Classical
open SimpleGraph
open GraphIntegralCompletion GraphCompletionCounts ForestCapacity

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def cellCount (T : SimpleGraph (I⊕J)) (d : ℕ) (b free : I → J → ℕ)
    (a : TreeIndex T d b) (i : I) (j : J) : ℕ :=
  if h : T.Adj (.inl i) (.inr j) then (a ⟨(i,j),h⟩).val else free i j

noncomputable def profile (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (d : ℕ) (b x y free : I → J → ℕ) (a : TreeIndex T d b) (u : (I×J)×Bool) : ℕ :=
  if small u.1.1 u.1.2 then (if u.2 then y u.1.1 u.1.2 else x u.1.1 u.1.2)
  else if u.2 then width T d b u.1.1 u.1.2-cellCount T d b free a u.1.1 u.1.2
    else cellCount T d b free a u.1.1 u.1.2

omit [Fintype I] [Fintype J] in
lemma cellCount_le (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (d : ℕ) (b free : I → J → ℕ) (a : TreeIndex T d b)
    (hf : ∀ i j, small i j=false → ¬T.Adj (.inl i) (.inr j) → free i j≤b i j)
    (i : I) (j : J) (hs : small i j=false) : cellCount T d b free a i j≤width T d b i j := by
  by_cases ht : T.Adj (.inl i) (.inr j)
  · simp only [cellCount,ht,dite_eq_left,width,ite_true, if_true]
    have h := (a ⟨(i,j),ht⟩).isLt
    change (a ⟨(i,j),ht⟩).val <20*d*b i j+1 at h
    omega
  · simp only [cellCount,ht,not_false_eq_true,dite_eq_right,width,ite_false]
    exact hf i j hs ht

omit [Fintype I] [Fintype J] in
lemma row_profile (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T ≤ cellGraph small) (d : ℕ) (b x y free : I → J → ℕ) (a : TreeIndex T d b)
    (i : I) (j : J) :
    ForestPenaltyApplication.physicalRow (lower T d b) (profile small T d b x y free a) i j=
      (if small i j then (x i j:ℤ) else largeValue T (physical T d b a) free i j : ℤ) := by
  by_cases ht : T.Adj (.inl i) (.inr j)
  · have hs : small i j=false := hTG ht
    simp only [ForestPenaltyApplication.physicalRow,lower,profile,hs,Bool.false_eq_true,
      ite_false,ht,ite_true, if_true,cellCount,dite_eq_left,largeValue,physical]
    push_cast
    ring
  · simp only [ForestPenaltyApplication.physicalRow,lower,ht,ite_false,profile,
      Bool.false_eq_true,cellCount,not_false_eq_true,dite_eq_right,largeValue]
    split_ifs <;> norm_num

omit [Fintype I] [Fintype J] in
lemma column_profile (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T ≤ cellGraph small) (d : ℕ) (b x y free : I → J → ℕ) (a : TreeIndex T d b)
    (hy : ∀ i j, small i j=true → y i j≤b i j)
    (hf : ∀ i j, small i j=false → ¬T.Adj (.inl i) (.inr j) → free i j≤b i j)
    (i : I) (j : J) :
    ForestPenaltyApplication.physicalColumn (lower T d b) (width T d b)
      (profile small T d b x y free a) i j=
      (if small i j then ((b i j-y i j:ℕ):ℤ)
        else largeValue T (physical T d b a) free i j : ℤ) := by
  by_cases hs : small i j=true
  · have ht : ¬T.Adj (.inl i) (.inr j) := by
      intro h
      have hh : small i j=false := hTG h
      exact Bool.false_ne_true (hh.symm.trans hs)
    simp only [ForestPenaltyApplication.physicalColumn,lower,width,ht,ite_false,profile,
      hs,ite_true, if_true,Int.cast_zero,zero_add]
    push_cast
    rw [Nat.cast_sub (hy i j hs)]
  · have hs' : small i j=false := Bool.eq_false_iff.mpr hs
    have hbound := cellCount_le small T d b free a hf i j hs'
    have hcol : ForestPenaltyApplication.physicalColumn (lower T d b) (width T d b)
        (profile small T d b x y free a) i j=
        ForestPenaltyApplication.physicalRow (lower T d b) (profile small T d b x y free a) i j := by
      simp only [ForestPenaltyApplication.physicalColumn,ForestPenaltyApplication.physicalRow,
        profile,hs',Bool.false_eq_true,ite_false,ite_true, if_true,Nat.cast_sub hbound]
      ring
    rw [hcol,row_profile small T hTG d b x y free a i j]
    simp only [hs',Bool.false_eq_true,ite_false]

lemma deviation_profile (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T ≤ cellGraph small) (d : ℕ) (b x y free : I → J → ℕ) (a : TreeIndex T d b)
    (r : I → ℤ) (c : J → ℤ)
    (hy : ∀ i j, small i j=true → y i j≤b i j)
    (hf : ∀ i j, small i j=false → ¬T.Adj (.inl i) (.inr j) → free i j≤b i j) :
    ForestPenaltyApplication.deviation (lower T d b) (width T d b) r c
      (profile small T d b x y free a)=actualDeviation small T b x y free r c (physical T d b a) := by
  funext g
  cases g with
  | inl i =>
    simp only [ForestPenaltyApplication.deviation,actualDeviation,Sum.elim_inl]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Int.cast_ite,Int.cast_natCast] using row_profile small T hTG d b x y free a i j
  | inr j =>
    simp only [ForestPenaltyApplication.deviation,actualDeviation,Sum.elim_inr]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Int.cast_ite,Int.cast_natCast] using column_profile small T hTG d b x y free a hy hf i j

omit [Fintype I] [Fintype J] in
lemma row_pointwise (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T ≤ cellGraph small) (x free : I → J → ℕ) (tree : I → J → ℤ)
    (hsupport : ∀ i j, ¬T.Adj (.inl i) (.inr j) → tree i j=0) (i : I) (j : J) :
    (if small i j then (x i j:ℤ) else largeValue T tree free i j)=tree i j+
      ForestPhysicalCompletion.fixedRow small T (fun i j => (x i j:ℤ))
        (fun i j => (free i j:ℤ)) i j := by
  by_cases ht : T.Adj (.inl i) (.inr j)
  · have hs : small i j=false := hTG ht
    simp only [hs,Bool.false_eq_true,ite_false,largeValue,ht,ite_true, if_true,
      ForestPhysicalCompletion.fixedRow,add_zero]
  · simp only [largeValue,ht,ite_false,hsupport i j ht,zero_add,
      ForestPhysicalCompletion.fixedRow]

omit [Fintype I] [Fintype J] in
lemma column_pointwise (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T ≤ cellGraph small) (b y free : I → J → ℕ) (tree : I → J → ℤ)
    (hsupport : ∀ i j, ¬T.Adj (.inl i) (.inr j) → tree i j=0) (i : I) (j : J) :
    (if small i j then ((b i j-y i j:ℕ):ℤ) else largeValue T tree free i j)=tree i j+
      ForestPhysicalCompletion.fixedColumn small T (fun i j => ((b i j-y i j:ℕ):ℤ))
        (fun i j => (free i j:ℤ)) i j := by
  by_cases ht : T.Adj (.inl i) (.inr j)
  · have hs : small i j=false := hTG ht
    simp only [hs,Bool.false_eq_true,ite_false,largeValue,ht,ite_true, if_true,
      ForestPhysicalCompletion.fixedColumn,add_zero]
  · simp only [largeValue,ht,ite_false,hsupport i j ht,zero_add,
      ForestPhysicalCompletion.fixedColumn]

end ContingencyTables.ForestLiteralCount

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestAssignmentSplit
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Splitting actual large-cell assignments into tree and free choices

The coordinate enumeration used for signatures and the graph completion
sum use exactly the same assignments. This finite equivalence records
that fact, including the larger signed tree intervals.
-/

namespace ContingencyTables.ForestAssignmentSplit

open scoped BigOperators Classical
open SimpleGraph LargePairEnumeration GraphCompletionCounts ForestCapacity ForestLiteralCount

variable {I J : Type*}

lemma freeTable_bound (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (b : I → J → ℕ) (a : FreeIndex small T b) (i : I) (j : J)
    (hs : small i j=false) (ht : ¬T.Adj (.inl i) (.inr j)) :
    freeTable small T b a i j≤b i j := by
  unfold freeTable
  rw [dite_eq_left ⟨hs,ht⟩]
  have h := (a ⟨(i,j),⟨hs,ht⟩⟩).isLt
  change (a ⟨(i,j),⟨hs,ht⟩⟩).val<b i j+1 at h
  omega

/-- The large-cell product is the tree-interval product times the
original free-cell product, each with multiplicity one. -/
noncomputable def assignmentSplit (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T ≤ cellGraph small) (d : ℕ) (b : I → J → ℕ) :
    ((a : LargeCell (fun a : I×J => small a.1 a.2)) →
      Fin (width T d b a.val.1 a.val.2+1)) ≃ TreeIndex T d b×FreeIndex small T b where
  toFun a :=
    ((fun t => Fin.cast (by simp only [width,t.property,ite_true, if_true])
      (a ⟨t.val,hTG t.property⟩)),
     fun f => Fin.cast (by simp only [width,f.property.2,ite_false])
      (a ⟨f.val,f.property.1⟩))
  invFun a l := if h : T.Adj (.inl l.val.1) (.inr l.val.2) then
      Fin.cast (by simp only [width,h,ite_true, if_true]) (a.1 ⟨l.val,h⟩)
    else Fin.cast (by simp only [width,h,ite_false]) (a.2 ⟨l.val,⟨l.property,h⟩⟩)
  left_inv a := by
    funext l
    by_cases ht : T.Adj (.inl l.val.1) (.inr l.val.2)
    · apply Fin.ext
      simp [ht]
    · apply Fin.ext
      simp [ht]
  right_inv a := by
    apply Prod.ext
    · funext t
      apply Fin.ext
      simp [t.property]
    · funext f
      apply Fin.ext
      simp [f.property.2]

/-- A tree/free split assignment gives precisely the cell counts in the
literal graph profile, before taking the complementary column view. -/
lemma split_cellCount (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T ≤ cellGraph small) (d : ℕ) (b : I → J → ℕ)
    (a : TreeIndex T d b×FreeIndex small T b)
    (l : LargeCell (fun a : I×J => small a.1 a.2)) :
    (((assignmentSplit small T hTG d b).symm a l).val)=
      cellCount T d b (freeTable small T b a.2) a.1 l.val.1 l.val.2 := by
  by_cases ht : T.Adj (.inl l.val.1) (.inr l.val.2)
  · simp [assignmentSplit,Equiv.symm,ht,cellCount]
  · simp [assignmentSplit,Equiv.symm,ht,cellCount,freeTable,l.property]

end ContingencyTables.ForestAssignmentSplit

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TwoLiftStates
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual paired states and the two factorial weights

Every physical cell contains an arbitrary finite bundle of paired labels.
The plain and one-hole/one-full predicates imply the exact cell count
identities. Thus the literal subset lifts agree on plain states and obey
the manuscript's W² comparison on every actual chain state.
-/

namespace ContingencyTables.TwoLiftStates

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures LabelledFactorial

variable {P C : Type*} [Fintype P] [Fintype C]

omit [Fintype P] in
lemma pair_injective : Function.Injective (pair : P → (P × Bool) × (P × Bool)) := by
  intro p q h
  exact congrArg (fun x => x.1.1) h

end ContingencyTables.TwoLiftStates

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestRootPenalty
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual root residuals of the integral forest completion

Summing a root-path flow gives the prescribed demand minus the total
demand in the component. This formula also applies at roots and on
singleton components, where the nonroot-only margin lemma is vacuous.
-/

namespace ContingencyTables.ForestRootPenalty

open scoped BigOperators Classical
open SimpleGraph GraphIntegralCompletion ForestPhysicalCompletion ForestLiteralCount

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def residualDemand (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (r : I → ℤ) (c : J → ℤ) (x q free : I → J → ℤ) : I⊕J → ℤ :=
  Sum.elim (rowResidual small T r x free) (fun j => -columnResidual small T c q free j)

end ContingencyTables.ForestRootPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RealKernelApproximation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accumulating rational implementation errors against a real kernel

The exact companion weights may be real. The implemented probabilities
are rational; comparison takes place after their canonical real cast.
-/

namespace ContingencyTables.RealKernelApproximation
open scoped BigOperators Classical
open CommonBasesFPRAS ResidualMixture FirstSuccess

noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]

def rationalKernel (K : X → RationalLaw Y) : FiniteKernel X Y where
  P x y := ((K x).mass y:ℝ)
  nonnegative x y := by exact_mod_cast (K x).nonnegative y
  substochastic x := by
    have h := congrArg (fun z : ℚ => (z:ℝ)) (K x).total
    simpa only [Rat.cast_sum,Rat.cast_one] using h.le

end
end ContingencyTables.RealKernelApproximation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_InitialDefectChoices
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual remaining label choices for an initial defect

The hole and full pair are removed before the remaining row labels are
chosen. This gives the finite combinatorial space underlying the exact
local initialization brackets, including two removed labels in one cell.
-/

namespace ContingencyTables.InitialDefectChoices

open scoped BigOperators Classical
open CommonBasesFPRAS TwoLiftStates
open InitialTransversals (Copy)

variable {C : Type*} [Fintype C] (b : C → ℕ) (p q : Copy b)

noncomputable def encode (S : (c : C) → Finset (Local b p q c)) : Set (Copy b×Bool) :=
  fun a => if a.1=q then True else if h : a.1≠p ∧ a.1≠q then
    if a.2 then (⟨a.1.2,h⟩:Local b p q a.1.1)∉S a.1.1
      else (⟨a.1.2,h⟩:Local b p q a.1.1)∈S a.1.1
    else False

omit [Fintype C] in
lemma encode_full (S : (c : C) → Finset (Local b p q c)) (t : Bool) :
    (q,t)∈encode b p q S := by
  change (if q=q then True else _) 
  simp

omit [Fintype C] in
lemma encode_hole (hpq : p≠q) (S : (c : C) → Finset (Local b p q c)) (t : Bool) :
    (p,t)∉encode b p q S := by
  change ¬(if p=q then True else if h : p≠p ∧ p≠q then _ else False)
  simp [hpq]

omit [Fintype C] in
lemma encode_false (S : (c : C) → Finset (Local b p q c)) (a : Copy b)
    (ha : a≠p ∧ a≠q) :
    (a,false)∈encode b p q S ↔ (⟨a.2,ha⟩:Local b p q a.1)∈S a.1 := by
  change (if a=q then True else if h : a≠p ∧ a≠q then _ else False)↔_
  simp [ha]

omit [Fintype C] in
lemma encode_true (S : (c : C) → Finset (Local b p q c)) (a : Copy b)
    (ha : a≠p ∧ a≠q) :
    (a,true)∈encode b p q S ↔ (⟨a.2,ha⟩:Local b p q a.1)∉S a.1 := by
  change (if a=q then True else if h : a≠p ∧ a≠q then _ else False)↔_
  simp [ha]

lemma encode_defect (hpq : p≠q) (S : (c : C) → Finset (Local b p q c)) :
    DefectState pairs (TwoLiftStates.pair p) (TwoLiftStates.pair q) (encode b p q S) := by
  refine ⟨pair_mem p,pair_mem q,(fun h => hpq (pair_injective h)),?_,?_,?_⟩
  · exact ⟨encode_hole b p q hpq S false,encode_hole b p q hpq S true⟩
  · exact ⟨encode_full b p q S false,encode_full b p q S true⟩
  · intro t ht htp htq
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp (show t∈Finset.univ.toList.map TwoLiftStates.pair from ht)
    have ha : a≠p ∧ a≠q := ⟨fun h => htp (congrArg TwoLiftStates.pair h),
      fun h => htq (congrArg TwoLiftStates.pair h)⟩
    by_cases hs : (⟨a.2,ha⟩:Local b p q a.1)∈S a.1
    · exact Or.inl ⟨(encode_false b p q S a ha).mpr hs,
        fun h => (encode_true b p q S a ha).mp h hs⟩
    · exact Or.inr ⟨(encode_true b p q S a ha).mpr hs,
        fun h => hs ((encode_false b p q S a ha).mp h)⟩

noncomputable def defectEquivChoices (hpq : p≠q) :
    {S : Set (Copy b×Bool) // DefectState pairs (TwoLiftStates.pair p) (TwoLiftStates.pair q) S} ≃
      ((c : C) → Finset (Local b p q c)) where
  toFun S c := Finset.univ.filter (fun k => ((⟨c,k.val⟩,false):Copy b×Bool)∈S.val)
  invFun S := ⟨encode b p q S,encode_defect b p q hpq S⟩
  left_inv S := by
    apply Subtype.ext
    ext ⟨a,t⟩
    let R : (c : C) → Finset (Local b p q c) :=
      fun c => Finset.univ.filter (fun k => ((⟨c,k.val⟩,false):Copy b×Bool)∈S.val)
    change (a,t)∈encode b p q R ↔ (a,t)∈S.val
    by_cases hap : a=p
    · subst a
      have he := S.property.2.2.2.1
      cases t <;> simp only [TwoLiftStates.pair,PairEmpty] at he
      · exact iff_of_false (encode_hole b p q hpq R false) he.1
      · exact iff_of_false (encode_hole b p q hpq R true) he.2
    · by_cases haq : a=q
      · subst a
        have hf := S.property.2.2.2.2.1
        cases t <;> simp only [TwoLiftStates.pair,PairFull] at hf
        · exact iff_of_true (encode_full b p q R false) hf.1
        · exact iff_of_true (encode_full b p q R true) hf.2
      · have ha : a≠p ∧ a≠q := ⟨hap,haq⟩
        have hs := S.property.2.2.2.2.2 (TwoLiftStates.pair a) (pair_mem a)
          (fun h => hap (pair_injective h)) (fun h => haq (pair_injective h))
        cases t
        · rw [encode_false b p q R a ha]
          simp [R]
        · rw [encode_true b p q R a ha]
          dsimp only [R]
          simp only [Finset.mem_filter,Finset.mem_univ,true_and]
          rcases hs with ⟨hf,ht⟩|⟨ht,hf⟩ <;>
            simp only [TwoLiftStates.pair] at hf ht <;> tauto
  right_inv S := by
    funext c
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact encode_false b p q S ⟨c,k.val⟩ k.property

noncomputable def chosen (S : (c : C) → Finset (Local b p q c)) (c : C) : Finset (Fin (b c)) :=
  (S c).map ⟨Subtype.val,Subtype.val_injective⟩

noncomputable def localWeight (c : C) (S : Finset (Local b p q c)) : ℝ :=
  (((S.card+(if q.1=c then 1 else 0)).factorial:ℝ)*
    ((Fintype.card (Local b p q c)-S.card+(if q.1=c then 1 else 0)).factorial:ℝ))/(b c).factorial

end ContingencyTables.InitialDefectChoices

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledPenalty
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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

lemma intervalCost_nonnegative (x : ℝ) : 0 ≤ intervalCost x := le_max_left _ _

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual continuous forest penalty stays within the source allowance -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestPhysicalCompletion ForestRootPenalty
open BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def zeroAssignment (A : Instance I J) : FreeIndex A.small A.T A.b :=
  fun _ => ⟨0,Nat.succ_pos _⟩

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PowerOfTwoApproximation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded rational approximation to the evaluator's power of two -/

namespace ContingencyTables.PowerOfTwoApproximation

open RationalRootBisection

noncomputable section

def rounded (beta : ℚ) (s : ℕ) : ℝ := (numerator beta s:ℝ)/s

end

end ContingencyTables.PowerOfTwoApproximation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteObservableTransport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact transport of finite experiments with rational outputs

Output values need not form a finite type. Equality against every real
observable is preserved by deterministic postprocessing and by the
independent arrays used in the counting estimator.
-/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS
open scoped Classical

noncomputable section
variable {X Y U V Z W : Type*}
variable [Fintype X] [Fintype Y] [Fintype U] [Fintype V]

def SameLaw (f : X → Z) (g : Y → Z) : Prop :=
  ∀ phi : Z → ℝ,uniformAverage (fun x => phi (f x))=uniformAverage (fun y => phi (g y))

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_InitialDrawReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact invariance of the finite initializer under computed cell order -/

namespace ContingencyTables.InitialFactorialBits

open CommonBasesFPRAS ResidualMixture FirstSuccess FixedCardinalityMixture
open InitialTransversals CompanionFactorialApplication
open scoped BigOperators Classical
noncomputable section
variable {C : Type*} [Fintype C] {q : ℕ}

def finiteChoiceLaw (b : C → ℕ) (B : ℕ) : RationalLaw ((c : C) → Finset (Fin (b c))) where
  mass S := ∏ c,(mapLaw (uniformLaw (α := Fin (drawBits B (b c)) → Bool))
    (subsetDraw B (b c))).mass (S c)
  nonnegative S := Finset.prod_nonneg (fun c _ => (mapLaw
    (uniformLaw (α := Fin (drawBits B (b c)) → Bool)) (subsetDraw B (b c))).nonnegative (S c))
  total := by
    rw [←Fintype.prod_sum]
    simp only [RationalLaw.total,Finset.prod_const_one]

end
end ContingencyTables.InitialFactorialBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MedianFractionProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary fraction median with polynomial running time -/

namespace ContingencyTables.MedianFractionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial

def insertRaw (q : Fraction) : List Fraction → List Fraction
  | [] => [q]
  | x::xs => if TreeFraction.less (x,q) then x::insertRaw q xs else q::x::xs

end ContingencyTables.MedianFractionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Graphs_SafeTrace
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.SafeTrace
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ]

inductive Path (M : Λ → TM1.Stmt Γ Λ σ) (safe : Λ → Prop) :
    ℕ → TM1.Cfg Γ Λ σ → TM1.Cfg Γ Λ σ → Prop
  | refl (c) : Path M safe 0 c c
  | cons {n c d} (hc : ∀ l,c.l=some l→safe l)
      (rest : Path M safe n (advance (TM1.step M) c) d) : Path M safe (n+1) c d

end MatchingFPRAS.SafeTrace

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

def retryProc : RegisterProc.Proc (K Reg) :=
  RegisterProc.seq (split 1 2 (by decide))
    (RegisterProc.seq (copy 1 0 (by decide)) (clear 1))

end ContingencyTables.OnlineIntegerRetry

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestAffineProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary list evaluation of the forest's signed affine numerators

Each coefficient is stored by its nonnegative and nonpositive parts.
The program performs two finite product sums and passes their difference
to the proved interval-cost routine. Large capacities are never iterated.
-/

namespace ContingencyTables.ForestAffineProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

noncomputable section
variable {q : ℕ}

def data (offset : ℤ) (coefficient : Fin q → ℤ) (v : Fin q → ℕ) (den : ℕ) : Input :=
  ((signedParts offset,List.ofFn (fun i => (signedParts (coefficient i),v i))),den)


open CompanionFactorialApplication ForestAssignmentSplit CompanionOracleDensity GraphCompletionCounts

end
end ContingencyTables.ForestAffineProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestBoxCardinality
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The expanded physical forest box still has a short cardinality bound

The tree interval width 20db has at most (b+1)^2 integer positions
when every large capacity is at least 20d. This provides a uniform bound
for the positive equality-softened balanced sums before taking limits.
-/

namespace ContingencyTables.ForestBoxCardinality

open scoped BigOperators Classical
open CompanionFactorialApplication ForestLiteralCount

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev Assignments (A : Instance I J) :=
  (a : I×J) → Fin (width A.T A.d A.b a.1 a.2+1)

end ContingencyTables.ForestBoxCardinality

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCompletion
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forest completion with an explicit component-root selector

Only reachability and constancy on each component are needed for the
integral completion. Making these data explicit permits the executed
least-root selector to replace the original quotient representative,
without asserting that two different selectors are equal.
-/

namespace ContingencyTables.RootedCompletion

open scoped BigOperators Classical
open SimpleGraph GraphIntegralCompletion ForestCut ForestCapacity MaximumForest

variable {V : Type*}

lemma Selection.idempotent {G : SimpleGraph V} (S : Selection G) (v : V) :
    S.root (S.root v)=S.root v := (S.constant (S.reachable v)).symm

variable [Fintype V]

lemma flow_skew {G : SimpleGraph V} (S : Selection G) (r : V → ℤ) (a b : V) :
    flow S r a b= -flow S r b a := by
  unfold flow
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [walkFlow_skew,mul_neg]

lemma flow_supported {G : SimpleGraph V} (S : Selection G) (r : V → ℤ)
    (a b : V) (hab : ¬G.Adj a b) : flow S r a b=0 := by
  unfold flow
  apply Finset.sum_eq_zero
  intro v _
  rw [walkFlow_supported _ a b hab,mul_zero]

theorem flow_divergence_all {G : SimpleGraph V} (S : Selection G) (r : V → ℤ) (a : V) :
    (∑ b,flow S r a b)=r a-∑ v,if S.root v=a then r v else 0 := by
  unfold flow
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum,walkFlow_sum,mul_sub,Finset.sum_sub_distrib]
  simp [mul_ite,eq_comm]

theorem flow_divergence {G : SimpleGraph V} (S : Selection G) (r : V → ℤ)
    (a : V) (ha : a≠S.root a) : (∑ b,flow S r a b)=r a := by
  have hroot : ∀ v,S.root v≠a := by
    intro v hv
    have h := S.idempotent v
    rw [hv] at h
    exact ha h.symm
  rw [flow_divergence_all]
  simp only [hroot,ite_false,Finset.sum_const_zero,sub_zero]

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] in
lemma table_supported (T : SimpleGraph (I⊕J)) (S : Selection T)
    (r : I → ℤ) (c : J → ℤ) (i : I) (j : J) (h : ¬T.Adj (.inl i) (.inr j)) :
    table T S r c i j=0 := flow_supported S _ _ _ h

omit [Fintype V] in
lemma table_row (small : I → J → Bool) (T : SimpleGraph (I⊕J)) (S : Selection T)
    (hT : T ≤ cellGraph small) (r : I → ℤ) (c : J → ℤ) (i : I)
    (hi : Sum.inl i≠S.root (.inl i)) : (∑ j,table T S r c i j)=r i := by
  have hs := flow_divergence S (Sum.elim r (fun j => -c j)) (.inl i) hi
  rw [Fintype.sum_sum_type] at hs
  have hz : (∑ i',flow S (Sum.elim r (fun j => -c j)) (.inl i) (.inl i'))=0 := by
    apply Finset.sum_eq_zero
    intro i' _
    apply flow_supported
    intro h
    exact hT h
  simpa only [hz,zero_add,Sum.elim_inl,table] using hs

omit [Fintype V] in
lemma table_column (small : I → J → Bool) (T : SimpleGraph (I⊕J)) (S : Selection T)
    (hT : T ≤ cellGraph small) (r : I → ℤ) (c : J → ℤ) (j : J)
    (hj : Sum.inr j≠S.root (.inr j)) : (∑ i,table T S r c i j)=c j := by
  have hs := flow_divergence S (Sum.elim r (fun j => -c j)) (.inr j) hj
  rw [Fintype.sum_sum_type] at hs
  have hz : (∑ j',flow S (Sum.elim r (fun j => -c j)) (.inr j) (.inr j'))=0 := by
    apply Finset.sum_eq_zero
    intro j' _
    apply flow_supported
    intro h
    exact hT h
  have hskew : (∑ i,flow S (Sum.elim r (fun j => -c j)) (.inr j) (.inl i))=
      -(∑ i,table T S r c i j) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact flow_skew S _ _ _
  simpa only [hz,add_zero,Sum.elim_inr,hskew,neg_inj] using hs

omit [Fintype V] in
theorem zero_of_nonroot_sums (T : SimpleGraph (I⊕J)) (S : Selection T)
    (hT : T.IsAcyclic) (z : I → J → ℝ)
    (hsupport : ∀ i j,¬T.Adj (.inl i) (.inr j) → z i j=0)
    (hr : ∀ i,Sum.inl i≠S.root (.inl i) → (∑ j,z i j)=0)
    (hc : ∀ j,Sum.inr j≠S.root (.inr j) → (∑ i,z i j)=0) :
    ∀ i j,z i j=0 := by
  intro i₀ j₀
  by_cases ht : T.Adj (.inl i₀) (.inr j₀)
  · let t : Sym2 (I⊕J) := s(Sum.inl i₀,Sum.inr j₀)
    let D := T.deleteEdges {t}
    let root := S.root (.inl i₀)
    obtain ⟨v,hv,hroot,hcross⟩ := exists_root_avoiding_side T hT ht root
      (S.reachable (.inl i₀)).symm
    let rowU : I → Bool := fun i => side D v (.inl i)
    let colU : J → Bool := fun j => side D v (.inr j)
    have hcross' : rowU i₀≠colU j₀ := hcross
    have hnonroot : ∀ a : I⊕J,side D v a=true → a≠S.root a := by
      intro a ha he
      have hva : D.Reachable v a := by simpa only [side,decide_eq_true_eq] using ha
      have hcomp := hv.trans (hva.mono (T.deleteEdges_le {t}))
      have hsame : S.root a=root := by
        rw [←S.constant hcomp,S.idempotent]
      have haroot : a=root := he.trans hsame
      have hbad : side D v root=true := by simpa only [haroot] using ha
      exact Bool.false_ne_true (hroot.symm.trans hbad)
    let f : I×J → ℝ := fun a => cutTerm (fun _ _ => false) rowU colU 0 0 z 0 a.1 a.2
    have hsum : (∑ a,f a)=0 := by
      rw [Fintype.sum_prod_type]
      apply cut_sum_zero
      · intro i hi
        simpa only [rowDifference,Bool.false_eq_true,ite_false,Pi.zero_apply,sub_zero]
          using hr i (hnonroot (.inl i) hi)
      · intro j hj
        simpa only [columnDifference,Bool.false_eq_true,ite_false,Pi.zero_apply,sub_zero]
          using hc j (hnonroot (.inr j) hj)
    have hother : ∀ a : I×J,a≠(i₀,j₀) → f a=0 := by
      rintro ⟨i,j⟩ hne
      by_cases hij : T.Adj (.inl i) (.inr j)
      · have he : rowU i=colU j := side_eq_of_tree_edge T t v hij
          (fun h => hne (cell_edge_injective h))
        simp [f,cutTerm,he]
      · simp [f,cutTerm,hsupport i j hij]
    have hisolate : (∑ a,f a)=f (i₀,j₀) := by
      apply Finset.sum_eq_single (i₀,j₀)
      · intro a _ hne
        exact hother a hne
      · simp
    rw [hisolate] at hsum
    have habs : |f (i₀,j₀)|=|z i₀ j₀| := by
      simp only [f,cutTerm,Bool.false_eq_true,ite_false,Pi.zero_apply,sub_zero,
        abs_mul,abs_indicator_sub hcross',one_mul]
    rw [hsum,abs_zero] at habs
    exact abs_eq_zero.mp habs.symm
  · exact hsupport i₀ j₀ ht

omit [Fintype V] in
theorem table_unique (small : I → J → Bool) (T : SimpleGraph (I⊕J)) (S : Selection T)
    (hTG : T ≤ cellGraph small) (hT : T.IsAcyclic) (r : I → ℤ) (c : J → ℤ)
    (z : I → J → ℤ)
    (hsupport : ∀ i j,¬T.Adj (.inl i) (.inr j) → z i j=0)
    (hr : ∀ i,Sum.inl i≠S.root (.inl i) → (∑ j,z i j)=r i)
    (hc : ∀ j,Sum.inr j≠S.root (.inr j) → (∑ i,z i j)=c j) :
    z=table T S r c := by
  let delta : I → J → ℝ := fun i j => (z i j:ℝ)-table T S r c i j
  have hz := zero_of_nonroot_sums T S hT delta (by
    intro i j hij
    simp only [delta,hsupport i j hij,Int.cast_zero,table_supported T S r c i j hij,sub_self])
    (by
      intro i hi
      dsimp only [delta]
      rw [Finset.sum_sub_distrib,←Int.cast_sum,←Int.cast_sum,
        hr i hi,table_row small T S hTG r c i hi,sub_self])
    (by
      intro j hj
      dsimp only [delta]
      rw [Finset.sum_sub_distrib,←Int.cast_sum,←Int.cast_sum,
        hc j hj,table_column small T S hTG r c j hj,sub_self])
  funext i j
  exact_mod_cast (sub_eq_zero.mp (hz i j))

end ContingencyTables.RootedCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCut
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit endpoint on the side away from a selected root

One reachability test in the edge-deleted forest selects the endpoint.
No choice of a component representative or of a cut vertex is needed.
-/

namespace ContingencyTables.RootedCut

open scoped BigOperators Classical
open SimpleGraph MaximumForest RootedCompletion GraphCompletionCounts ForestCut
open ForestCapacity

variable {V : Type*}

theorem away_properties (T : SimpleGraph V) (hT : T.IsAcyclic) {u v : V}
    (ht : T.Adj u v) (root : V) (hr : T.Reachable root u) :
    T.Reachable root (away T u v root) ∧ cut T u v root root=false ∧
      cut T u v root u≠cut T u v root v := by
  let D := T.deleteEdges {s(u,v)}
  have hsep : ¬D.Reachable u v :=
    isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hT ht)
  by_cases hru : D.Reachable u root
  · have ha : away T u v root=v := ite_eq_left hru
    refine ⟨by simpa only [ha] using hr.trans ht.reachable,?_,?_⟩
    · have hn : ¬D.Reachable v root := fun h => hsep (hru.trans h.symm)
      change side D (away T u v root) root=false
      rw [ha]
      simpa only [side,decide_eq_false_iff_not] using hn
    · have hn : ¬D.Reachable v u := fun h => hsep h.symm
      change side D (away T u v root) u≠side D (away T u v root) v
      rw [ha]
      simp [side,hn]
  · have ha : away T u v root=u := ite_eq_right hru
    refine ⟨by simpa only [ha] using hr,?_,?_⟩
    · change side D (away T u v root) root=false
      rw [ha]
      simpa only [side,decide_eq_false_iff_not] using hru
    · change side D (away T u v root) u≠side D (away T u v root) v
      rw [ha]
      simp [side,hsep]

variable {I J : Type*}

lemma treeCut_self (T : SimpleGraph (I⊕J)) (S : Selection T) (hT : T.IsAcyclic)
    (t : TreeCell T) : treeCut T S t (.inl t.val.1)≠treeCut T S t (.inr t.val.2) :=
  (away_properties T hT t.property _ (S.reachable _).symm).2.2

noncomputable def sign (T : SimpleGraph (I⊕J)) (S : Selection T)
    (t : TreeCell T) (a : I×J) : ℝ :=
  indicator (treeCut T S t (.inl a.1))-indicator (treeCut T S t (.inr a.2))

lemma sign_abs_self (T : SimpleGraph (I⊕J)) (S : Selection T) (hT : T.IsAcyclic)
    (t : TreeCell T) : |sign T S t t.val|=1 :=
  abs_indicator_sub (treeCut_self T S hT t)

lemma sign_self_ne_zero (T : SimpleGraph (I⊕J)) (S : Selection T) (hT : T.IsAcyclic)
    (t : TreeCell T) : sign T S t t.val≠0 := by
  intro hz
  have hh := sign_abs_self T S hT t
  rw [hz,abs_zero] at hh
  norm_num at hh

end ContingencyTables.RootedCut

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedAffine
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cut coefficients for an explicitly selected forest root

The same signed cut calculation applies to the executed root selector.
In particular, coefficient size and the maximum-forest capacity bound
do not depend on a classical choice of cut representative.
-/

namespace ContingencyTables.RootedAffine

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedCut GraphCompletionCounts
open ForestCapacity ForestCut MaximumForest

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def coefficient (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) : ℝ :=
  if A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)
  then -sign A.T S t a/sign A.T S t t.val else 0

noncomputable def smallContribution (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q : I → J → ℝ) : ℝ :=
  ∑ a : I×J,if A.small a.1 a.2 then
    indicator (treeCut A.T S t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
      indicator (treeCut A.T S t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2) else 0

noncomputable def offset (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q : I → J → ℝ) : ℝ :=
  A.X t.val.1 t.val.2-smallContribution A S t x q/sign A.T S t t.val-
    ∑ a : I×J,coefficient A S t a*(A.X a.1 a.2:ℝ)

noncomputable def affineTree (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q : I → J → ℝ) (z : I×J → ℝ) : ℝ :=
  AffinePenalty.affineValue (offset A S t x q) (coefficient A S t) z

end ContingencyTables.RootedAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhysicalCompletion
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal residual completion for the executed root convention

The row and column small views remain distinct. The explicit selected
roots determine which incidence equations are enforced; the resulting
integral completion is exactly the selected-cut affine formula.
-/

namespace ContingencyTables.RootedPhysicalCompletion

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedAffine GraphCompletionCounts ForestCut
open ForestPhysicalCompletion

variable {I J : Type*} [Fintype I] [Fintype J]

lemma solved_supported (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (i : I) (j : J) (h : ¬A.T.Adj (.inl i) (.inr j)) :
    solved A S x q free i j=0 := table_supported A.T S _ _ i j h

lemma row_pointwise (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (i : I) (j : J) :
    (if A.small i j then x i j else completed A S x q free i j)=
      solved A S x q free i j+fixedRow A.small A.T x free i j := by
  by_cases ht : A.T.Adj (.inl i) (.inr j)
  · have hs : A.small i j=false := A.hTG ht
    simp only [hs,Bool.false_eq_true,ite_false,completed,ht,ite_true, if_true,fixedRow,add_zero]
  · simp only [completed,ht,ite_false,solved_supported A S x q free i j ht,zero_add,fixedRow]

lemma column_pointwise (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (i : I) (j : J) :
    (if A.small i j then q i j else completed A S x q free i j)=
      solved A S x q free i j+fixedColumn A.small A.T q free i j := by
  by_cases ht : A.T.Adj (.inl i) (.inr j)
  · have hs : A.small i j=false := A.hTG ht
    simp only [hs,Bool.false_eq_true,ite_false,completed,ht,ite_true, if_true,fixedColumn,add_zero]
  · simp only [completed,ht,ite_false,solved_supported A S x q free i j ht,zero_add,fixedColumn]

lemma row_completed_sum (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (i : I) (hi : Sum.inl i≠S.root (.inl i)) :
    (∑ j,if A.small i j then x i j else completed A S x q free i j)=A.r i := by
  simp_rw [row_pointwise]
  rw [Finset.sum_add_distrib]
  have he : (∑ j,solved A S x q free i j)=rowResidual A.small A.T A.r x free i :=
    table_row A.small A.T S A.hTG _ _ i hi
  rw [he,rowResidual]
  exact sub_add_cancel _ _

lemma column_completed_sum (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (j : J) (hj : Sum.inr j≠S.root (.inr j)) :
    (∑ i,if A.small i j then q i j else completed A S x q free i j)=A.c j := by
  simp_rw [column_pointwise]
  rw [Finset.sum_add_distrib]
  have he : (∑ i,solved A S x q free i j)=columnResidual A.small A.T A.c q free j :=
    table_column A.small A.T S A.hTG _ _ j hj
  rw [he,columnResidual]
  exact sub_add_cancel _ _

end ContingencyTables.RootedPhysicalCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedIntervals
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual tree intervals for an explicitly selected component root

The maximum-forest cut estimate applies to every reachable root.  Thus
the executed least-root convention retains the same finite tree box,
including for unbalanced retained small-cell views.
-/

namespace ContingencyTables.RootedIntervals

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPhysicalCompletion
open ForestCapacity GraphCompletionCounts ForestCut

variable {I J : Type*} [Fintype I] [Fintype J]

lemma nonroot_of_component (A : Instance I J) (S : Selection A.T)
    (u v : I⊕J) (h : A.T.Reachable (S.root u) v) (hv : v≠S.root u) :
    v≠S.root v := by
  have he : S.root v=S.root u := by
    rw [←S.constant h,S.idempotent]
  simpa only [he] using hv

theorem solved_in_intervals (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ)
    (hsmall : ∀ i j,A.small i j=true →
      (0≤ x i j ∧ x i j≤ A.b i j) ∧ (0≤ q i j ∧ q i j≤ A.b i j))
    (hfree : ∀ i j,A.small i j=false → ¬A.T.Adj (.inl i) (.inr j) →
      0≤ free i j ∧ free i j≤ A.b i j) :
    ∀ i j,A.T.Adj (.inl i) (.inr j) →
      -((10*A.d*A.b i j:ℕ):ℤ)≤ solved A S x q free i j ∧
        solved A S x q free i j≤(10*A.d*A.b i j:ℕ) := by
  intro i₀ j₀ ht
  let root := S.root (.inl i₀)
  have hb := completion_interval A.small A.b A.T A.hTG A.hT A.hmax i₀ j₀ ht root
    (S.reachable (.inl i₀)).symm
    (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ))
    (fun i j => (completed A S x q free i j:ℝ)) (fun i j => (A.X i j:ℝ))
    (A.d:ℝ) A.W (by exact_mod_cast A.hd) (by exact_mod_cast A.hcard) A.hlarge
    (by
      intro i j hs
      exact ⟨A.hsmall i j hs,by exact_mod_cast (hsmall i j hs).1,
        by exact_mod_cast (hsmall i j hs).2⟩)
    (by intro i j; exact_mod_cast A.hX i j)
    (by
      intro i j hs htree
      have hn : ¬A.T.Adj (.inl i) (.inr j) := by
        simpa only [treeCell,decide_eq_false_iff_not] using htree
      simp only [completed,hn,ite_false]
      have hf := hfree i j hs hn
      constructor
      · exact_mod_cast hf.1
      · have hcast : (free i j:ℝ)≤(A.b i j:ℝ) := by exact_mod_cast hf.2
        linarith)
    (by
      intro i hcomp hi
      have hrow := row_completed_sum A S x q free i
        (nonroot_of_component A S (.inl i₀) (.inl i) hcomp hi)
      have hrowR : (∑ j,if A.small i j then (x i j:ℝ) else
          (completed A S x q free i j:ℝ))=(A.r i:ℝ) := by exact_mod_cast hrow
      have hXR : (∑ j,(A.X i j:ℝ))=(A.r i:ℝ) := by exact_mod_cast A.hXr i
      unfold rowDifference
      calc
        _=(∑ j,if A.small i j then (x i j:ℝ) else
          (completed A S x q free i j:ℝ))-(∑ j,(A.X i j:ℝ)) := by
            rw [←Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> rfl
        _=0 := by rw [hrowR,hXR,sub_self])
    (by
      intro j hcomp hj
      have hcol := column_completed_sum A S x q free j
        (nonroot_of_component A S (.inl i₀) (.inr j) hcomp hj)
      have hcolR : (∑ i,if A.small i j then (q i j:ℝ) else
          (completed A S x q free i j:ℝ))=(A.c j:ℝ) := by exact_mod_cast hcol
      have hXC : (∑ i,(A.X i j:ℝ))=(A.c j:ℝ) := by exact_mod_cast A.hXc j
      unfold columnDifference
      calc
        _=(∑ i,if A.small i j then (q i j:ℝ) else
          (completed A S x q free i j:ℝ))-(∑ i,(A.X i j:ℝ)) := by
            rw [←Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i _
            split_ifs <;> rfl
        _=0 := by rw [hcolR,hXC,sub_self])
  simp only [completed,ht,ite_true, if_true] at hb
  constructor
  · have hlow : (-10:ℤ)*(A.d:ℤ)*(A.b i₀ j₀:ℤ)≤ solved A S x q free i₀ j₀ := by
      exact_mod_cast hb.1
    convert hlow using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  · exact_mod_cast hb.2

end ContingencyTables.RootedIntervals

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical factors with the executed component-root convention

The line factors use the explicitly selected roots. Their tree factors,
widths and doubled row/column coordinates are exactly the source data.
-/

namespace ContingencyTables.RootedPenalty

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS CompanionFactorialApplication RootedCompletion
open ForestPenaltyApplication ForestLiteralCount EqualitySoftening
open ProductIntegerSignature RowColumnPenalties

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def ell (A : Instance I J) : I → J → ℤ := lower A.T A.d A.b
noncomputable def widths (A : Instance I J) : I → J → ℕ := width A.T A.d A.b

noncomputable def rootPenalty (A : Instance I J) (S : Selection A.T)
    (z : ((I×J)×Bool) → ℕ) : ℝ :=
  ∑ g,if rootFlag S g then |deviation (ell A) (widths A) A.r A.c z g| else 0

noncomputable def penalty (A : Instance I J) (S : Selection A.T)
    (z : ((I×J)×Bool) → ℕ) : ℝ :=
  rootPenalty A S z+treePenalty A.T A.b (ell A) z

lemma line_product_eq (A : Instance I J) (S : Selection A.T) (alpha : ℝ)
    (z : ((I×J)×Bool) → ℕ)
    (h : ∀ g,rootFlag S g=false → deviation (ell A) (widths A) A.r A.c z g=0) :
    (∏ g,exactLineFactor (rootFlag S) (fun _ => alpha)
      (lineOffset (ell A) (widths A) A.r A.c) viewSlope g (lineTotal cellLine z g))=
      (2:ℝ)^(-alpha*rootPenalty A S z) := by
  have hp : ∀ g,exactLineFactor (rootFlag S) (fun _ => alpha)
      (lineOffset (ell A) (widths A) A.r A.c) viewSlope g (lineTotal cellLine z g)=
      (2:ℝ)^(-alpha*(if rootFlag S g then
        |deviation (ell A) (widths A) A.r A.c z g| else 0)) := by
    intro g
    simp only [exactLineFactor,ScalarPenalty.factor,line_affine]
    cases hg : rootFlag S g
    · simp [h g hg]
    · simp
  simp_rw [hp]
  rw [←Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)]
  congr 1
  simp only [rootPenalty,Finset.mul_sum]

lemma unary_product_eq (A : Instance I J) (alpha : ℝ)
    (z : ((I×J)×Bool) → ℕ) :
    (∏ a,unaryFactor (unaryRate A.T A.b alpha) (unaryEll (ell A)) unarySlope
      (unaryCap A.b) a (z a))=(2:ℝ)^(-alpha*treePenalty A.T A.b (ell A) z) := by
  unfold unaryFactor ScalarPenalty.factor
  rw [←Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [unaryRate,unaryEll,unarySlope,unaryCap,Fintype.sum_bool,Bool.true_eq_false,
    false_and,ite_false,zero_mul,neg_zero,zero_add,true_and]
  rw [Fintype.sum_prod_type]
  simp only [treePenalty,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [div_eq_mul_inv,mul_zero] <;> ring

end ContingencyTables.RootedPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedLiteralCount
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplicity-one physical tree sum with the executed root convention -/

namespace ContingencyTables.RootedLiteralCount

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPhysicalCompletion
open RootedPenalty ForestLiteralCount GraphCompletionCounts
open ForestPhysicalCompletion (rowResidual columnResidual)

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def actualPenalty (A : Instance I J) (S : Selection A.T)
    (x y free : I → J → ℕ) (tree : I → J → ℤ) : ℝ :=
  (∑ v,if rootFlag S v then
    |actualDeviation A.small A.T A.b x y free A.r A.c tree v| else 0)+
  ∑ i,∑ j,if A.T.Adj (.inl i) (.inr j) then
    max 0 (max (-(tree i j:ℝ)) ((tree i j:ℝ)-A.b i j))/(A.b i j:ℝ) else 0

def RootConditions (A : Instance I J) (S : Selection A.T)
    (x q free tree : I → J → ℤ) : Prop :=
  (∀ i,Sum.inl i≠S.root (.inl i) →
    (∑ j,tree i j)=rowResidual A.small A.T A.r x free i) ∧
  (∀ j,Sum.inr j≠S.root (.inr j) →
    (∑ i,tree i j)=columnResidual A.small A.T A.c q free j)

lemma penalty_profile (A : Instance I J) (S : Selection A.T)
    (x y free : I → J → ℕ) (a : TreeIndex A.T A.d A.b)
    (hy : ∀ i j,A.small i j=true → y i j≤ A.b i j)
    (hf : ∀ i j,A.small i j=false → ¬A.T.Adj (.inl i) (.inr j) → free i j≤ A.b i j) :
    penalty A S (profile A.small A.T A.d A.b x y free a)=
      actualPenalty A S x y free (physical A.T A.d A.b a) := by
  unfold penalty rootPenalty actualPenalty
  rw [show ForestPenaltyApplication.deviation (ell A) (widths A) A.r A.c
      (profile A.small A.T A.d A.b x y free a)=
      actualDeviation A.small A.T A.b x y free A.r A.c (physical A.T A.d A.b a) from
    deviation_profile A.small A.T A.hTG A.d A.b x y free a A.r A.c hy hf]
  congr 1
  unfold ForestPenaltyApplication.treePenalty
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases ht : A.T.Adj (.inl i) (.inr j)
  · have hs : A.small i j=false := A.hTG ht
    have hrow := row_profile A.small A.T A.hTG A.d A.b x y free a i j
    simp only [hs,Bool.false_eq_true,ite_false,largeValue,ht,ite_true, if_true] at hrow
    simp only [ht,ite_true, if_true,EqualitySoftening.affineDistance,mul_one]
    rw [show (ell A i j:ℝ)+(profile A.small A.T A.d A.b x y free a ((i,j),false):ℝ)=
      (physical A.T A.d A.b a i j:ℝ) from hrow]
  · simp only [ht,ite_false]

lemma nonroot_iff (A : Instance I J) (S : Selection A.T)
    (x y free : I → J → ℕ) (tree : I → J → ℤ)
    (hsupport : ∀ i j,¬A.T.Adj (.inl i) (.inr j) → tree i j=0) :
    (∀ g,rootFlag S g=false →
      actualDeviation A.small A.T A.b x y free A.r A.c tree g=0) ↔
    RootConditions A S (fun i j => (x i j:ℤ))
      (fun i j => ((A.b i j-y i j:ℕ):ℤ)) (fun i j => (free i j:ℤ)) tree := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hflag : rootFlag S (.inl i)=false := by
        simpa only [rootFlag,decide_eq_false_iff_not] using hi
      have hraw := h (.inl i) hflag
      simp only [actualDeviation,Sum.elim_inl] at hraw
      have hsum : (∑ j,if A.small i j then (x i j:ℤ) else largeValue A.T tree free i j)=A.r i :=
        by exact_mod_cast sub_eq_zero.mp hraw
      simp_rw [ForestLiteralCount.row_pointwise A.small A.T A.hTG x free tree hsupport] at hsum
      rw [Finset.sum_add_distrib] at hsum
      unfold rowResidual
      omega
    · intro j hj
      have hflag : rootFlag S (.inr j)=false := by
        simpa only [rootFlag,decide_eq_false_iff_not] using hj
      have hraw := h (.inr j) hflag
      simp only [actualDeviation,Sum.elim_inr] at hraw
      have hsum : (∑ i,if A.small i j then ((A.b i j-y i j:ℕ):ℤ)
          else largeValue A.T tree free i j)=A.c j := by exact_mod_cast sub_eq_zero.mp hraw
      simp_rw [ForestLiteralCount.column_pointwise A.small A.T A.hTG A.b y free tree hsupport] at hsum
      rw [Finset.sum_add_distrib] at hsum
      unfold columnResidual
      omega
  · intro h g hg
    cases g with
    | inl i =>
      have hi : Sum.inl i≠S.root (.inl i) := by
        simpa only [rootFlag,decide_eq_false_iff_not] using hg
      have hsum : (∑ j,if A.small i j then (x i j:ℤ) else largeValue A.T tree free i j)=A.r i := by
        simp_rw [ForestLiteralCount.row_pointwise A.small A.T A.hTG x free tree hsupport]
        rw [Finset.sum_add_distrib,h.1 i hi]
        exact sub_add_cancel _ _
      simp only [actualDeviation,Sum.elim_inl]
      have hreal : (((∑ j,if A.small i j then (x i j:ℤ)
        else largeValue A.T tree free i j):ℤ):ℝ)=(A.r i:ℝ) := by exact_mod_cast hsum
      rw [hreal,sub_self]
    | inr j =>
      have hj : Sum.inr j≠S.root (.inr j) := by
        simpa only [rootFlag,decide_eq_false_iff_not] using hg
      have hsum : (∑ i,if A.small i j then ((A.b i j-y i j:ℕ):ℤ)
          else largeValue A.T tree free i j)=A.c j := by
        simp_rw [ForestLiteralCount.column_pointwise A.small A.T A.hTG A.b y free tree hsupport]
        rw [Finset.sum_add_distrib,h.2 j hj]
        exact sub_add_cancel _ _
      simp only [actualDeviation,Sum.elim_inr]
      have hreal : (((∑ i,if A.small i j then ((A.b i j-y i j:ℕ):ℤ)
        else largeValue A.T tree free i j):ℤ):ℝ)=(A.c j:ℝ) := by exact_mod_cast hsum
      rw [hreal,sub_self]

noncomputable def solutionIndex (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ)
    (hbox : ∀ i j,A.T.Adj (.inl i) (.inr j) →
      -((10*A.d*A.b i j:ℕ):ℤ)≤ solved A S x q free i j ∧
        solved A S x q free i j≤(10*A.d*A.b i j:ℕ)) : TreeIndex A.T A.d A.b := fun e =>
  ⟨(solved A S x q free e.val.1 e.val.2+(10*A.d*A.b e.val.1 e.val.2:ℕ)).toNat,by
    have h := hbox e.val.1 e.val.2 e.property
    have hz : 0≤ solved A S x q free e.val.1 e.val.2+(10*A.d*A.b e.val.1 e.val.2:ℕ) := by omega
    have hle : (solved A S x q free e.val.1 e.val.2+
        (10*A.d*A.b e.val.1 e.val.2:ℕ)).toNat≤20*A.d*A.b e.val.1 e.val.2 := by
      exact_mod_cast (show ((solved A S x q free e.val.1 e.val.2+
        (10*A.d*A.b e.val.1 e.val.2:ℕ)).toNat:ℤ)≤(20*A.d*A.b e.val.1 e.val.2:ℕ) by
          rw [Int.toNat_of_nonneg hz]
          push_cast at h ⊢
          nlinarith)
    omega⟩

lemma physical_solutionIndex (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ)
    (hbox : ∀ i j,A.T.Adj (.inl i) (.inr j) →
      -((10*A.d*A.b i j:ℕ):ℤ)≤ solved A S x q free i j ∧
        solved A S x q free i j≤(10*A.d*A.b i j:ℕ)) :
    physical A.T A.d A.b (solutionIndex A S x q free hbox)=solved A S x q free := by
  funext i j
  by_cases h : A.T.Adj (.inl i) (.inr j)
  · have hz : 0≤ solved A S x q free i j+(10*A.d*A.b i j:ℕ) := by
      have hb := hbox i j h
      omega
    simp only [physical,h,dite_eq_left,solutionIndex,Int.toNat_of_nonneg hz]
    omega
  · simp only [physical,h,not_false_eq_true,dite_eq_right,
      solved_supported A S x q free i j h]

theorem tree_indicator_sum (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ)
    (hsmall : ∀ i j,A.small i j=true →
      (0≤ x i j ∧ x i j≤ A.b i j) ∧ (0≤ q i j ∧ q i j≤ A.b i j))
    (hfree : ∀ i j,A.small i j=false → ¬A.T.Adj (.inl i) (.inr j) →
      0≤ free i j ∧ free i j≤ A.b i j)
    (weight : (I → J → ℤ) → ℝ) :
    (∑ a : TreeIndex A.T A.d A.b,if RootConditions A S x q free (physical A.T A.d A.b a)
      then weight (physical A.T A.d A.b a) else 0)=weight (solved A S x q free) := by
  let hb := RootedIntervals.solved_in_intervals A S x q free hsmall hfree
  let a₀ := solutionIndex A S x q free hb
  have ha₀ : physical A.T A.d A.b a₀=solved A S x q free := physical_solutionIndex A S x q free hb
  have hsol : RootConditions A S x q free (solved A S x q free) :=
    ⟨table_row A.small A.T S A.hTG _ _,table_column A.small A.T S A.hTG _ _⟩
  rw [Finset.sum_eq_single a₀]
  · simp only [ha₀,hsol,ite_true, if_true]
  · intro a _ hne
    by_cases ha : RootConditions A S x q free (physical A.T A.d A.b a)
    · have he := table_unique A.small A.T S A.hTG A.hT _ _ (physical A.T A.d A.b a)
        (physical_supported A.T A.d A.b a) ha.1 ha.2
      have haa : a=a₀ := physical_injective A.T A.d A.b (he.trans ha₀.symm)
      exact (hne haa).elim
    · simp only [ha,ite_false]
  · simp

end ContingencyTables.RootedLiteralCount

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRootPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root discrepancy is independent of the free entries

Every large-cell edge stays in a maximum-forest component.  Its two
incidences therefore cancel in the selected-root component sum.
-/

namespace ContingencyTables.RootedRootPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPhysicalCompletion
open ForestPhysicalCompletion (rowResidual columnResidual fixedRow fixedColumn)
open ForestRootPenalty (residualDemand smallDemand)

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def componentTotal (A : Instance I J) (S : Selection A.T)
    (d : I⊕J → ℤ) (a : I⊕J) : ℤ :=
  ∑ v,(if S.root v=a then 1 else 0)*d v

end ContingencyTables.RootedRootPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComponentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial signed component sums for the executed root labels -/

namespace ContingencyTables.RootedComponentProgram

open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators Classical

def records {n : ℕ} (root : Fin n → Fin n) (p q : Fin n → ℕ) : List Record :=
  List.ofFn (fun i => ((root i).val,(p i,q i)))

end ContingencyTables.RootedComponentProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedScaledPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convexity and the physical scaled Lipschitz bound for selected roots -/

namespace ContingencyTables.RootedScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open RootedAffine RootedRootPenalty
open ForestScaledPenalty (intervalCost intervalCost_nonnegative free_card_le )

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def normalizedOffset (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q : I → J → ℤ) : ℝ :=
  offset A S t (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ))/(A.b t.val.1 t.val.2:ℝ)

noncomputable def normalizedCoefficient (A : Instance I J) (S : Selection A.T)
    (B : ℝ) (t : TreeCell A.T) (f : FreeCell A.small A.T) : ℝ :=
  coefficient A S t f.val*((A.b f.val.1 f.val.2:ℝ)+1)/B/(A.b t.val.1 t.val.2:ℝ)

noncomputable def scaledTree (A : Instance I J) (S : Selection A.T)
    (B : ℝ) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℝ) (t : TreeCell A.T) : ℝ :=
  AffinePenalty.affineValue (normalizedOffset A S t x q) (normalizedCoefficient A S B t) v

noncomputable def rootConstant (A : Instance I J) (S : Selection A.T)
    (x q : I → J → ℤ) : ℝ :=
  ∑ a,if RootedPenalty.rootFlag S a then |(signedResidual A S x q 0 a:ℝ)| else 0

noncomputable def penalty (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℝ) : ℝ :=
  C*(rootConstant A S x q+∑ t : TreeCell A.T,intervalCost (scaledTree A S B x q v t))

lemma penalty_nonnegative (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hC : 0≤ C) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℝ) :
    0≤ penalty A S C B x q v := by
  unfold penalty rootConstant
  apply mul_nonneg hC
  apply add_nonneg
  · exact Finset.sum_nonneg (fun a _ => by split_ifs <;> positivity)
  · exact Finset.sum_nonneg (fun t _ => intervalCost_nonnegative _)

end ContingencyTables.RootedScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedIntegerEvaluation
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral coefficients of the executed selected-root affine penalty -/

namespace ContingencyTables.RootedIntegerEvaluation

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit

variable {I J : Type*} [Fintype I] [Fintype J]

lemma sign_real (A : Instance I J) (S : Selection A.T) (t : TreeCell A.T) (a : I×J) :
    (sign A S t a:ℝ)=RootedCut.sign A.T S t a := by
  cases hr : RootedCut.treeCut A.T S t (.inl a.1) <;>
    cases hc : RootedCut.treeCut A.T S t (.inr a.2) <;>
    norm_num [sign,integerIndicator,RootedCut.sign,ForestCut.indicator,hr,hc]

lemma selfSign_square (A : Instance I J) (S : Selection A.T) (t : TreeCell A.T) :
    (RootedCut.sign A.T S t t.val)^2=1 := by
  have hn := RootedCut.treeCut_self A.T S A.hT t
  cases hr : RootedCut.treeCut A.T S t (.inl t.val.1) <;>
    cases hc : RootedCut.treeCut A.T S t (.inr t.val.2) <;>
    simp_all [RootedCut.sign,ForestCut.indicator]

lemma coefficient_real (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) :
    (coefficient A S t a:ℝ)=RootedAffine.coefficient A S t a := by
  have hs := selfSign_square A S t
  have hn := RootedCut.sign_self_ne_zero A.T S A.hT t
  unfold coefficient RootedAffine.coefficient
  split_ifs
  · simp only [Int.cast_mul,Int.cast_neg,sign_real]
    apply (eq_div_iff hn).mpr
    calc
      (-(RootedCut.sign A.T S t a)*RootedCut.sign A.T S t t.val)*RootedCut.sign A.T S t t.val=
          -(RootedCut.sign A.T S t a)*(RootedCut.sign A.T S t t.val)^2 := by ring
      _=_ := by rw [hs,mul_one]
  · exact Int.cast_zero

lemma smallContribution_real (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q : I → J → ℤ) :
    (smallContribution A S t x q:ℝ)=RootedAffine.smallContribution A S t
      (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ)) := by
  unfold smallContribution RootedAffine.smallContribution
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · cases hr : RootedCut.treeCut A.T S t (.inl a.1) <;>
      cases hc : RootedCut.treeCut A.T S t (.inr a.2) <;>
      simp_all [integerIndicator,ForestCut.indicator]
  · exact Int.cast_zero

lemma offset_real (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q : I → J → ℤ) :
    (offset A S t x q:ℝ)=RootedAffine.offset A S t
      (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ)) := by
  have hs := selfSign_square A S t
  have hn := RootedCut.sign_self_ne_zero A.T S A.hT t
  have he : RootedAffine.smallContribution A S t (fun i j => (x i j:ℝ))
      (fun i j => (q i j:ℝ))*RootedCut.sign A.T S t t.val=
      RootedAffine.smallContribution A S t (fun i j => (x i j:ℝ))
        (fun i j => (q i j:ℝ))/RootedCut.sign A.T S t t.val := by
    apply (eq_div_iff hn).mpr
    rw [mul_assoc,←pow_two,hs,mul_one]
  simp only [offset,RootedAffine.offset,Int.cast_sub,Int.cast_mul,Int.cast_sum,
    smallContribution_real,sign_real,coefficient_real,he]

lemma rationalScaledTree_cast (A : Instance I J) (S : Selection A.T)
    (B : ℕ) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℚ) (t : TreeCell A.T) :
    (rationalScaledTree A S B x q v t:ℝ)=
      RootedScaledPenalty.scaledTree A S (B:ℝ) x q (fun f => (v f:ℝ)) t := by
  simp only [rationalScaledTree,RootedScaledPenalty.scaledTree,AffinePenalty.affineValue,
    RootedScaledPenalty.normalizedOffset,RootedScaledPenalty.normalizedCoefficient,
    Rat.cast_add,Rat.cast_div,Rat.cast_mul,Rat.cast_sum,Rat.cast_natCast,Rat.cast_one,
    Rat.cast_intCast,offset_real,coefficient_real]

noncomputable def numerator (A : Instance I J) (S : Selection A.T)
    (B : ℕ) (t : TreeCell A.T) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℕ) : ℤ :=
  (B:ℤ)*offset A S t x q+
    ∑ f : FreeCell A.small A.T,
      coefficient A S t f.val*((A.b f.val.1 f.val.2:ℤ)+1)*(v f:ℤ)

noncomputable def forestData (A : Instance I J) (S : Selection A.T)
    (B : ℕ) (t : TreeCell A.T) (x y : I → J → ℤ)
    {n : ℕ} (e : Fin n ≃ FreeCell A.small A.T) (v : FreeCell A.small A.T → ℕ) :
    ForestAffineProgram.Input :=
  ForestAffineProgram.data ((B:ℤ)*offset A S t x y)
    (fun i => coefficient A S t (e i).val*((A.b (e i).val.1 (e i).val.2:ℤ)+1))
    (fun i => v (e i)) (B*A.b t.val.1 t.val.2)

end ContingencyTables.RootedIntegerEvaluation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPenaltyProgram
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact binary penalty evaluation for the selected-root forest

The signed affine and fraction programs compute the root-specific
geometric penalty from its explicit input metadata.
-/

namespace ContingencyTables.RootedPenaltyProgram

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open MatchingFPRAS RootedIntegerEvaluation

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rootCount_cast (A : Instance I J) (S : Selection A.T) (x q : I → J → ℤ) :
    (rootCount A S x q:ℝ)=RootedScaledPenalty.rootConstant A S x q := by
  unfold rootCount RootedScaledPenalty.rootConstant
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  · exact Nat.cast_zero

theorem rationalPenalty_cast (A : Instance I J) (S : Selection A.T)
    (C : ℕ) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℚ) :
    (rationalPenalty A S C x q v:ℝ)=RootedScaledPenalty.penalty A S C
      (CompanionOracleDensity.binWidth A C) x q (fun f => (v f:ℝ)) := by
  simp only [rationalPenalty,RootedScaledPenalty.penalty,ForestScaledPenalty.intervalCost,
    Rat.cast_mul,Rat.cast_natCast,Rat.cast_add,Rat.cast_sum,Rat.cast_max,Rat.cast_zero,
    Rat.cast_neg,Rat.cast_sub,Rat.cast_one,rootCount_cast,rationalScaledTree_cast,
    CompanionOracleDensity.rationalBinWidth_cast]

noncomputable def data (A : Instance I J) (S : Selection A.T) (C : ℕ)
    (x q : I → J → ℤ) {nt nf : ℕ}
    (trees : Fin nt ≃ TreeCell A.T) (free : Fin nf ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) : ForestPenaltyProgram.Input :=
  ((C,rootCount A S x q),List.ofFn (fun i =>
    forestData A S (CompanionOracleDensity.rationalBinWidth A C) (trees i) x q free v))

end ContingencyTables.RootedPenaltyProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCoefficientProgram
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing signed affine coefficients from the actual forest graph

The tree and cell endpoints are ordinary vertex indices. The program
computes the canonical cut flags, tests the capacity threshold and tree
adjacency, and returns the normalized signed coefficient.
-/

namespace ContingencyTables.RootedCoefficientProgram

open MatchingFPRAS.TreeTyped
open SignedPairProgram FiniteGraphRootProgram FiniteGraphCutProgram
open scoped Classical

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation

noncomputable def input {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (a : Fin m×Fin n) : Input :=
  (((graphCode (A.T.comap finSumFinEquiv.symm),
      ((finSumFinEquiv (m := m) (n := n) (.inl t.val.1)).val,(finSumFinEquiv (m := m) (n := n) (.inr t.val.2)).val)),
      ((finSumFinEquiv (m := m) (n := n) (.inl a.1)).val,(finSumFinEquiv (m := m) (n := n) (.inr a.2)).val)),
    (A.W,A.b a.1 a.2))

end ContingencyTables.RootedCoefficientProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCellDataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Assembling the affine input from ordinary rectangular cell arrays

The baseline and both stored views are binary natural matrices. The
program reads each cell once, computes its row/column vertex indices,
and constructs the offset evaluator input in row-major order.
-/

namespace ContingencyTables.RootedCellDataProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open FiniteGraphRootProgram FiniteGraphCutProgram
open scoped Classical

open CompanionFactorialApplication RootedCompletion

noncomputable def data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ) : Input :=
  ((((graphCode (A.T.comap finSumFinEquiv.symm),
      ((finSumFinEquiv (m := m) (n := n) (.inl t.val.1)).val,
        (finSumFinEquiv (m := m) (n := n) (.inr t.val.2)).val)),A.W),
    (List.ofFn (fun i => (A.r i).toNat),List.ofFn (fun j => (A.c j).toNat))),
    ((matrixCode A.b,matrixCode (fun i j => (A.X i j).toNat)),(matrixCode x,matrixCode q)))

end ContingencyTables.RootedCellDataProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedDemandProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the root-demand input from the actual cell arrays

The two natural entries at a vertex encode its signed small-cell
discrepancy. They are formed by rectangular scans and then passed to the
component/root program.
-/

namespace ContingencyTables.RootedDemandProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms SignedPairProgram
open FiniteGraphRootProgram
open scoped BigOperators Classical

open CompanionFactorialApplication RootedCompletion

noncomputable def contribution {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : Fin m⊕Fin n) (a : Fin m×Fin n) : ℤ :=
  if A.small a.1 a.2 then
    (if v=Sum.inl a.1 then A.X a.1 a.2-(x a.1 a.2:ℤ) else 0)+
      (if v=Sum.inr a.2 then (q a.1 a.2:ℤ)-A.X a.1 a.2 else 0)
  else 0

end ContingencyTables.RootedDemandProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedLargeMarginal
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual balanced large-cell marginal for the explicit root selector

The raw removal and reflected signatures are derived from the physical
line/unary factors. No signature of the marginal is postulated.
-/

namespace ContingencyTables.RootedLargeMarginal

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPenalty
open LargePairEnumeration BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

lemma large_width (A : Instance I J) {n : ℕ}
    (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2)) (k : Fin n) :
    2≤ RootedPenalty.widths A (e k).val.1 (e k).val.2 := by
  have hb := (A.hlarge _ _ (e k).property).2
  by_cases ht : A.T.Adj (.inl (e k).val.1) (.inr (e k).val.2)
  · simp only [RootedPenalty.widths,ForestLiteralCount.width,ht,ite_true, if_true]
    have hd := A.hd
    have hp : 0<A.d*A.b (e k).val.1 (e k).val.2 := Nat.mul_pos (by omega) (by omega)
    nlinarith
  · simp only [RootedPenalty.widths,ForestLiteralCount.width,ht,ite_false]
    exact A.hW.trans (A.hlarge _ _ (e k).property).1

end ContingencyTables.RootedLargeMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPenaltyEvaluateProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for the actual forest exponent

The bin width and height are computed from the dimension allowance,
capacity scale and phase coefficient. All forest metadata is generated
from the cell arrays by `RootedForestPrepareProgram`.
-/

namespace ContingencyTables.RootedPenaltyEvaluateProgram

open MatchingFPRAS.TreeTyped
open scoped Classical

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

lemma height_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (C a : ℕ) :
    height ((A.d,A.W),(C,a))=CompanionOracleDensity.rationalHeight A C := by
  simp only [height,baseHeight,scaledSquare,squareDimension,
    CompanionOracleDensity.rationalHeight,pow_two]
  ring

end ContingencyTables.RootedPenaltyEvaluateProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBinFramesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the actual bin draws from the computed free-cell catalog

Only the capacity matrix, catalog metadata, grid coordinate list and
numeric sampling parameters are supplied. The program computes each
full range and bin index before invoking the proved vector draw.
-/

namespace ContingencyTables.RootedBinFramesProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators Classical

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary

noncomputable section
variable {m n K : ℕ}

def data (A : Instance (Fin m) (Fin n)) (h : ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : Input :=
  ((K,(h,A.d)),(RootedForestCatalog.data A,gridNatCode v))

end
end ContingencyTables.RootedBinFramesProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBinDrawLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed bin program has the analysed independent law

The execution order is the computed free-cell catalog.  The mathematical
law uses another enumeration.  Dependent word equivalences identify their
independent Boolean inputs, while preserving each physical cell's draw.
-/

namespace ContingencyTables.RootedBinDrawLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FirstSuccess ResidualMixture FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

local instance freeCellDecidableEq (A : Instance (Fin m) (Fin n)) :
    DecidableEq (FreeCell A.small A.T) := by
  letI : DecidableEq (Fin m) := Classical.decEq _
  letI : DecidableEq (Fin n) := Classical.decEq _
  infer_instance

abbrev FreeWords (A : Instance (Fin m) (Fin n)) (h : ℕ) :=
  (t : FreeCell A.small A.T) → Fin (offsetBitLength (freeRange A t) h A.d) → Bool

def originalWordEquiv (A : Instance (Fin m) (Fin n)) (h : ℕ) :
    BinWords A h ≃ FreeWords A h :=
  Equiv.piCongrLeft (fun t : FreeCell A.small A.T =>
    Fin (offsetBitLength (freeRange A t) h A.d) → Bool) (index A)

end
end ContingencyTables.RootedBinDrawLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSampleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact law of the executed correction sample

The two coordinate enumerations need not agree on a fixed bit string.
Their independent finite-word laws agree, which preserves every real
observable of the computed rational sample.
-/

namespace ContingencyTables.RootedCorrectionSampleLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity ResidualMixture FirstSuccess FairBits
open CommonBasesFPRAS FiniteLawMoments
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

local instance freeCellDecidableEq (A : Instance (Fin m) (Fin n)) :
    DecidableEq (FreeCell A.small A.T) := by
  letI : DecidableEq (Fin m) := Classical.decEq _
  letI : DecidableEq (Fin n) := Classical.decEq _
  infer_instance

end
end ContingencyTables.RootedCorrectionSampleLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComputedEstimator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed blocks have the complete estimator law

Only the physical sample programs differ from the original enumeration.
Exact independent-observable transport identifies their whole product
estimator, including every event used by the confidence proof.
-/

namespace ContingencyTables.RootedComputedEstimator

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FirstSuccess ResidualMixture FiniteObservableTransport
open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

abbrev RatioWords (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ) :=
  Fin (sampleCount j delta failure) →
    (Fin (oracleTime A C K 1 delta*oracleStepBits A C) → Bool)

end
end ContingencyTables.RootedComputedEstimator

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_TreeMarginalSignature
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual one-tree physical marginal before the equality limit

One physical cell is retained as its doubled Boolean pair. Every other
physical cell, including small capacities zero and one, is summed at
balance. The resulting positive scalar sequence has the proved raw
log-concavity and finite interpolation bounds.
-/

namespace ContingencyTables.TreeMarginalSignature

open scoped BigOperators Classical Matrix Topology
open Filter CommonBasesFPRAS CompanionFactorialApplication ForestPenaltyApplication
open LargePairEnumeration BalancedFamily BalancedBox EqualitySoftening IntegerWeightedTransport RowColumnPenalties

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def singleView (t : I×J) : SmallView (keep t) ≃ Bool where
  toFun p := p.2
  invFun b := (⟨t,by simp [keep]⟩,b)
  left_inv p := by
    have hp : p.1.val=t := by simpa only [keep,decide_eq_true_eq] using p.1.property
    rcases p with ⟨⟨a,ha⟩,b⟩
    dsimp only at hp
    subst a
    rfl
  right_inv b := rfl

noncomputable def enumeration (t : I×J) : Fin (Fintype.card (LargeCell (keep t))) ≃ LargeCell (keep t) :=
  (Fintype.equivFin _).symm

noncomputable def otherWidths (A : Instance I J) (t : I×J) :
    Fin (Fintype.card (LargeCell (keep t))) → ℕ := fun k => cellWidth A (enumeration t k).val

noncomputable def coordinateEquiv (A : Instance I J) (t : I×J) :
    Coordinates Bool (widths (otherWidths A t)) ≃ (I×J)×Bool :=
  (LargePairEnumeration.coordinateEquiv Bool (otherWidths A t)).trans
    ((Equiv.sumCongr (singleView t).symm (Equiv.refl _)).trans
      (physicalJoinEquiv (keep t) (enumeration t)))

end ContingencyTables.TreeMarginalSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_TreeMarginalEnumeration
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The physical one-cell marginal is exactly its balanced assignment fibre -/

namespace ContingencyTables.TreeMarginalSignature

open scoped BigOperators Classical
open CompanionFactorialApplication ForestPenaltyApplication LargePairEnumeration
open PhysicalLargeProfiles BalancedFamily BalancedEnumeration BalancedCellFibres
open IntegerWeightedTransport

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def otherCells (t : I×J) : LargeCell (keep t) ≃ {a : I×J // a≠t} where
  toFun a := ⟨a.val,by simpa only [keep,decide_eq_false_iff_not] using a.property⟩
  invFun a := ⟨a.val,by simpa only [keep,decide_eq_false_iff_not] using a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end ContingencyTables.TreeMarginalSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TransversalCount
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact binomial/factorial cancellation in a transversal normalizer

Every small integer profile has a product of binomial numbers of label
preimages. Its factorial lift contributes the inverse product, so the
actual transversal normalizer is exactly the raw integer-profile sum.
-/

namespace ContingencyTables.TransversalCount

open scoped BigOperators Classical
open CommonBasesFPRAS TwoLiftStates LabelledFactorial InitialTransversals InitialLocalChoices

variable {C : Type*} [Fintype C] (b : C → ℕ)

noncomputable def cardProfile (S : (c : C) → Finset (Fin (b c))) : Profile b :=
  fun c => cardAt b c (S c)

noncomputable def display (x : Profile b) : C×Bool → ℕ :=
  fun u => if u.2 then b u.1-(x u.1).val else (x u.1).val

end ContingencyTables.TransversalCount

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedFarMass
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential far-penalty bound for the actual selected-root mass -/

namespace ContingencyTables.RootedFarMass

open scoped BigOperators Classical
open CompanionFactorialApplication TreeMarginalSignature BalancedCellFibres

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def actualPenalty (A : Instance I J) (R : RootedCompletion.Selection A.T) (a : Profiles (cellWidth A)) : ℝ :=
  RootedPenalty.penalty A R (BalancedCellFibres.profile (cellWidth A) a)

end ContingencyTables.RootedFarMass

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RealPathApproximation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping an entire finite history during real-kernel comparison -/

namespace ContingencyTables.RealKernelApproximation
open scoped BigOperators Classical
open CommonBasesFPRAS ResidualMixture FirstSuccess

noncomputable section
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def mapKernel (f : X → Y) : FiniteKernel X Y where
  P x y := if f x=y then 1 else 0
  nonnegative x y := by split_ifs <;> norm_num
  substochastic x := by simp

/-- `a` can contain the entire past. Only `read a` is used for the next
random transition; `put a` retains every coordinate needed afterward. -/
def liftKernel (K : FiniteKernel X Y) (read : A → X) (put : A → Y → B) : FiniteKernel A B where
  P a b := (mapKernel (put a)).push (K.P (read a)) b
  nonnegative a b := (mapKernel (put a)).push_nonneg _ (K.nonnegative (read a)) b
  substochastic a := ((mapKernel (put a)).push_mass_le _ (K.nonnegative (read a))).trans
    (K.substochastic (read a))

def liftRational [DecidableEq B] (Q : X → RationalLaw Y)
    (read : A → X) (put : A → Y → B) (a : A) : RationalLaw B := mapLaw (Q (read a)) (put a)

end
end ContingencyTables.RealKernelApproximation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedHistoryStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional accuracy of each actual adaptive outer phase -/

namespace ContingencyTables.RootedHistoryStep

open CommonBasesFPRAS FirstSuccess FairBits CompanionFactorialApplication
open CompanionRationalUpdates CompanionOracleDensity RootedPhaseHistory RootedStoredHistory
open CompanionPhaseWords (Stored)
open CompanionTraceWords (eventIndicator)
open CompanionTargetMixing (restartTime)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def error (A : Instance I J) (s : Settings A) (eta : ℝ) (j : ℕ) : ℝ :=
  32000*(Fintype.card (Labels A):ℝ)^8*
    ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
      (((s.N+1:ℕ):ℝ)*eta^2)+
    (s.N:ℝ)*((6*(s.xi:ℝ)+1/(2:ℝ)^s.k)/2)+
      2*(1/(2:ℝ)^s.h+(j:ℝ)*((restartTime A s.H s.L:ℝ)*
        ((20*(Fintype.card (Labels A):ℝ)^2)/(s.n:ℝ)+
          ((s.n+1:ℕ):ℝ)*((6*(s.xi:ℝ)+1/(2:ℝ)^s.k)/2))))+
        2*((s.N+1:ℕ):ℝ)*(s.xi:ℝ)

end
end ContingencyTables.RootedHistoryStep

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactIntegerRetry
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact law and geometric tail of integer rejection -/

namespace ContingencyTables.ExactIntegerChoice
open MatchingFPRAS ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section
variable {r Q : ℕ} (w : Fin r → ℕ) (h : 0<totalWeight w) [NeZero Q]
variable (hQ : totalWeight w≤Q)

abbrev trialLaw : RationalLaw (Option (Fin r)) :=
  mapLaw (uniformLaw (α := Fin Q)) (weightedTrial w h hQ)

end
end ContingencyTables.ExactIntegerChoice

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteCorrectionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residual correction of the initialized finite sampler -/

namespace ContingencyTables.FirstSuccess
open ResidualMixture
open scoped BigOperators Classical

lemma variation_point_le {X : Type*} [Fintype X] (p q : RationalLaw X) (x : X) :
    |p.mass x-q.mass x| ≤ variation p q := by
  classical
  have hm : (∑ y,(p.mass y:ℝ))=∑ y,(q.mass y:ℝ) := by
    exact_mod_cast p.total.trans q.total.symm
  have h := RealKernelApproximation.distance_event
    (fun y => (p.mass y:ℝ)) (fun y => (q.mass y:ℝ)) hm {x}
  simp only [Finset.sum_singleton] at h
  have hd : RealKernelApproximation.distance (fun y => (p.mass y:ℝ))
      (fun y => (q.mass y:ℝ))=(variation p q:ℝ) := by
    simp only [RealKernelApproximation.distance,variation,Rat.cast_div,Rat.cast_sum,
      Rat.cast_abs,Rat.cast_sub,Rat.cast_ofNat]
  rw [hd] at h
  exact_mod_cast h

/-- Total variation at most the square of the rare-branch probability
implies the exact pointwise domination required by residual correction. -/
theorem residual_from_variation {X : Type*} [Fintype X] [Nonempty X]
    (p : RationalLaw X) (delta : ℚ) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hcard : (Fintype.card X:ℚ)*delta ≤ 1)
    (herror : variation p (uniformLaw (α := X)) ≤ delta^2) :
    ∃ q : RationalLaw X,∀ x,(1-delta)*p.mass x+delta*q.mass x=uniformMass (α := X) := by
  apply exact_correction p hd hd1 hcard
  intro x
  have h := variation_point_le p (uniformLaw (α := X)) x
  have hu : (uniformLaw (α := X)).mass x=uniformMass (α := X) := rfl
  rw [hu] at h
  linarith [(abs_le.mp (h.trans herror)).2]

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteDeterministicJoint
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint laws with a deterministic second coordinate -/

namespace ContingencyTables.FirstSuccess
open scoped BigOperators Classical
open ResidualMixture

variable {X : Type*} {Y : X → Type*} [Fintype X] [∀ x,Fintype (Y x)]

lemma mapLaw_deterministicJoint (p : RationalLaw X) (f : (x : X) → Y x) :
    mapLaw p (fun x => (⟨x,f x⟩ : Sigma Y))=
      dependentJointLaw p (fun x => pointLaw (f x)) := by
  apply RationalLaw.ext
  funext a
  rcases a with ⟨x,y⟩
  change (∑ z,if (⟨z,f z⟩ : Sigma Y)=⟨x,y⟩ then p.mass z else 0)=
    p.mass x*(if y=f x then 1 else 0)
  rw [Finset.sum_eq_single x]
  · by_cases h : f x=y <;> simp [h,eq_comm]
  · intro z _ hz
    have hn : (⟨z,f z⟩ : Sigma Y)≠⟨x,y⟩ := fun h => hz (congrArg Sigma.fst h)
    simp only [hn,ite_false]
  · simp

lemma pointLaw_eq_uniform {A : Type*} [Fintype A] [Subsingleton A] [Nonempty A] (a : A) :
    pointLaw a=uniformLaw (α := A) := by
  let : Unique A := ⟨⟨a⟩,fun x => Subsingleton.elim x a⟩
  apply RationalLaw.ext
  funext x
  simp only [pointLaw,uniformLaw,uniformMass,Subsingleton.elim a x,ite_true, if_true,
    Fintype.card_unique,Nat.cast_one,div_one]

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteRecordedHistory
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed-capacity recorder stores the chronological word history -/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS FirstSuccess RealKernelApproximation
open CompanionBooleanPhase CompanionPhaseTrajectory

def recorded {X : Type*} {k : ℕ} (F : X → (Fin k → Bool) → X) (N : ℕ) (c : X)
    (n : ℕ) (words : Fin n → Fin k → Bool) : PathState X N :=
  wordWalk (fun a bits => pathPut a (F (pathRead a) bits)) (pathInitial N c) n words

end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PairedProfileSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed paired counts are the manuscript's literal profile -/

namespace ContingencyTables.PairedProfileSemantics

open PairedProfileProgram CanonicalInitialEncoding InitialTransversals
open CompanionArithmeticProposal CompanionFactorialApplication
open scoped BigOperators Classical

noncomputable section

variable {q : ℕ} (b : Fin q → ℕ)

def cellRows (S : Set (Copy b × Bool)) : List (List ℕ) :=
  List.ofFn (fun i => interleave (List.ofFn (fun k : Fin (b i) =>
    (if (⟨i,k⟩,false) ∈ S then 1 else 0,
     if (⟨i,k⟩,true) ∈ S then 1 else 0))))

end
end ContingencyTables.PairedProfileSemantics

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_TapeTools
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]

def Exec (M : Λ→TM1.Stmt Γ Λ σ) (c d : TM1.Cfg Γ Λ σ) (t : ℕ) : Prop :=
  ∃ k,k≤t ∧ MachineCost.run (TM1.step M) k c=d
end MatchingFPRAS.LiteralTape

end OAI
end


