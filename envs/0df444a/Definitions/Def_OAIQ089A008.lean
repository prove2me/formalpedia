-- Prove2me | Definitions.Def_OAIQ089A008
-- name    : OAIQ089A008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T02:59:19.316346+00:00
-- url     : https://prove2.me/theorems/1adf5684-9739-4afa-85b8-9ca4e9d48971
-- title:
--   Definitions bundle OAIQ089A008 of the split of OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 242 declarations of OpenAI's Lean: 107 definitions and 135 theorems. The definitions and types are `OAI.ContingencyTables.FirstPaperContextTransport.contextSoft`, `OAI.ContingencyTables.FirstPaperPhysicalMarginal.softMarginal`, `OAI.ContingencyTables.FixedCardinalityProgram.sampleWords`, `OAI.ContingencyTables.FlowMatrixBounds.matrixBound`, `OAI.ContingencyTables.GridBoundary.arithmeticExponentAt`, `OAI.ContingencyTables.IndexedTableLaw.index`, `OAI.ContingencyTables.IndexedTableLaw.law`, `OAI.ContingencyTables.IndexedTableLaw.tableAt`, `OAI.ContingencyTables.IntegerResidualCorrection.law`, `OAI.ContingencyTables.MeasuredMap.foldMeasure`, `OAI.ContingencyTables.OnlineIntegerRetry.output`, `OAI.ContingencyTables.OnlineRetryPrefix.At`, `OAI.ContingencyTables.OriginalBoxLaw.law`, `OAI.ContingencyTables.OriginalTableBox.decode`, `OAI.ContingencyTables.OriginalTableBox.encode`, `OAI.ContingencyTables.OriginalTableBox.index`, `OAI.ContingencyTables.OriginalTableBox.tableAt`, `OAI.ContingencyTables.ProfilePrograms.publicWordCount`, `OAI.ContingencyTables.RootedAnnealing.weight`, `OAI.ContingencyTables.RootedBinDrawLaw.Words`, `OAI.ContingencyTables.RootedBinDrawLaw.freeWordEquiv`, `OAI.ContingencyTables.RootedBinDrawLaw.reindexWords`, `OAI.ContingencyTables.RootedBinDrawLaw.wordBits`, `OAI.ContingencyTables.RootedBinDrawLaw.wordEquiv`, `OAI.ContingencyTables.RootedBooleanPhase.referenceChain`, `OAI.ContingencyTables.RootedBooleanPhase.targetChain`, `OAI.ContingencyTables.RootedBooleanPhase.targetPathMass`, `OAI.ContingencyTables.RootedCatalogGrid.naturalValues`, `OAI.ContingencyTables.RootedComputedEstimator.CorrectionWords`, `OAI.ContingencyTables.RootedComputedEstimator.Inputs`, `OAI.ContingencyTables.RootedCorrectionProgram.data`, `OAI.ContingencyTables.RootedCorrectionSampleLaw.Words`, `OAI.ContingencyTables.RootedCorrectionSampleProgram.data`, `OAI.ContingencyTables.RootedCountIdentification.h`, `OAI.ContingencyTables.RootedEstimatorExecution.correctionBlock`, `OAI.ContingencyTables.RootedEstimatorExecution.data`, `OAI.ContingencyTables.RootedEstimatorExecution.ratioBlock`, `OAI.ContingencyTables.RootedEstimatorMedianProgram.value`, `OAI.ContingencyTables.RootedEstimatorWordProgram.Banks`, `OAI.ContingencyTables.RootedEstimatorWordProgram.bankInput` and 67 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `ContingencyTables_Dense_DenseExponentArithmetic`, `ContingencyTables_Machines_FixedCardinalityFold`, `ContingencyTables_Machines_ListWordProgram`, `ContingencyTables_Machines_OnlineIntegerRetry`, `ContingencyTables_Machines_OnlineRetryPrefix`, `ContingencyTables_Parameters`, `ContingencyTables_Rooted_ForestCountIdentification`, `ContingencyTables_Rooted_RootedAnnealing`, `ContingencyTables_Rooted_RootedBinDrawLaw`, `ContingencyTables_Rooted_RootedBinFramesProgram`, `ContingencyTables_Rooted_RootedBooleanKernel`, `ContingencyTables_Rooted_RootedCatalogGrid`, `ContingencyTables_Rooted_RootedComputedEstimator`, `ContingencyTables_Rooted_RootedCorrectionSampleLaw`, `ContingencyTables_Rooted_RootedCorrectionSampleProgram`, `ContingencyTables_Rooted_RootedCorrectionSemantics`, `ContingencyTables_Rooted_RootedCountIdentification`, `ContingencyTables_Rooted_RootedEstimatorExecution`, `ContingencyTables_Rooted_RootedEstimatorLayoutProgram`, `ContingencyTables_Rooted_RootedEstimatorMedianLaw`, `ContingencyTables_Rooted_RootedEstimatorWordLaw`, `ContingencyTables_Rooted_RootedEstimatorWordSemantics`, `ContingencyTables_Rooted_RootedFactorialApplication`, `ContingencyTables_Rooted_RootedFarMass`, `ContingencyTables_Rooted_RootedForestCatalog`, `ContingencyTables_Rooted_RootedForestDataProgram`, `ContingencyTables_Rooted_RootedForestPrepareProgram`, `ContingencyTables_Rooted_RootedLargeMarginal`, `ContingencyTables_Rooted_RootedLiteralCount`, `ContingencyTables_Rooted_RootedMultiplierUpdate`, `ContingencyTables_Rooted_RootedNearMass`, `ContingencyTables_Rooted_RootedOffsetProgram`, `ContingencyTables_Rooted_RootedOracleAcceptance`, `ContingencyTables_Rooted_RootedOracleFlatProgram`, `ContingencyTables_Rooted_RootedOracleStepProgram`, `ContingencyTables_Rooted_RootedPenalty`, `ContingencyTables_Rooted_RootedPenaltyEvaluateProgram`, `ContingencyTables_Rooted_RootedPhaseOracleError`, `ContingencyTables_Rooted_RootedPhaseTrial`, `ContingencyTables_Rooted_RootedPhysicalNormalizer`, `ContingencyTables_Rooted_RootedRestartStages`, `ContingencyTables_Rooted_RootedStoredHistory`, `ContingencyTables_Rooted_RootedTargetMixing`, `ContingencyTables_Rooted_RootedTargetTrace`, `ContingencyTables_Rooted_RootedTraceWords`, `ContingencyTables_Rooted_RootedTreeInputProgram`, `ContingencyTables_Rooted_RootedTreeMarginal`, `ContingencyTables_Rooted_RootedWarmStart`, `ContingencyTables_Sampling_AllSmallChain`, `ContingencyTables_Sampling_AllSmallFibres`, `ContingencyTables_Sampling_FirstPaperContextTransport`, `ContingencyTables_Sampling_FirstPaperPhysicalMarginal`, `ContingencyTables_Sampling_FirstPaperPhysicalVariance`, `ContingencyTables_Sampling_FirstPaperSmallMixing`, `ContingencyTables_Sampling_FirstPaperSuccessRatio`, `ContingencyTables_Sampling_InverseSmallRepair`, `ContingencyTables_Sampling_OriginalBoxLaw`, `ContingencyTables_Sampling_OriginalTableBox`, `ContingencyTables_Sampling_Padding`, `ContingencyTables_Sampling_PhysicalExchangeMargins`, `ContingencyTables_Sampling_PhysicalLargeProfiles`, `ContingencyTables_Sampling_PhysicalMassBound`, `ContingencyTables_Sampling_PhysicalPrefixEnergies`, `ContingencyTables_Sampling_PhysicalResidualMargins`, `ContingencyTables_Sampling_ProfileInverseRepairProgram`, `ContingencyTables_Sampling_ProfilePublicProgram`, `ContingencyTables_Sampling_ProfileRepairProgram`, `ContingencyTables_Sampling_RepairLargeMass`, `ContingencyTables_Sampling_RepairPrefixes`, `ContingencyTables_Sampling_RepairSmallMargins`, `ContingencyTables_Sampling_SmallBoundsProgram`, `ContingencyTables_Sampling_SmallComplementProgram`, `ContingencyTables_Sampling_SmallCoordinateSums`, `ContingencyTables_Sampling_SmallDefectCodeTest`, `ContingencyTables_Sampling_SmallExchangeListProgram`, `ContingencyTables_Sampling_SmallGraphProfiles`, `ContingencyTables_Sampling_SmallLineSumProgram`, `ContingencyTables_Sampling_SmallMarginSemantics`, `ContingencyTables_Sampling_SmallPatternArithmetic`, `ContingencyTables_Sampling_SmallPatternProgram`, `ContingencyTables_Sampling_SmallProfileFlatCode`, `ContingencyTables_Sampling_SmallRepairCodeProgram`, `ContingencyTables_Sampling_SmallResidualTotals`, `ContingencyTables_Sampling_SmallViewLookupProgram`, `ContingencyTables_Sampling_UnitGraphEnergy`, `ContingencyTables_Transport_BooleanIntegerLaw`, `ContingencyTables_Transport_ContextGraphEnergy`, `ContingencyTables_Transport_ContextGraphMembership`, `ContingencyTables_Transport_FiniteExchangeObservables`, `ContingencyTables_Transport_FlowMatrixBounds`, `ContingencyTables_Transport_IndexedTableLaw`, `ContingencyTables_Transport_IntegerContextSlices`, `ContingencyTables_Transport_IntegerEquivLaw`, `ContingencyTables_Transport_IntegerExchangeArithmetic`, `ContingencyTables_Transport_IntegerExposure`, `ContingencyTables_Transport_IntegerLaw`, `ContingencyTables_Transport_IntegerLeafEnergy`, `ContingencyTables_Transport_IntegerRecursivePotential`, `ContingencyTables_Transport_IntegerResidualCorrection`, `ContingencyTables_Transport_IntegerRootTransport`, `ContingencyTables_Transport_IntegerSliceReindex`, `ContingencyTables_Transport_IntegerSliceRestriction`, `ContingencyTables_Transport_LabelledFactorial`, `ContingencyTables_Transport_MeasuredMap`, `ContingencyTables_Transport_NestedPenaltyApplication`, `ContingencyTables_Transport_NestedProductSignature`, `ContingencyTables_Transport_NestedReindex`, `ContingencyTables_Transport_RationalChainCast`, `ContingencyTables_Transport_RationalChainMixing`, `ContingencyTables_Transport_RationalWalkApproximation`, `ContingencyTables_Transport_ReferenceCompletionBlock`, `ContingencyTables_Transport_RowMajorEnumeration`, `ContingencyTables_Transport_RowMajorPrefixFibres`, `ContingencyTables_Transport_SliceFactorial`, `ContingencyTables_Transport_UniformPartialRejection`, `MatchingCount_Complexity_TreeCostMeasure`, `MatchingCount_Complexity_TreePolynomial`, `MatchingCount_Machines_TreeCanonical`, `MatchingCount_Machines_TreeColex`, `MatchingCount_Machines_TreeFinite`, `MatchingCount_Machines_TreeFiniteCollections`, `MatchingCount_Machines_TreeFiniteOps`, `MatchingCount_Machines_TreePostRealization`, `MatchingCount_Tapes_Codec`, `MatchingCount_Tapes_Packed`.
--
--   **Imports.** It imports the published bundle `Def_ContingencyTables`; the bundles `OAIQ089A003`, `OAIQ089A004` and `OAIQ089A005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ089A009` and `OAIQ089A010`; the statements `OAI.ContingencyTables.CompanionObservationQueriesProgram.polynomial_output`, `OAI.ContingencyTables.CompanionObservedUpdateProgram.polynomial_output`, `OAI.ContingencyTables.CompanionPhaseTrialProgram.polynomial_output`, `OAI.ContingencyTables.CompanionRepeatedReturnProgram.polynomial_output`, `OAI.ContingencyTables.RootedEstimatorMedianProgram.polynomial_output`, `OAI.ContingencyTables.RootedObservationStart.observed_failure_near`, `OAI.ContingencyTables.RootedPlainTrial.trial_failure`, `OAI.ContingencyTables.RootedTargetMixing.targetTrace_poincare` and `OAI.ContingencyTables.RootedTraceWords.arithmetic_recorded_event_bound`; the proof of `OAI.ContingencyTables.CompanionObservationQueriesProgram.polynomial_output`.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A003
import Definitions.Def_OAIQ089A004
import Definitions.Def_OAIQ089A005

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_Padding
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

/-- Successful enlarged tables are in exact bijection with original tables. -/
def paddingEquiv (r : I → ℕ) (c : J → ℕ) (P : I → J → ℕ) :
    Table r c ≃ {Y : Table (paddedRows r P) (paddedColumns c P) //
      ∀ i j, P i j ≤ Y.val i j} where
  toFun := fun X => ⟨padTable P X, fun _ _ => Nat.le_add_left _ _⟩
  invFun := fun Y => unpadTable P Y.val Y.property
  left_inv := by
    intro X
    apply Subtype.ext
    funext i j
    exact Nat.add_sub_cancel _ _
  right_inv := by
    intro Y
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    exact Nat.sub_add_cancel (Y.property i j)

theorem successful_card (r : I → ℕ) (c : J → ℕ) (P : I → J → ℕ) :
    Fintype.card {Y : Table (paddedRows r P) (paddedColumns c P) //
      ∀ i j, P i j ≤ Y.val i j} = Fintype.card (Table r c) := by
  classical
  exact (Fintype.card_congr (paddingEquiv r c P)).symm

section SuccessFraction

variable [DecidableEq I] [DecidableEq J]

theorem large_padding_good_card (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (L : ℕ) :
    Fintype.card {Y : Table (paddedRows r (largePadding K L))
        (paddedColumns c (largePadding K L)) //
      ¬∃ p : K, Y.val p.val.1 p.val.2 < L} = Fintype.card (Table r c) := by
  let P := largePadding K L
  let T := Table (paddedRows r P) (paddedColumns c P)
  have heq (Y : T) : (¬∃ p : K, Y.val p.val.1 p.val.2 < L) ↔
      ∀ i j, P i j ≤ Y.val i j := by
    constructor
    · intro hb i j
      by_cases hij : (i, j) ∈ K
      · have hn : ¬Y.val i j < L := fun h => hb ⟨⟨(i, j), hij⟩, h⟩
        simpa [P, largePadding, hij] using (show L ≤ Y.val i j by omega)
      · simp [P, largePadding, hij]
    · intro hg
      rintro ⟨p, hp⟩
      have h := hg p.val.1 p.val.2
      have hm : (p.val.1, p.val.2) ∈ K := p.property
      simp only [P, largePadding, hm, ite_true, if_true] at h
      omega
  have he : {Y : T // ¬∃ p : K, Y.val p.val.1 p.val.2 < L} ≃
      {Y : T // ∀ i j, P i j ≤ Y.val i j} := Equiv.subtypeEquivRight heq
  rw [Fintype.card_congr he]
  exact successful_card r c P

/-- The successful enlarged-table fraction is bounded using the proved
small-entry estimate and the exact padding bijection. This is the counting
part of paper 200-01's stationary-success proposition. -/
theorem padding_success_fraction (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (K : Finset (I × J)) (L U d : ℕ)
    (hd : 0 < d) (hrows : Fintype.card I ≤ d) (hcols : Fintype.card J ≤ d)
    (hrow : ∀ p ∈ K, U ≤ r p.1) (hcol : ∀ p ∈ K, U ≤ c p.2)
    (hU : 4 * d ≤ U) (hL : 2 * L ≤ U) :
    1 - K.card * (4 * L * (d : ℝ) ^ 3 / U) ≤
      (Fintype.card (Table r c) : ℝ) /
        Fintype.card (Table (paddedRows r (largePadding K L))
          (paddedColumns c (largePadding K L))) := by
  classical
  let P := largePadding K L
  let r' := paddedRows r P
  let c' := paddedColumns c P
  have htotal' : ∑ i, r' i = ∑ j, c' j := by
    dsimp [r', c', paddedRows, paddedColumns]
    rw [sum_add_distrib, sum_add_distrib, htotal, sum_comm (f := P)]
  let T := Table r' c'
  let bad (Y : T) : Prop := ∃ p : K, Y.val p.val.1 p.val.2 < L
  have hgood : Fintype.card {Y : T // ¬bad Y} = Fintype.card (Table r c) :=
    large_padding_good_card r c K L
  have hcard : (0 : ℝ) < Fintype.card T := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (table_nonempty r' c' htotal'))
  have hbound (p : K) :
      (Fintype.card {Y : T // Y.val p.val.1 p.val.2 < L} : ℝ) / Fintype.card T ≤
        4 * L * (d : ℝ) ^ 3 / U :=
    small_entry_probability htotal' p.val.1 p.val.2 U d L hd hrows hcols
      ((hrow p.val p.property).trans (Nat.le_add_right _ _))
      ((hcol p.val p.property).trans (Nat.le_add_right _ _)) hU hL
  have hfrac := fraction_not_exists (fun (p : K) (Y : T) => Y.val p.val.1 p.val.2 < L)
    (4 * L * (d : ℝ) ^ 3 / U) hcard (fun p => by
      simpa only [Fintype.card_eq_nat_card] using hbound p)
  simp only [Fintype.card_eq_nat_card] at hfrac hgood ⊢
  change 1 - Nat.card K * (4 * L * (d : ℝ) ^ 3 / U) ≤
    (Nat.card {Y : T // ¬bad Y} : ℝ) / Nat.card T at hfrac
  rw [hgood] at hfrac
  simpa only [Nat.card_eq_finsetCard] using hfrac

end SuccessFraction

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Parameters
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parameter arithmetic for the samplers

The manuscript's padding and rare tabulation estimates give explicit
inequalities for successful unpadding and expected correction cost.
-/

namespace ContingencyTables

open scoped BigOperators

/-- For the actual choices `L=d¹²`, `U=d²⁰`, the uniform padded table
unpads successfully with probability at least one half. -/
theorem padding_success_half {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j)
    (K : Finset (I × J)) (d : ℕ) (hd : 14 ≤ d)
    (hrows : Fintype.card I ≤ d) (hcols : Fintype.card J ≤ d)
    (hK : K.card ≤ d) (hrow : ∀ p ∈ K, d ^ 20 ≤ r p.1)
    (hcol : ∀ p ∈ K, d ^ 20 ≤ c p.2) :
    (1 / 2 : ℝ) ≤ (Fintype.card (Table r c) : ℝ) /
      Fintype.card (Table (paddedRows r (largePadding K (d ^ 12)))
        (paddedColumns c (largePadding K (d ^ 12)))) := by
  have hd₀ : 0 < d := by omega
  have hU : 4 * d ≤ d ^ 20 := by
    have hd₄ : 4 ≤ d := by omega
    have hpow : d ≤ d ^ 19 := Nat.le_self_pow (by decide) d
    calc
      4 * d ≤ d * d ^ 19 := Nat.mul_le_mul hd₄ hpow
      _ = d ^ 20 := by ring
  have hL : 2 * d ^ 12 ≤ d ^ 20 := by
    have hpow : d ≤ d ^ 8 := Nat.le_self_pow (by decide) d
    have hd₂ : 2 ≤ d ^ 8 := by omega
    calc
      2 * d ^ 12 ≤ d ^ 8 * d ^ 12 := Nat.mul_le_mul_right _ hd₂
      _ = d ^ 20 := by ring
  have h := padding_success_fraction r c htotal K (d ^ 12) (d ^ 20) d
    hd₀ hrows hcols hrow hcol hU hL
  have he := padding_error_le_half d K.card hd hK
  push_cast at h
  linarith

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseExponentArithmetic
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural arithmetic for the dense acceptance exponent

Each integral completion entry is represented by a difference of two
natural numbers. The rational floor in the geometric definition is then
an ordinary natural quotient, including zero denominators.
-/

namespace ContingencyTables.GridBoundary
open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

variable {q K : ℕ}

def arithmeticExponentAt (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I×J ≃ Fin q) (a : Grid (I := Fin q) K) :
    Option (Option I×Option J) → ℕ
  | none => 0
  | some g =>
      let parts := integerParts R P (cornerFree R P d e a) g.1 g.2
      componentExponent d (min (R g.1) (P g.2)) parts.1 parts.2

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalWalkApproximation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adaptive completion errors add once per actual transition -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {α β : Type*} [Fintype α] [Fintype β]

variable [DecidableEq α]

/-- The common state may depend on earlier randomness. Only the uniform
one-step bound is used; the approximating chain need not be reversible. -/
theorem walkLaw_variation (K L : α → RationalLaw α) (η : ℚ)
    (hη : ∀ x,variation (K x) (L x) ≤ η) (a : α) (n : ℕ) :
    variation (walkLaw K a n) (walkLaw L a n) ≤ n*η := by
  induction n with
  | zero => simp [walkLaw,variation]
  | succ n ih =>
    change variation (bindLaw (walkLaw K a n) K) (bindLaw (walkLaw L a n) L) ≤ _
    calc
      _ ≤ variation (walkLaw K a n) (walkLaw L a n)+η := variation_bind_uniform _ _ K L η hη
      _ ≤ (n:ℚ)*η+η := add_le_add_left ih η
      _ = _ := by push_cast; ring

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomial
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeFunction Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def PolynomialBound {f : A → B} (F : Realizer f) (p : Polynomial ℕ) : Prop :=
  ∀ a,F.cost a+weight (f a)≤p.eval (weight a)
def PolynomialTime {f : A → B} (F : Realizer f) : Prop := ∃ p,PolynomialBound F p

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeCanonical
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

variable (r : A → A → Prop) [DecidableRel r]
def insertStepRealizer (R : Realizer (fun x : A×A=>decide (r x.1 x.2))) : Realizer (insertStep r) :=
  (pair (composition second first) (pair (composition (pair first (composition (composition second second) first)) listCons)
    (choose (composition (pair (composition second first) first) R)
      (composition (pair (composition second first) (composition (pair first (composition (composition second second) first)) listCons)) listCons)
      (composition (pair first (composition (composition second second) second)) listCons)))).congr (by intro x; simp [insertStep])
omit [Codec A] in
lemma insert_fold (as bs : List A) (a : A) :
    as.reverse.foldl (fun z b=>insertStep r (b,z)) (a,(bs,List.orderedInsert r a bs))=
      (a,(as++bs,List.orderedInsert r a (as++bs))) := by
  induction as with
  | nil => rfl
  | cons b as ih =>
    rw [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    rfl
def orderedInsert (R : Realizer (fun x : A×A=>decide (r x.1 x.2))) :
    Realizer (fun x : A×List A=>List.orderedInsert r x.1 x.2) :=
  (composition (composition (pair (composition second reverse)
    (pair first (pair (constant []) (composition (pair first (constant [])) listCons))))
      (fold (insertStepRealizer r R))) (composition second second)).congr (by
        intro x
        change (x.2.reverse.foldl (fun z b=>insertStep r (b,z)) (x.1,([],[x.1]))).2.2=_
        have h:=insert_fold r x.2 [] x.1
        simpa only [List.append_nil,List.orderedInsert_nil] using congrArg (fun x=>x.2.2) h)

def insertionSort (R : Realizer (fun x : A×A=>decide (r x.1 x.2))) :
    Realizer (List.insertionSort r) :=
  (composition (pair reverse (constant [])) (fold (orderedInsert r R))).congr (by
    intro as
    change as.reverse.foldl (fun bs a=>List.orderedInsert r a bs) []=as.insertionSort r
    rw [List.foldl_reverse]
    rfl)

variable [DecidableEq A]
omit [Codec A] in
lemma canonical_eq_sort [IsTrans A r] [Std.Total r] [Std.Antisymm r] (as : List A) :
    as.dedup.insertionSort r=as.toFinset.sort r := by
  have hn:=(List.perm_insertionSort r as.dedup).nodup_iff.mpr (List.nodup_dedup as)
  have hh:=(List.toFinset_sort (r:=r) hn).mpr (List.pairwise_insertionSort r as.dedup)
  have he : (as.dedup.insertionSort r).toFinset=as.toFinset := by ext a; simp
  rw [he] at hh
  exact hh.symm
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFinite
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

variable [LinearOrder A]

def finsetList : Realizer (fun s : Finset A=>s.sort (·≤·)) :=
  (identity (A:=List A)).recode (fun s : Finset A=>s.sort (·≤·)) (fun s=>s.sort (·≤·)) (fun _=>rfl) (fun _=>rfl)

def finsetCard : Realizer (Finset.card (α:=A)) :=
  (composition finsetList listLength).congr (by intro s; simp)

omit [Codec A] in
lemma sort_filter (p : A → Bool) (s : Finset A) :
    (s.sort (·≤·)).filter p=(s.filter fun a=>p a).sort (·≤·) := by
  have hh := (List.toFinset_sort (r:=(·≤·)) ((Finset.sort_nodup s (·≤·)).filter p)).mpr
    ((Finset.pairwise_sort s (·≤·)).filter p)
  simpa only [List.toFinset_filter,Finset.sort_toFinset] using hh.symm

def finsetFilter {p : A → Bool} (P : Realizer p) : Realizer (fun s : Finset A=>s.filter fun a=>p a) :=
  (filter P).recode (fun s=>s.sort (·≤·)) _ (fun _=>rfl) (fun s=>by
    change encode ((s.sort (·≤·)).filter p)=encode ((s.filter fun a=>p a).sort (·≤·))
    rw [sort_filter])

def finsetFilterWith {p : B×A → Bool} (P : Realizer p) :
    Realizer (fun x : B×Finset A=>x.2.filter fun a=>p (x.1,a)) :=
  (filterWith P).recode (fun x=>(x.1,x.2.sort (·≤·))) _ (fun _=>rfl) (fun x=>by
    change encode ((x.2.sort (·≤·)).filter fun a=>p (x.1,a))=encode ((x.2.filter fun a=>p (x.1,a)).sort (·≤·))
    rw [sort_filter])

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreeCostMeasure
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def WorkBound {f : A → B} (F : Realizer f) (measure : A → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ a,F.cost a+weight (f a)≤p.eval (measure a)

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFiniteOps
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

variable [LinearOrder A]
def finsetAny {p : B×A → Bool} (P : Realizer p) :
    Realizer (fun x : B×Finset A=>decide (∃ a∈x.2,p (x.1,a)=true)) :=
  (composition (composition (pair first (composition second finsetList)) (mapWith P)) any).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.any_map,List.any_eq_true,id_eq,decide_eq_true_eq,Finset.mem_sort])

def finsetAll {p : B×A → Bool} (P : Realizer p) :
    Realizer (fun x : B×Finset A=>decide (∀ a∈x.2,p (x.1,a)=true)) :=
  (composition (composition (pair first (composition second finsetList)) (mapWith P)) all).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.all_map,List.all_eq_true,id_eq,decide_eq_true_eq,Finset.mem_sort])

def finsetErase (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : A×Finset A=>x.2.erase x.1) :=
  (finsetFilterWith (composition E boolNot)).congr (by
    intro x; ext a
    simp only [Function.comp_apply,Finset.mem_filter,Bool.not_eq_true',decide_eq_false_iff_not,Finset.mem_erase]
    tauto)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeColex
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type} [Codec A] [Codec B] [LinearOrder A] [LinearOrder B]

def lexLe (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2)))
    (S : Realizer (fun x : B×B=>decide (x.1≤x.2))) :
    Realizer (fun x : (A×B)×(A×B)=>decide (toLex x.1≤toLex x.2)) :=
  (composition (pair (composition (pair first.fst second.fst) R)
    (composition (pair (composition (composition (pair first.fst second.fst) E) boolNot)
      (composition (pair first.snd second.snd) S)) boolOr)) boolAnd).congr (by
        intro x
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',
          decide_eq_true_eq,decide_eq_false_iff_not,Prod.Lex.le_iff]
        rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
        dsimp only
        constructor
        · rintro ⟨h,h'⟩
          rcases lt_or_eq_of_le h with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h,h'.resolve_left (not_not.mpr h)⟩
        · rintro (h|⟨h,h'⟩)
          · exact ⟨h.le,Or.inl (ne_of_lt h)⟩
          · exact ⟨h.le,Or.inr h'⟩)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFiniteCollections
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

variable [LinearOrder A]
def finsetSingleton : Realizer (fun a : A=>({a} : Finset A)) :=
  (composition (pair identity (constant ([] : List A))) listCons).recode id
    (fun a=>({a} : Finset A)) (fun _=>rfl) (by intro a; simp only [Function.comp_apply,encode_finset,Finset.sort_singleton]; rfl)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ListWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the finite-list proposal

The list is scanned only up to its own length. A binary index beyond the
end produces `none`; its numerical magnitude never determines a loop bound.
-/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

variable {A : Type} [Codec A] [Inhabited A]

omit [Codec A] [Inhabited A] in
lemma bitValue_eq_word (k : ℕ) (bits : Fin k → Bool) :
    StackAddition.value (List.ofFn bits)=(FairBits.binaryWordEquiv k bits).val := by
  have hv (k : ℕ) (bits : Fin k → Bool) :
      StackAddition.value (List.ofFn bits)=∑ i, (bits i).toNat*2^i.val := by
    induction k with
    | zero => simp [StackAddition.value]
    | succ k ih =>
      rw [List.ofFn_succ,StackAddition.value,ih,Fin.sum_univ_succ]
      simp only [Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
  rw [hv]
  change _=∑ i : Fin k, (finTwoEquiv.symm (bits i)).val*2^i.val
  apply Finset.sum_congr rfl
  intro i _
  cases bits i <;> rfl

omit [Codec A] [Inhabited A] in
theorem listWordChoice_ofFn (xs : List A) (k : ℕ) (bits : Fin k → Bool) :
    listWordChoice (xs,List.ofFn bits)=FairBits.listBitDraw xs k bits := by
  simp only [listWordChoice,FairBits.listBitDraw,bitValue_eq_word]

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityFold
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial sequential list program for the subset draw

The accumulator retains the remaining population and requested size,
and records one inclusion bit per input word. Both counters decrease;
only the output list grows. The final program reverses that list once.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def sampleWords (n k : ℕ) : List (List Bool) → List Bool
  | [] => []
  | w::ws =>
      let b := includeCode ((n,k),w)
      b::sampleWords (n-1) (if b then k-1 else min k (n-1)) ws

end ContingencyTables.FixedCardinalityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OnlineRetryPrefix
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite execution prefixes of the unbounded exact-rejection loop -/

namespace ContingencyTables.OnlineRetryPrefix
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.PhysicalStream
open MatchingFPRAS.TreeMachine (Env K encodeEnv)
open MatchingFPRAS.RegisterProc MatchingFPRAS.OnlineStack
open MatchingFPRAS.OnlineControl Turing

variable {R Λ α : Type} [DecidableEq R]

/-- A failed finite prefix ends at the live retry label, while a successful
prefix ends in the machine's halted configuration. -/
def At (M : Λ → Instr R Λ) (out : α → Option Λ×Env R)
    (l : Option Λ) (E : Env R) (p : Experiment α) : Prop :=
  Executes (code M) (coins M) (fun a => OnlineControl.cfg M (out a).1 (out a).2) (OnlineControl.cfg M l E) p

end ContingencyTables.OnlineRetryPrefix

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OnlineIntegerRetry
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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

variable {A B : Type} [Codec A] [Codec B] [Inhabited B]
variable {f : A → Experiment (Option B)}

def output (a : A) (s : Data) : Option B → Option Label×Env Reg
  | none => (some .prepare,env (TreeTyped.encode a) .nil s)
  | some b => (none,env (TreeTyped.encode b) .nil s)

end ContingencyTables.OnlineIntegerRetry

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

omit [Fintype G] in
lemma smallTotal_removeTwo (line : I → G) (inner : I → Bool) (z : I → ℕ)
    (i j : I) (hv : ValidPair z i j) (g : G) :
    smallTotal line inner (removeTwo z i j) g +
      (if subgroup line inner i=some g then 1 else 0) +
      (if subgroup line inner j=some g then 1 else 0) = smallTotal line inner z g := by
  have h := lineTotal_removeTwo (fun k => (line k,inner k)) z i j hv (g,true)
  cases hi : inner i <;> cases hj : inner j <;>
    simpa [smallTotal,subgroup,hi,hj,Prod.mk.injEq] using h

/-- Exact literal nested product at every valid integer two-removal entry. -/
theorem nestedWeight_removeTwo (line : I → G) (inner : I → Bool) (a c : G → ℕ → ℝ)
    (z : I → ℕ) (i j : I) (hv : ValidPair z i j) :
    nestedWeight line inner a c (removeTwo z i j) =
      nestedRemoval line inner
        (fun g => a g (lineTotal line z g)) (fun g => a g (lineTotal line z g-1))
        (fun g => if 2 ≤ lineTotal line z g then a g (lineTotal line z g-2) else 0)
        (fun g => c g (smallTotal line inner z g)) (fun g => c g (smallTotal line inner z g-1))
        (fun g => if 2 ≤ smallTotal line inner z g then c g (smallTotal line inner z g-2) else 0) i j := by
  unfold nestedWeight nestedRemoval productTwoUpdates
  congr 1
  · apply Finset.prod_congr rfl
    intro g _
    have ht := lineTotal_removeTwo line z i j hv g
    by_cases hi : g=line i
    · by_cases hj : g=line j
      · have hn : 2 ≤ lineTotal line z g := by simp only [hi.symm,hj.symm,ite_true, if_true] at ht; omega
        have he : lineTotal line (removeTwo z i j) g=lineTotal line z g-2 := by
          simp only [hi.symm,hj.symm,ite_true, if_true] at ht; omega
        simp only [ite_eq_left hi,ite_eq_left hj,ite_eq_left hn,he]
      · have he : lineTotal line (removeTwo z i j) g=lineTotal line z g-1 := by
          simp only [hi.symm,ite_true, if_true,Ne.symm hj,ite_false] at ht; omega
        simp only [ite_eq_left hi,ite_eq_right hj,he]
    · by_cases hj : g=line j
      · have he : lineTotal line (removeTwo z i j) g=lineTotal line z g-1 := by
          simp only [Ne.symm hi,ite_false,hj.symm,ite_true, if_true] at ht; omega
        simp only [ite_eq_right hi,ite_eq_left hj,he]
      · have he : lineTotal line (removeTwo z i j) g=lineTotal line z g := by
          simp only [Ne.symm hi,Ne.symm hj,ite_false,add_zero] at ht; exact ht
        simp only [ite_eq_right hi,ite_eq_right hj,he]
  · rw [Fintype.prod_option]
    simp only [unitExtension,Option.elim_none,ite_self,one_mul]
    apply Finset.prod_congr rfl
    intro g _
    have ht := smallTotal_removeTwo line inner z i j hv g
    by_cases hi : some g=subgroup line inner i
    · by_cases hj : some g=subgroup line inner j
      · have hn : 2 ≤ smallTotal line inner z g := by simp only [hi.symm,hj.symm,ite_true, if_true] at ht; omega
        have he : smallTotal line inner (removeTwo z i j) g=smallTotal line inner z g-2 := by
          simp only [hi.symm,hj.symm,ite_true, if_true] at ht; omega
        simp only [ite_eq_left hi,ite_eq_left hj,Option.elim_some,ite_eq_left hn,he]
      · have he : smallTotal line inner (removeTwo z i j) g=smallTotal line inner z g-1 := by
          simp only [hi.symm,ite_true, if_true,Ne.symm hj,ite_false] at ht; omega
        simp only [ite_eq_left hi,ite_eq_right hj,Option.elim_some,he]
    · by_cases hj : some g=subgroup line inner j
      · have he : smallTotal line inner (removeTwo z i j) g=smallTotal line inner z g-1 := by
          simp only [Ne.symm hi,ite_false,hj.symm,ite_true, if_true] at ht; omega
        simp only [ite_eq_right hi,ite_eq_left hj,Option.elim_some,he]
      · have he : smallTotal line inner (removeTwo z i j) g=smallTotal line inner z g := by
          simp only [Ne.symm hi,Ne.symm hj,ite_false,add_zero] at ht; exact ht
        simp only [ite_eq_right hi,ite_eq_right hj,Option.elim_some,he]

/-- The exact integer two-removal signature for the first paper's full
line penalties and nested small-slot subset penalties. -/
theorem nested_product_removal_onePositive (line : I → G) (inner : I → Bool)
    (a c : G → ℕ → ℝ) (z : I → ℕ)
    (ha : ∀ g n, n ≤ lineTotal line z g → 0 < a g n)
    (hc : ∀ g n, n ≤ smallTotal line inner z g → 0 < c g n)
    (halc : ∀ g, 2 ≤ lineTotal line z g →
      a g (lineTotal line z g)*a g (lineTotal line z g-2) ≤ a g (lineTotal line z g-1)^2)
    (hclc : ∀ g, 2 ≤ smallTotal line inner z g →
      c g (smallTotal line inner z g)*c g (smallTotal line inner z g-2) ≤
        c g (smallTotal line inner z g-1)^2) :
    OnePositiveDirection (integerRemovalMatrix (nestedWeight line inner a c) z).toBilin' := by
  let a₀ := fun g => a g (lineTotal line z g)
  let a₁ := fun g => a g (lineTotal line z g-1)
  let a₂ := fun g => if 2 ≤ lineTotal line z g then a g (lineTotal line z g-2) else 0
  let c₀ := fun g => c g (smallTotal line inner z g)
  let c₁ := fun g => c g (smallTotal line inner z g-1)
  let c₂ := fun g => if 2 ≤ smallTotal line inner z g then c g (smallTotal line inner z g-2) else 0
  let H := nestedRemoval line inner a₀ a₁ a₂ c₀ c₁ c₂
  have ha₀ : ∀ g, 0 < a₀ g := fun g => ha g _ le_rfl
  have ha₁ : ∀ g, 0 < a₁ g := fun g => ha g _ (Nat.sub_le _ _)
  have ha₂ : ∀ g, 0 ≤ a₂ g := by intro g; dsimp [a₂]; split_ifs; exact (ha g _ (Nat.sub_le _ _)).le; exact le_rfl
  have hc₀ : ∀ g, 0 < c₀ g := fun g => hc g _ le_rfl
  have hc₁ : ∀ g, 0 < c₁ g := fun g => hc g _ (Nat.sub_le _ _)
  have hc₂ : ∀ g, 0 ≤ c₂ g := by intro g; dsimp [c₂]; split_ifs; exact (hc g _ (Nat.sub_le _ _)).le; exact le_rfl
  have hH : OnePositiveDirection H.toBilin' := nestedRemoval_onePositive line inner a₀ a₁ a₂ c₀ c₁ c₂
    ha₀ ha₁ ha₂ hc₀ hc₁
    (fun g => by dsimp [a₀,a₁,a₂]; split_ifs with h; exact halc g h; simp [sq_nonneg])
    (fun g => by dsimp [c₀,c₁,c₂]; split_ifs with h; exact hclc g h; simp [sq_nonneg])
  have hHdiag (i : I) : 0 ≤ H i i := by
    apply mul_nonneg
    · exact updates_nonnegative a₀ a₁ a₂ (fun g => (ha₀ g).le) (fun g => (ha₁ g).le) ha₂ _ _
    · apply updates_nonnegative
      · intro g; cases g <;> simp [unitExtension,(hc₀ _).le]
      · intro g; cases g <;> simp [unitExtension,(hc₁ _).le]
      · intro g; cases g <;> simp [unitExtension,hc₂]
  have hsig : OnePositiveDirection (scaledMatrix H (activeMask z)).toBilin' := by
    intro x hx y hxy
    rw [scaledMatrix_form] at hx hxy ⊢
    exact hH _ hx _ hxy
  apply onePositive_of_dominated_compression (scaledMatrix H (activeMask z)).toBilin'
    (integerRemovalMatrix (nestedWeight line inner a c) z).toBilin' LinearMap.id
  · exact fun x y => (matrix_bilin_symm _ (fun i j => by
      simp only [integerRemovalMatrix,validPair_symm z i j,removeTwo_comm z i j])).eq x y
  · exact hsig
  · intro v
    rw [masked_correction _ z H (nestedWeight_removeTwo line inner a c z)]
    simp only [map_sub,LinearMap.sub_apply,diagonalMatrix_form,LinearMap.id_apply]
    apply sub_le_self
    apply Finset.sum_nonneg
    intro i _
    have hκ : 0 ≤ if z i=1 then H i i else 0 := by split_ifs; exact hHdiag i; exact le_rfl
    nlinarith [mul_nonneg hκ (sq_nonneg (v i))]

end ContingencyTables.NestedProductSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_LabelledFactorial
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

/-- Integer removal signatures imply the omission property of the literal
first factorial lift, through the proved exact copy-display congruence. -/
theorem firstLift_omission (group : I → G) (h : (G → ℕ) → ℝ) (D : ℝ) (k : ℕ)
    (hD : 0 < D) (hh : ∀ n, 0 ≤ h n)
    (hsig : ∀ A : Set I, A.ncard + 2 = Fintype.card I - k →
      OnePositiveDirection (integerRemovalMatrix h (groupCount group Aᶜ)).toBilin') :
    OmissionProperty (firstLift group h D) k := by
  intro A hA
  rw [firstLift_omission_matrix]
  apply onePositive_reindex (displayCopyEquiv group Aᶜ)
  have hs := removalLift_onePositive h (groupCount group Aᶜ) D hD hh (hsig A hA)
  have hm := (signature_iff _ (matrix_bilin_symm _ (show ∀ i j,
      removalLiftMatrix h (groupCount group Aᶜ) D i j =
      removalLiftMatrix h (groupCount group Aᶜ) D j i from by
    intro i j
    simp only [removalLiftMatrix, eq_comm, removeTwo_comm]))).mp hs
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  congr 2; exact Subsingleton.elim _ _

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

/-- The exact box-valid raw removal signature implies the omission
property of the manuscript's first lift at its original degree. -/
theorem firstLift_omission_slice (group : L → C) (h : (C → ℕ) → ℝ) (D : ℝ) (R : ℕ)
    (hD : 0 < D) (hh : ∀ z, 0 ≤ h z)
    (hsig : RemovalSlice h (groupCount group Set.univ) R) :
    OmissionProperty (firstLift group h D) R := by
  apply firstLift_omission group h D R hD hh
  intro A hA
  apply hsig _ (groupCount_inBox group Aᶜ)
  rw [groupCount_total]
  have hc := Set.ncard_add_ncard_compl A
  simp only [Nat.card_eq_fintype_card] at hc
  omega

end ContingencyTables.SliceFactorial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_NestedPenaltyApplication
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

theorem softWeight_removal (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (hL : 0 ≤ L) (z : C → ℕ) :
    OnePositiveDirection
      (integerRemovalMatrix (softWeight line inner offset slope smallOffset smallSlope L) z).toBilin' := by
  apply nested_product_removal_onePositive line inner
  · intro g n _; exact factor_positive _ _ _
  · intro g n _; exact factor_positive _ _ _
  · intro g hn; exact abs_factor_logConcave L (offset g) (slope g) hL _ hn
  · intro g hn; exact positivePart_factor_logConcave L (smallOffset g) (smallSlope g) hL _ hn

theorem softWeight_tendsto (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (z : C → ℕ) :
    Tendsto (fun L : ℝ => softWeight line inner offset slope smallOffset smallSlope L z) atTop
      (nhds (hardWeight line inner offset slope smallOffset smallSlope z)) := by
  simp_rw [softWeight_eq]
  exact factor_limit _ (penalty_nonnegative line inner offset slope smallOffset smallSlope z)

variable {I : Type*} [Fintype I]

/-- The actual softened marginal is positive before the hard limit and
has the raw integer removal signature on every required display. -/
theorem softened_marginal_slices (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (line : Coordinates I Ms → G) (inner : Coordinates I Ms → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M) :
    PositiveSlice (eliminate Ms (softWeight line inner offset slope smallOffset smallSlope L)) m R ∧
      RemovalSlice (eliminate Ms (softWeight line inner offset slope smallOffset smallSlope L)) m R := by
  apply eliminate_slices Ms m R _ hwidth
  · intro z _ _; exact softWeight_positive line inner offset slope smallOffset smallSlope L z
  · intro z _ _
    convert softWeight_removal line inner offset slope smallOffset smallSlope L hL z using 1
    all_goals try with_reducible_and_instances rfl
    congr 2 <;> exact Subsingleton.elim _ _

end ContingencyTables.NestedPenaltyApplication

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalLargeProfiles
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the arbitrary enumeration from the physical large-cell sum -/

namespace ContingencyTables.PhysicalLargeProfiles

open scoped BigOperators Classical
open LargePairEnumeration

variable {C : Type*}

lemma joinedProfile_physical {n : ℕ} (small : C → Bool) (M : C → ℕ)
    (e : Fin n ≃ LargeCell small) (z : SmallView small → ℕ)
    (a : PhysicalAssignments small M) :
    joinedProfile (fun k => M (e k).val) z
      ((Equiv.piCongrLeft (fun l : LargeCell small => Fin (M l.val+1)) e).symm a) ∘
      (physicalJoinEquiv small e).symm=physicalProfile small M z a := by
  funext u
  rcases u with ⟨c,b⟩
  by_cases hs : small c=true
  · simp [physicalJoinEquiv,partitionEquiv,joinedProfile,physicalProfile,hs]
  · simp [physicalJoinEquiv,partitionEquiv,joinedProfile,physicalProfile,hs]
    have hval := congrArg (fun l : LargeCell small => (a l).val)
      (e.apply_symm_apply ⟨c,Bool.eq_false_iff.mpr hs⟩)
    exact congrArg (fun t : ℕ => if b then M c-t else t) hval

variable [Fintype C]

/-- The physical finite sum is independent of the order used to enumerate
large cells in the recursive signature proof. -/
theorem sum_joined_eq_physical {n : ℕ} (small : C → Bool) (M : C → ℕ)
    (e : Fin n ≃ LargeCell small) (z : SmallView small → ℕ)
    (F : (C×Bool → ℕ) → ℝ) :
    (∑ a : ((k : Fin n) → Fin (M (e k).val+1)),
      F (joinedProfile (fun k => M (e k).val) z a ∘ (physicalJoinEquiv small e).symm))=
      ∑ a : PhysicalAssignments small M, F (physicalProfile small M z a) := by
  apply Fintype.sum_equiv (Equiv.piCongrLeft (fun l : LargeCell small => Fin (M l.val+1)) e)
  intro a
  congr 1
  have h := joinedProfile_physical small M e z
    ((Equiv.piCongrLeft (fun l : LargeCell small => Fin (M l.val+1)) e) a)
  simpa only [Equiv.symm_apply_apply] using h

end ContingencyTables.PhysicalLargeProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestCountIdentification
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The companion signature marginal is the literal weighted completion count

The physical all-large product is split bijectively into tree and free
assignments. Exact nonroot equations then retain one tree completion per
free assignment, with exactly its root/tree exponential penalty.
-/

namespace ContingencyTables.ForestCountIdentification

open scoped BigOperators Classical
open SimpleGraph LargePairEnumeration PhysicalLargeProfiles
open ForestCapacity GraphCompletionCounts ForestAssignmentSplit ForestLiteralCount

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] [Fintype J] in
lemma split_profile (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T ≤ cellGraph small) (d : ℕ) (b : I → J → ℕ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ)
    (a : TreeIndex T d b×FreeIndex small T b) :
    physicalProfile (fun a : I×J => small a.1 a.2) (fun p => width T d b p.1 p.2) z
      ((assignmentSplit small T hTG d b).symm a)=
      profile small T d b (smallX small z) (smallY small z) (freeTable small T b a.2) a.1 := by
  funext u
  rcases u with ⟨⟨i,j⟩,v⟩
  by_cases hs : small i j=true
  · cases v <;> simp [physicalProfile,hs,profile,smallX,smallY]
  · have hs' : small i j=false := Bool.eq_false_iff.mpr hs
    have he := split_cellCount small T hTG d b a ⟨(i,j),hs'⟩
    cases v <;> simp [physicalProfile,hs,profile,he]

end ContingencyTables.ForestCountIdentification

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_NestedReindex
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical coordinate reindexing of the first paper's nested penalties -/

namespace ContingencyTables.NestedReindex

open scoped BigOperators Classical
open ProductIntegerSignature NestedProductSignature NestedPenaltyApplication
open BalancedFamily BalancedBox EqualityReindex

variable {C D G : Type*} [Fintype C] [Fintype D] [Fintype G]

omit [Fintype G] in
lemma smallTotal_reindex (e : C ≃ D) (line : D → G) (inner : D → Bool)
    (z : C → ℕ) (g : G) :
    smallTotal (line ∘ e) (inner ∘ e) z g=smallTotal line inner (z ∘ e.symm) g := by
  exact lineTotal_reindex e (fun d => (line d,inner d)) z (g,true)

lemma penalty_reindex (e : C ≃ D) (line : D → G) (inner : D → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (z : C → ℕ) :
    penalty (line ∘ e) (inner ∘ e) offset slope smallOffset smallSlope z=
      penalty line inner offset slope smallOffset smallSlope (z ∘ e.symm) := by
  unfold penalty
  simp_rw [lineTotal_reindex,smallTotal_reindex]

lemma softWeight_reindex (e : C ≃ D) (line : D → G) (inner : D → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (z : C → ℕ) :
    softWeight (line ∘ e) (inner ∘ e) offset slope smallOffset smallSlope L z=
      softWeight line inner offset slope smallOffset smallSlope L (z ∘ e.symm) := by
  rw [softWeight_eq,softWeight_eq,penalty_reindex]

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem physical_soft_marginal_slices (Ms : List ℕ) (m : S → ℕ) (R : ℕ)
    (e : Coordinates S Ms ≃ D) (line : D → G) (inner : D → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (L : ℝ) (hL : 0≤L)
    (hwidth : ∀ M ∈ Ms, 2≤M) :
    PositiveSlice (eliminate Ms (fun z =>
      softWeight line inner offset slope smallOffset smallSlope L (z ∘ e.symm))) m R ∧
    RemovalSlice (eliminate Ms (fun z =>
      softWeight line inner offset slope smallOffset smallSlope L (z ∘ e.symm))) m R := by
  have hd : (inferInstance : DecidableEq S)=Classical.decEq S := Subsingleton.elim _ _
  cases hd
  have heq : (fun z => softWeight line inner offset slope smallOffset smallSlope L
      (z ∘ e.symm))=softWeight (line ∘ e) (inner ∘ e) offset slope smallOffset smallSlope L := by
    funext z
    exact (softWeight_reindex e line inner offset slope smallOffset smallSlope L z).symm
  rw [heq]
  exact softened_marginal_slices Ms m R (line ∘ e) (inner ∘ e)
    offset slope smallOffset smallSlope L hL hwidth

end ContingencyTables.NestedReindex

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

noncomputable def physicalWeight (A : Instance I J) (S : Selection A.T) (alpha : ℝ) :
    (((I×J)×Bool) → ℕ) → ℝ :=
  exactWeight cellLine (rootFlag S) (fun _ => alpha)
    (lineOffset (ell A) (widths A) A.r A.c) viewSlope
    (unaryRate A.T A.b alpha) (unaryEll (ell A)) unarySlope (unaryCap A.b)

theorem exact_eq (A : Instance I J) (S : Selection A.T) (alpha : ℝ)
    (z : ((I×J)×Bool) → ℕ) :
    physicalWeight A S alpha z=
      if (∀ g,rootFlag S g=false → deviation (ell A) (widths A) A.r A.c z g=0)
      then (2:ℝ)^(-alpha*penalty A S z) else 0 := by
  by_cases h : ∀ g,rootFlag S g=false → deviation (ell A) (widths A) A.r A.c z g=0
  · rw [ite_eq_left h]
    unfold physicalWeight exactWeight productWeight penalty
    rw [line_product_eq A S alpha z h,unary_product_eq,
      ←Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨g,hg,hdev⟩ := h
    have hz : exactLineFactor (rootFlag S) (fun _ => alpha)
        (lineOffset (ell A) (widths A) A.r A.c) viewSlope g (lineTotal cellLine z g)=0 := by
      simp [exactLineFactor,hg,line_affine,hdev]
    unfold physicalWeight exactWeight productWeight
    rw [Finset.prod_eq_zero (Finset.mem_univ g) hz,zero_mul]

end ContingencyTables.RootedPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedLargeMarginal
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

noncomputable def largeMarginal (A : Instance I J) (S : Selection A.T) (alpha : ℝ)
    {n : ℕ} (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2))
    (z : View A → ℕ) : ℝ :=
  ∑ a : ((k : Fin n) → Fin (RootedPenalty.widths A (e k).val.1 (e k).val.2+1)),
    physicalWeight A S alpha
      (joinedProfile (fun k => RootedPenalty.widths A (e k).val.1 (e k).val.2) z a ∘
        (physicalJoinEquiv (fun a : I×J => A.small a.1 a.2) e).symm)

theorem largeMarginal_eq_eliminate (A : Instance I J) (S : Selection A.T)
    (alpha : ℝ) {n : ℕ} (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2)) :
    largeMarginal A S alpha e=
      BalancedFamily.eliminate (LargePairEnumeration.widths
        (fun k => RootedPenalty.widths A (e k).val.1 (e k).val.2)) (fun q =>
          physicalWeight A S alpha
            (q ∘ (physicalCoordinateEquiv (fun a : I×J => A.small a.1 a.2) e
              (fun k => RootedPenalty.widths A (e k).val.1 (e k).val.2)).symm)) := by
  funext z
  exact (eliminate_eq_actual_cells (fun a : I×J => A.small a.1 a.2) e _
    (physicalWeight A S alpha) z).symm

end ContingencyTables.RootedLargeMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedLiteralCount
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

theorem literal_tree_sum (A : Instance I J) (S : Selection A.T)
    (x y free : I → J → ℕ) (alpha : ℝ)
    (hx : ∀ i j,A.small i j=true → x i j≤ A.b i j)
    (hy : ∀ i j,A.small i j=true → y i j≤ A.b i j)
    (hf : ∀ i j,A.small i j=false → ¬A.T.Adj (.inl i) (.inr j) → free i j≤ A.b i j) :
    (∑ a : TreeIndex A.T A.d A.b,
      physicalWeight A S alpha (profile A.small A.T A.d A.b x y free a))=
      (2:ℝ)^(-alpha*actualPenalty A S x y free
        (solved A S (fun i j => (x i j:ℤ)) (fun i j => ((A.b i j-y i j:ℕ):ℤ))
          (fun i j => (free i j:ℤ)))) := by
  have hsum := tree_indicator_sum A S (fun i j => (x i j:ℤ))
    (fun i j => ((A.b i j-y i j:ℕ):ℤ)) (fun i j => (free i j:ℤ))
    (by
      intro i j hs
      refine ⟨⟨Nat.cast_nonneg _,?_⟩,⟨Nat.cast_nonneg _,?_⟩⟩
      · exact_mod_cast hx i j hs
      · exact_mod_cast Nat.sub_le (A.b i j) (y i j))
    (by
      intro i j hs ht
      exact ⟨Nat.cast_nonneg _,by exact_mod_cast hf i j hs ht⟩)
    (fun tree => (2:ℝ)^(-alpha*actualPenalty A S x y free tree))
  calc
    _=(∑ a : TreeIndex A.T A.d A.b,
      if RootConditions A S (fun i j => (x i j:ℤ))
        (fun i j => ((A.b i j-y i j:ℕ):ℤ)) (fun i j => (free i j:ℤ)) (physical A.T A.d A.b a)
      then (2:ℝ)^(-alpha*actualPenalty A S x y free (physical A.T A.d A.b a)) else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [RootedPenalty.exact_eq,
          show ForestPenaltyApplication.deviation (ell A) (widths A) A.r A.c
            (profile A.small A.T A.d A.b x y free a)=
            actualDeviation A.small A.T A.b x y free A.r A.c (physical A.T A.d A.b a) from
            deviation_profile A.small A.T A.hTG A.d A.b x y free a A.r A.c hy hf,
          penalty_profile A S x y free a hy hf]
        simp only [nonroot_iff A S x y free _ (physical_supported A.T A.d A.b a)]
    _=_ := hsum

end ContingencyTables.RootedLiteralCount

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCountIdentification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root physical marginal is its literal completion count -/

namespace ContingencyTables.RootedCountIdentification

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPenalty RootedLiteralCount
open ForestCountIdentification ForestAssignmentSplit ForestLiteralCount
open PhysicalLargeProfiles LargePairEnumeration BalancedBox GraphCompletionCounts

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def h (A : Instance I J) (S : Selection A.T) (alpha : ℝ)
    (z : View A → ℕ) : ℝ :=
  ∑ f : FreeIndex A.small A.T A.b,
    (2:ℝ)^(-alpha*RootedLiteralCount.actualPenalty A S
      (smallX A.small z) (smallY A.small z) (freeTable A.small A.T A.b f)
      (RootedPhysicalCompletion.solved A S (fun i j => (smallX A.small z i j:ℤ))
        (fun i j => ((A.b i j-smallY A.small z i j:ℕ):ℤ))
        (fun i j => (freeTable A.small A.T A.b f i j:ℤ))))

theorem h_positive (A : Instance I J) (S : Selection A.T) (alpha : ℝ)
    (z : View A → ℕ) : 0<h A S alpha z := by
  let f : FreeIndex A.small A.T A.b := fun _ => 0
  unfold h
  apply lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _)
  exact Finset.single_le_sum (fun a _ =>
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).le) (Finset.mem_univ f)

theorem physical_sum_split (A : Instance I J) (z : View A → ℕ)
    (F : (((I×J)×Bool) → ℕ) → ℝ) :
    (∑ a : PhysicalAssignments (fun a : I×J => A.small a.1 a.2)
      (fun a => width A.T A.d A.b a.1 a.2),
      F (physicalProfile (fun a : I×J => A.small a.1 a.2)
        (fun a => width A.T A.d A.b a.1 a.2) z a))=
      ∑ f : FreeIndex A.small A.T A.b,∑ t : TreeIndex A.T A.d A.b,
        F (profile A.small A.T A.d A.b (smallX A.small z) (smallY A.small z)
          (freeTable A.small A.T A.b f) t) := by
  have heq := Fintype.sum_equiv (assignmentSplit A.small A.T A.hTG A.d A.b)
    (fun a => F (physicalProfile (fun a : I×J => A.small a.1 a.2)
      (fun a => width A.T A.d A.b a.1 a.2) z a))
    (fun a => F (profile A.small A.T A.d A.b (smallX A.small z) (smallY A.small z)
      (freeTable A.small A.T A.b a.2) a.1)) (by
      intro a
      apply congrArg F
      have he := split_profile A.small A.T A.hTG A.d A.b z
        ((assignmentSplit A.small A.T A.hTG A.d A.b) a)
      simpa only [Equiv.symm_apply_apply] using he)
  rw [heq,Fintype.sum_prod_type,Finset.sum_comm]

theorem h_eq_largeMarginal (A : Instance I J) (S : Selection A.T) (alpha : ℝ)
    {n : ℕ} (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2))
    (z : View A → ℕ) (hz : InBox (bounds A) z) :
    h A S alpha z=RootedLargeMarginal.largeMarginal A S alpha e z := by
  unfold RootedLargeMarginal.largeMarginal RootedPenalty.widths
  rw [sum_joined_eq_physical (fun a : I×J => A.small a.1 a.2)
    (fun a : I×J => width A.T A.d A.b a.1 a.2) e z (physicalWeight A S alpha)]
  trans (∑ f : FreeIndex A.small A.T A.b,∑ t : TreeIndex A.T A.d A.b,
    physicalWeight A S alpha (profile A.small A.T A.d A.b
      (smallX A.small z) (smallY A.small z) (freeTable A.small A.T A.b f) t))
  · unfold h
    apply Finset.sum_congr rfl
    intro f _
    apply (RootedLiteralCount.literal_tree_sum A S _ _ _ alpha ?_ ?_ ?_).symm
    · intro i j hs
      simpa only [smallX,hs,dite_eq_left,bounds] using hz (⟨(i,j),hs⟩,false)
    · intro i j hs
      simpa only [smallY,hs,dite_eq_left,bounds] using hz (⟨(i,j),hs⟩,true)
    · exact freeTable_bound A.small A.T A.b f
  · convert (physical_sum_split A z (physicalWeight A S alpha)).symm using 1
    all_goals try with_reducible_and_instances rfl
    all_goals
      congr 1
      ext
      simp

end ContingencyTables.RootedCountIdentification

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedFactorialApplication
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual factorial lifts of the selected-root completion count -/

namespace ContingencyTables.RootedFactorialApplication

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS CompanionFactorialApplication
open LargePairEnumeration BalancedBox LabelledFactorial

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def f (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) : Set (Labels A×Bool) → ℝ :=
  firstLift (TwoLiftStates.group (labelCell A)) (RootedCountIdentification.h A R alpha) (denominator A)

noncomputable def g (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) : Set (Labels A×Bool) → ℝ :=
  secondLift (TwoLiftStates.group (labelCell A)) (RootedCountIdentification.h A R alpha) (denominator A)

end ContingencyTables.RootedFactorialApplication

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedAnnealing
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Adjacent selected-root weights and ideal multipliers

The actual computed-root penalty satisfies the source height bound.
It gives the factor-two annealing estimates for the same literal
completion count used by the executed density evaluator.
-/

namespace ContingencyTables.RootedAnnealing

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication LabelledFactorial
open CompanionAnnealing (scale scale_positive )
open ForestAssignmentSplit
open ForestScaledPenalty (integerCube)
open TwoLiftStates BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def weight (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) : Set (Labels A×Bool) → ℝ :=
  RootedFactorialApplication.f A R ((j:ℝ)/scale A)

theorem weight_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (S : Set (Labels A×Bool)) :
    0< weight A R j S := by
  exact div_pos (mul_pos (RootedCountIdentification.h_positive A R _ _) (FactorialSignatures.factorialProduct_positive _))
    (CompanionFactorialApplication.denominator_positive A)

end ContingencyTables.RootedAnnealing

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

lemma removalSignature_reindex (e : C ≃ D) (F : (D → ℕ) → ℝ) (z : C → ℕ)
    (hs : OnePositiveDirection (integerRemovalMatrix F (z ∘ e.symm)).toBilin') :
    OnePositiveDirection (integerRemovalMatrix (fun x => F (x ∘ e.symm)) z).toBilin' := by
  rw [removalMatrix_reindex]
  apply (signature_iff _ (matrix_bilin_symm _ (by
    intro i j
    exact integerRemoval_symm F (z ∘ e.symm) (e i) (e j)))).mpr
  apply onePositive_submatrix
  exact (signature_iff _ (matrix_bilin_symm _ (integerRemoval_symm F _))).mp hs

lemma removalSlice_reindex (e : C ≃ D) (F : (D → ℕ) → ℝ) (m : D → ℕ) (R : ℕ)
    (hF : RemovalSlice F m R) :
    RemovalSlice (fun x => F (x ∘ e.symm)) (m ∘ e) R := by
  intro z hz ht
  apply removalSignature_reindex
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
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

/-- Remaining balanced marginalization supplies the exposed child
family's positivity and signature on the exact required total slice. -/
theorem exposed_slices {I : Type*} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (U : ℕ) (m : I → ℕ) (R : ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M)
    (hpos : BalancedBox.PositiveSlice F (profile (bounds m Ms) U U) (R+U+Ms.sum))
    (hsig : BalancedBox.RemovalSlice F (profile (bounds m Ms) U U) (R+U+Ms.sum)) :
    BalancedBox.PositiveSlice (exposedFamily Ms F) (profile m U U) (R+U) ∧
      BalancedBox.RemovalSlice (exposedFamily Ms F) (profile m U U) (R+U) := by
  apply eliminate_slices Ms (profile m U U) (R+U) _ hwidth
  · have hp := positiveSlice_reindex (exposeEquiv (I := I) Ms) F (profile (bounds m Ms) U U)
      (R+U+Ms.sum) hpos
    rw [expose_bounds_forward] at hp
    exact hp
  · have hs := removalSlice_reindex (exposeEquiv (I := I) Ms) F (profile (bounds m Ms) U U)
      (R+U+Ms.sum) hsig
    rw [expose_bounds_forward] at hs
    exact hs


end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerLeafEnergy
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

lemma leafEdges_states_adjacent {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (z : I → ℕ) (e : (Coordinates I Ms → ℕ) × (Coordinates I Ms → ℕ))
    (he : e ∈ leafEdges Ms z) :
    e.1 ∈ leafVertices Ms z ∧ e.2 ∈ leafVertices Ms z ∧ IntegerExchangeAdjacent e.1 e.2 := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hi,hj,hij⟩ := (Finset.mem_filter.mp ha).2
  have hv (i : Coordinates I Ms) (h : 0 < embedding Ms z a.1 i) :
      removeOne (embedding Ms z a.1) i ∈ leafVertices Ms z := by
    apply Finset.mem_biUnion.mpr
    refine ⟨a.1,Finset.mem_univ _,?_⟩
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
  exact ⟨hv _ hi,hv _ hj,embedding Ms z a.1,a.2.1,a.2.2,hij,hi,hj,rfl,rfl⟩

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerExchangeArithmetic
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic recognition of unit-exchange edges -/

namespace ContingencyTables.IntegerWeightedTransport
open FactorialSignatures

variable {C : Type*} [DecidableEq C]

lemma exchangeTarget_adjacent (X : C → ℕ) (i j : C)
    (hij : i≠j) (hj : 0<X j) :
    IntegerExchangeAdjacent X (exchangeTarget X i j) := by
  let D : C → ℕ := fun a => X a+if a=i then 1 else 0
  refine ⟨D,i,j,hij,?_,?_,?_,?_⟩
  · simp only [D,ite_true, if_true]
    omega
  · simpa only [D,Ne.symm hij,ite_false,Nat.add_zero] using hj
  · funext a
    simp only [D,removeOne]
    split_ifs <;> omega
  · rfl

/-- The test quantifies only over two coordinates, never over profiles. -/
theorem adjacent_iff_arithmetic (X Y : C → ℕ) :
    IntegerExchangeAdjacent X Y ↔
      ∃ i j,i≠j ∧ 0<X j ∧ Y=exchangeTarget X i j := by
  constructor
  · rintro ⟨D,i,j,hij,hi,hj,rfl,rfl⟩
    refine ⟨i,j,hij,?_,?_⟩
    · simpa only [removeOne,Ne.symm hij,ite_false,Nat.sub_zero] using hj
    · funext a
      unfold exchangeTarget removeOne
      by_cases hai : a=i
      · subst a
        simp only [hij,ite_true, if_true,ite_false,Nat.sub_zero]
        omega
      · by_cases haj : a=j
        · subst a
          simp only [hai,ite_true, if_true,ite_false,Nat.sub_zero,Nat.add_zero]
        · simp only [hai,haj,ite_false,Nat.sub_zero,Nat.add_zero]
  · rintro ⟨i,j,hij,hj,rfl⟩
    exact exchangeTarget_adjacent X i j hij hj

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPhysicalMarginal
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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
open LargePairEnumeration PhysicalLargeProfiles FirstPaperProfiles CompletionCounts
open RowColumnPenalties PaddedCompletions NestedPenaltyApplication BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def softMarginal (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (a : ℝ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) : ℝ :=
  ∑ u : PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2),
    fullSoftFamily small B r c L a
      (physicalProfile (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) z u)

theorem hardMarginal_eq_eliminate (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) {n : ℕ}
    (e : Fin n ≃ LargeCell (fun a : I×J => small a.1 a.2)) :
    hardMarginal small B r c L=
      BalancedFamily.eliminate (widths (fun k => B (e k).val.1 (e k).val.2))
        (fun q => fullHardFamily small B r c L
          (q ∘ (physicalCoordinateEquiv (fun a : I×J => small a.1 a.2) e
            (fun k => B (e k).val.1 (e k).val.2)).symm)) := by
  funext z
  symm
  rw [eliminate_eq_actual_cells (fun a : I×J => small a.1 a.2) e
    (fun k => B (e k).val.1 (e k).val.2) (fullHardFamily small B r c L) z,
    sum_joined_eq_physical (fun a : I×J => small a.1 a.2)
      (fun a : I×J => B a.1 a.2) e z (fullHardFamily small B r c L)]
  unfold hardMarginal
  congr 2
  exact Subsingleton.elim _ _

theorem softMarginal_eq_eliminate (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (a : ℝ) {n : ℕ}
    (e : Fin n ≃ LargeCell (fun a : I×J => small a.1 a.2)) :
    softMarginal small B r c L a=
      BalancedFamily.eliminate (widths (fun k => B (e k).val.1 (e k).val.2))
        (fun q => fullSoftFamily small B r c L a
          (q ∘ (physicalCoordinateEquiv (fun a : I×J => small a.1 a.2) e
            (fun k => B (e k).val.1 (e k).val.2)).symm)) := by
  funext z
  symm
  rw [eliminate_eq_actual_cells (fun a : I×J => small a.1 a.2) e
    (fun k => B (e k).val.1 (e k).val.2) (fullSoftFamily small B r c L a) z,
    sum_joined_eq_physical (fun a : I×J => small a.1 a.2)
      (fun a : I×J => B a.1 a.2) e z (fullSoftFamily small B r c L a)]
  unfold softMarginal
  congr 2
  exact Subsingleton.elim _ _

/-- The literal positive soft count has its raw removal signature on
every required profile box and degree, before taking the hard limit. -/
theorem softMarginal_slices (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (a : ℝ) (ha : 0≤a)
    (m : SmallView (fun a : I×J => small a.1 a.2) → ℕ) (R : ℕ)
    (hwidth : ∀ i j, small i j=false → 2≤B i j) :
    PositiveSlice (softMarginal small B r c L a) m R ∧
      RemovalSlice (softMarginal small B r c L a) m R := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => small a.1 a.2))).symm
  let N := fun k => B (e k).val.1 (e k).val.2
  rw [softMarginal_eq_eliminate small B r c L a e]
  exact NestedReindex.physical_soft_marginal_slices (widths N) m R
    (physicalCoordinateEquiv (fun a : I×J => small a.1 a.2) e N)
    cellLine (smallCoordinate small)
    (fullOffset B (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L)) viewSlope
    (smallOffset small B r c) viewSlope a ha
    (widths_lower N (fun k => hwidth _ _ (e k).property))

theorem softMarginal_tendsto (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) :
    Filter.Tendsto (fun a : ℝ => softMarginal small B r c L a z) Filter.atTop
      (nhds (hardMarginal small B r c L z)) := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => small a.1 a.2))).symm
  simp_rw [softMarginal_eq_eliminate small B r c L _ e,
    hardMarginal_eq_eliminate small B r c L e]
  apply BalancedFamily.eliminate_tendsto
  intro q
  exact softWeight_tendsto cellLine (smallCoordinate small)
    (fullOffset B (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L)) viewSlope
    (smallOffset small B r c) viewSlope _

end ContingencyTables.FirstPaperPhysicalMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerSliceRestriction
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

lemma removalSignature_fixed (F : ((C ⊕ D) → ℕ) → ℝ) (c : C → ℕ) (z : D → ℕ)
    (hs : OnePositiveDirection (integerRemovalMatrix F (Sum.elim c z)).toBilin') :
    OnePositiveDirection (integerRemovalMatrix (fun x => F (Sum.elim c x)) z).toBilin' := by
  rw [removalMatrix_fixed]
  apply (signature_iff _ (matrix_bilin_symm _ (by
    intro i j
    exact integerRemoval_symm F (Sum.elim c z) (.inr i) (.inr j)))).mpr
  apply onePositive_submatrix
  exact (signature_iff _ (matrix_bilin_symm _ (integerRemoval_symm F _))).mp hs

theorem removalSlice_fixed (F : ((C ⊕ D) → ℕ) → ℝ) (mC c : C → ℕ) (mD : D → ℕ)
    (R : ℕ) (hc : InBox mC c)
    (hs : RemovalSlice F (Sum.elim mC mD) ((∑ i, c i)+R)) :
    RemovalSlice (fun x => F (Sum.elim c x)) mD R := by
  intro z hz ht
  apply removalSignature_fixed
  apply hs
  · intro t
    rcases t with i | i
    · exact hc i
    · exact hz i
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ht]
    omega

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerContextSlices
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed context after a physical coordinate bijection -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open BalancedBox

variable {C D S : Type*} [Fintype C] [Fintype D] [Fintype S]
  [DecidableEq C] [DecidableEq D] [DecidableEq S]

theorem context_slices (e : (C ⊕ D) ≃ S) (f : (S → ℕ) → ℝ)
    (mC c : C → ℕ) (mD : D → ℕ) (R : ℕ) (hc : InBox mC c)
    (hp : PositiveSlice f ((Sum.elim mC mD) ∘ e.symm) ((∑ i, c i)+R))
    (hs : RemovalSlice f ((Sum.elim mC mD) ∘ e.symm) ((∑ i, c i)+R)) :
    PositiveSlice (fun x => f ((Sum.elim c x) ∘ e.symm)) mD R ∧
      RemovalSlice (fun x => f ((Sum.elim c x) ∘ e.symm)) mD R := by
  have hpr := positiveSlice_reindex e f _ _ hp
  have hsr := removalSlice_reindex e f _ _ hs
  have hm : ((Sum.elim mC mD) ∘ e.symm) ∘ e=Sum.elim mC mD := by
    funext t
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
  rw [hm] at hpr hsr
  exact ⟨positiveSlice_fixed (fun x => f (x ∘ e.symm)) mC c mD R hc hpr,
    removalSlice_fixed (fun x => f (x ∘ e.symm)) mC c mD R hc hsr⟩

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerRecursivePotential
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

/-- The entire leaf potential is bounded by the root potential minus
the sum of the actual root future forms. All recursive hypotheses are
derived from the original valid total slice. -/
theorem recursivePotential_bound : ∀ (Ms : List ℕ) {I : Type u} [Fintype I] [DecidableEq I]
    (F : (Coordinates I Ms → ℕ) → ℝ) (m z : I → ℕ) (R : ℕ) (h : I → ℝ),
    (∀ U ∈ Ms, 2 ≤ U) → (∀ x, 0 ≤ F x) →
    BalancedBox.PositiveSlice F (bounds m Ms) (R+Ms.sum) →
    BalancedBox.RemovalSlice F (bounds m Ms) (R+Ms.sum) →
    BalancedBox.InBox m z → (∑ i, z i)=R+1 →
    holeLinear (eliminate Ms F) z h=0 →
    recursivePotential Ms F z h ≤ holePotential (eliminate Ms F) z h -
      (integerRemovalMatrix (correctionKernel Ms F) z).toBilin' h h := by
  intro Ms
  induction Ms with
  | nil =>
    intro I _ _ F m z R h _ _ _ _ _ _ _
    change holePotential F z h ≤ holePotential F z h -
      (integerRemovalMatrix (fun _ => 0) z).toBilin' h h
    have hz : integerRemovalMatrix (fun _ : I → ℕ => (0:ℝ)) z=0 := by
      ext i j
      simp [integerRemovalMatrix]
    rw [hz]
    simp
  | cons U Ms ih =>
    intro I _ _ F m z R h hwidth hF hpos hsig hz htotal hbalance
    have hU := hwidth U (by simp)
    have htail : ∀ V ∈ Ms, 2 ≤ V := fun V hV => hwidth V (by simp [hV])
    have hp : BalancedBox.PositiveSlice F (profile (bounds m Ms) U U) (R+U+Ms.sum) := by
      rw [show R+U+Ms.sum=R+(U::Ms).sum by simp only [List.sum_cons]; omega]
      exact hpos
    have hs : BalancedBox.RemovalSlice F (profile (bounds m Ms) U U) (R+U+Ms.sum) := by
      rw [show R+U+Ms.sum=R+(U::Ms).sum by simp only [List.sum_cons]; omega]
      exact hsig
    let f := exposedFamily Ms F
    let G := exposePullback Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    obtain ⟨hfpos,hfsig⟩ := exposed_slices Ms U m R F htail hp hs
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
    have hGpos := expose_source_positive Ms U m R F hp
    have hGsig : BalancedBox.RemovalSlice G (bounds (profile m U U) Ms) (R+U+Ms.sum) := by
      have ht := removalSlice_reindex (exposeEquiv (I := I) Ms) F
        (profile (bounds m Ms) U U) (R+U+Ms.sum) hs
      rw [expose_bounds_forward] at ht
      exact ht
    have hleaves : (∑ j : Fin (U+1), recursivePotential Ms G
        (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))) ≤
        ∑ j : Fin (U+1), (holePotential f (profile z j.val (U-j.val))
          (extendCoefficients h (g j.val) (g (j.val+1))) -
        (integerRemovalMatrix (correctionKernel Ms G) (profile z j.val (U-j.val))).toBilin'
          (extendCoefficients h (g j.val) (g (j.val+1)))
          (extendCoefficients h (g j.val) (g (j.val+1)))) := by
      apply Finset.sum_le_sum
      intro j _
      apply ih G (profile m U U) _ (R+U) _ htail (fun x => hF _) hGpos hGsig
      · exact BalancedBox.profile_inBox m z U j.val (U-j.val) hz
          (by have := j.isLt; omega) (Nat.sub_le _ _)
      · rw [BalancedBox.profile_total, htotal]
        have hj := j.isLt
        omega
      · exact integer_child_balance f z U j.val (by have := j.isLt; omega) h hinner hcum
    have hsplit := integer_split_potential_bound f z U h (by
      intro j hj0 hjU
      apply hfsig
      · exact BalancedBox.profile_inBox m z U j (U+1-j) hz (by omega) (by omega)
      · rw [BalancedBox.profile_total, htotal]
        omega) (by
      intro j hj0 hjU
      apply hfpos
      · exact BalancedBox.profile_inBox m z U (j-1) (U-j) hz (by omega) (Nat.sub_le _ _)
      · rw [BalancedBox.profile_total, htotal]
        omega) hcum
    change (∑ j ∈ Finset.range (U+1), holePotential f (profile z j (U-j))
      (extendCoefficients h (g j) (g (j+1)))) ≤ _ at hsplit
    rw [← weightedFuture_form, exposed_marginal] at hsplit
    rw [← Fin.sum_univ_eq_sum_range (fun j => holePotential f (profile z j (U-j))
      (extendCoefficients h (g j) (g (j+1)))) (U+1)] at hsplit
    have hfuture := correction_future_lower Ms U hU F z h g hF
    rw [Finset.sum_sub_distrib] at hleaves
    change (∑ j : Fin (U+1), recursivePotential Ms G
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))) ≤ _
    rw [correction_form_cons]
    linarith

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerRootTransport
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

/-- The root potential estimate for the actual integer recursion. The
only weight-dependent denominators are its two positive endpoint masses. -/
theorem recursive_root_potential (Ms : List ℕ)
    (F : (Coordinates Bool Ms → ℕ) → ℝ) (m z : Bool → ℕ) (R W : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hF : ∀ x, 0 ≤ F x)
    (hpos : BalancedBox.PositiveSlice F (bounds m Ms) (R+Ms.sum))
    (hsig : BalancedBox.RemovalSlice F (bounds m Ms) (R+Ms.sum))
    (hz : BalancedBox.InBox m z) (htotal : (∑ i, z i)=R+1)
    (hs : 0 < oneHole (eliminate Ms F) z false)
    (ht : 0 < oneHole (eliminate Ms F) z true) :
    let s := oneHole (eliminate Ms F) z false
    let t := oneHole (eliminate Ms F) z true
    let c := integerRemovalMatrix (auxiliaryKernel Ms F) z false true
    recursivePotential Ms F z (rootCoefficients s t) ≤
      1/s+1/t+2*((W:ℝ)+1)^2*c/(s*t) := by
  dsimp only
  have hp := recursivePotential_bound Ms F m z R
    (rootCoefficients _ _) hlower hF hpos hsig hz htotal (root_balance _ _ hs ht)
  rw [root_holePotential _ _ hs ht] at hp
  have hq := root_future_bound (integerRemovalMatrix (correctionKernel Ms F) z)
    (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true)
    (((W:ℝ)+1)^2) (integerRemovalMatrix (auxiliaryKernel Ms F) z false true)
    hs ht (integerRemoval_symm _ _ _ _)
    (removal_nonnegative _ (correctionKernel_nonnegative Ms F hF) _ _ _)
    (removal_nonnegative _ (correctionKernel_nonnegative Ms F hF) _ _ _)
    (correction_offdiagonal_upper Ms F W hupper hF z)
  linarith

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperContextTransport
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Raw transport for the literal first-paper completion counts

An actual small-coordinate bijection isolates a fixed balanced prefix,
the special pair, and the remaining ordinary pairs. Large completions
are still the original physical finite sum; the prefix coordinates are
excluded from every exchange in the transport graph.
-/

namespace ContingencyTables.FirstPaperContextTransport

open scoped BigOperators Classical Topology
open FirstPaperPhysicalMarginal LargePairEnumeration IntegerWeightedTransport
open BalancedFamily BalancedBox

universe u

variable {I J C : Type u} [Fintype I] [Fintype J] [Fintype C]
  [DecidableEq C]

noncomputable def contextSoft (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ : C → ℕ) (a : ℝ) : (Coordinates Bool Ms → ℕ) → ℝ :=
  fun x => softMarginal small B r c L a ((Sum.elim σ x) ∘ e.symm)

omit [Fintype C] [DecidableEq C] in
theorem contextSoft_nonnegative (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ : C → ℕ) (a : ℝ) (x : Coordinates Bool Ms → ℕ) :
    0 ≤ contextSoft small B r c L Ms e σ a x := by
  unfold contextSoft softMarginal
  apply Finset.sum_nonneg
  intro v _
  exact (NestedPenaltyApplication.softWeight_positive _ _ _ _ _ _ _ _).le

/-- The two needed slices are obtained from the physical large-cell
marginal's proved raw signature, then by a principal prefix restriction. -/
theorem contextSoft_slices (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ mC : C → ℕ) (m : Bool → ℕ) (R : ℕ)
    (hprefix : InBox mC σ) (a : ℝ) (ha : 0 ≤ a)
    (hlarge : ∀ i j, small i j=false → 2 ≤ B i j) :
    PositiveSlice (contextSoft small B r c L Ms e σ a) (bounds m Ms) (R+Ms.sum) ∧
      RemovalSlice (contextSoft small B r c L Ms e σ a) (bounds m Ms) (R+Ms.sum) := by
  apply context_slices e (softMarginal small B r c L a) mC σ (bounds m Ms)
    (R+Ms.sum) hprefix
  · exact (softMarginal_slices small B r c L a ha _ _ hlarge).1
  · exact (softMarginal_slices small B r c L a ha _ _ hlarge).2

end ContingencyTables.FirstPaperContextTransport

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
lemma repairMatrix_special {x q : I → J → ℕ} {s t : I×J}
    (h : IsDefect x q s t) :
    repairMatrix x s t s.1 s.2=x s.1 s.2+(if t.1=s.1 then 1 else 0) := by
  apply Int.natCast_inj.mp
  rw [repairMatrix_cast h]
  have hst : ¬(s.1=t.1 ∧ s.2=t.2) := fun hw => h.1 (Prod.ext hw.1 hw.2)
  simp only [transferInt,hst,↓reduceIte,sub_zero,Nat.cast_add]
  by_cases hr : t.1=s.1
  · simp [hr]
  · simp [hr,Ne.symm hr]

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallGraphProfiles
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The physical small graph and contextual unit exchanges -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles FactorialSignatures

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma balanced_not_defect (small : I → J → Bool) (B : I → J → ℕ) (z : SmallProfile small)
    (hb : Balanced small B z) : ¬SingleDefect small B z := by
  rintro ⟨s,t,_,_,hd⟩
  have h := hd.negative_entry
  rw [hb s.1 s.2] at h
  omega

end ContingencyTables.SmallGraphProfiles

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
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles FactorialSignatures

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

omit [LinearOrder I] [LinearOrder J] in
lemma balanced_of_pair_totals (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U) (z : SmallProfile small)
    (hpair : ∀ a : Cells small, z (a,false)+z (a,true)=U) : Balanced small B z := by
  intro i j
  cases hij : small i j
  · simp only [smallView,smallQ,hij,Bool.false_eq_true,↓reduceDIte]
  · have hh := hpair ⟨(i,j),hij⟩
    simp only [smallView,smallQ,hij,dite_eq_left,hB i j hij]
    omega

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

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]
variable (small : I → J → Bool) {n : ℕ} (e : Fin n ≃ Cells small)

lemma indexed_transfer (v : SmallProfile small) (s t : I×J) (i : Fin n) :
    (transferInt (smallView small v false) s t (e i).val.1 (e i).val.2).toNat=
      v (e i,false)+(if i.val=cellIndex small e t then 1 else 0)-
        (if i.val=cellIndex small e s then 1 else 0) := by
  have heta : (⟨((e i).val.1,(e i).val.2),(e i).property⟩ : Cells small)=e i :=
    Subtype.ext (Prod.eta (e i).val)
  simp only [cellIndex_eq]
  simp only [Prod.ext_iff,transferInt,smallView,(e i).property,dite_true,heta]
  split_ifs <;> omega

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RowMajorEnumeration
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

lemma enumeration_before_iff (small : I → J → Bool)
    (a b : Fin (Fintype.card (Cells small))) :
    RowMajorBefore (enumeration small a).val (enumeration small b).val ↔ a<b := by
  change RowMajorBefore (ofLex ((monoEquivOfFin (LexCells small)
    (Fintype.card_congr (lexCellEquiv small))) a).val)
    (ofLex ((monoEquivOfFin (LexCells small)
    (Fintype.card_congr (lexCellEquiv small))) b).val) ↔ a<b
  have hlex : ((monoEquivOfFin (LexCells small) (Fintype.card_congr (lexCellEquiv small))) a).val <
      ((monoEquivOfFin (LexCells small) (Fintype.card_congr (lexCellEquiv small))) b).val ↔ a<b :=
    (monoEquivOfFin (LexCells small) (Fintype.card_congr (lexCellEquiv small))).lt_iff_lt
  exact (Prod.Lex.lt_iff).symm.trans hlex

noncomputable def earlierIndexEquiv (small : I → J → Bool)
    (k : Fin (Fintype.card (Cells small))) :
    Earlier small (enumeration small k).val ≃ {j : Fin (Fintype.card (Cells small)) // j<k} where
  toFun a := ⟨(enumeration small).symm a.val,by
    apply (enumeration_before_iff small _ k).mp
    simpa only [Equiv.apply_symm_apply] using a.property⟩
  invFun a := ⟨enumeration small a.val,(enumeration_before_iff small a.val k).mpr a.property⟩
  left_inv a := Subtype.ext ((enumeration small).apply_symm_apply a.val)
  right_inv a := Subtype.ext ((enumeration small).symm_apply_apply a.val)

noncomputable def laterIndexEquiv (small : I → J → Bool)
    (k : Fin (Fintype.card (Cells small))) :
    Later small (enumeration small k).val ≃ {j : Fin (Fintype.card (Cells small)) // k<j} where
  toFun a := ⟨(enumeration small).symm a.val,by
    apply (enumeration_before_iff small k _).mp
    simpa only [Equiv.apply_symm_apply] using a.property⟩
  invFun a := ⟨enumeration small a.val,(enumeration_before_iff small k a.val).mpr a.property⟩
  left_inv a := Subtype.ext ((enumeration small).apply_symm_apply a.val)
  right_inv a := Subtype.ext ((enumeration small).symm_apply_apply a.val)

noncomputable def earlierEnumeration (small : I → J → Bool)
    (k : Fin (Fintype.card (Cells small))) : Fin k.val ≃ Earlier small (enumeration small k).val :=
  (earlierFinEquiv k).trans (earlierIndexEquiv small k).symm

noncomputable def laterEnumeration (small : I → J → Bool)
    (k : Fin (Fintype.card (Cells small))) :
    Fin (Fintype.card (Cells small)-k.val-1) ≃ Later small (enumeration small k).val :=
  (laterFinEquiv k).trans (laterIndexEquiv small k).symm

end ContingencyTables.RowMajorEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ContextGraphEnergy
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Contextual transport energy embeds in the actual physical graph -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles
open FirstPaperContextTransport FirstPaperPhysicalMarginal

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

def PhysicalPrefix (small : I → J → Bool) (s : I×J) (σ : I×J → ℕ)
    (z : SmallProfile small) : Prop :=
  ∀ a : Earlier small s, z (a.val,false)=σ a.val.val

omit [LinearOrder I] [LinearOrder J] in
lemma hardMarginal_nonnegative (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small) :
    0 ≤ hardMarginal small B r c L z := by
  unfold hardMarginal fullHardFamily NestedPenaltyApplication.hardWeight
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> norm_num

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalPrefixEnergies
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical prefix contexts use each exchange edge at most once -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def prefixValues (small : I → J → Bool) (s : I×J) (U : ℕ)
    (z : SmallProfile small) : Earlier small s → Fin (U+1) :=
  fun a => ⟨min (z (a.val,false)) U,Nat.lt_succ_of_le (min_le_right _ _)⟩

omit [Fintype I] [Fintype J] in
lemma physicalPrefix_iff_values (small : I → J → Bool) (s : I×J) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (z : SmallProfile small)
    (hz : ∀ a : Earlier small s,z (a.val,false) ≤ U) :
    PhysicalPrefix small s (prefixExtension small s U τ) z ↔ prefixValues small s U z=τ := by
  constructor
  · intro hp
    funext a
    apply Fin.ext
    change min (z (a.val,false)) U=(τ a).val
    rw [min_eq_left (hz a),hp a,prefixExtension_at]
  · intro hp a
    have h := congrArg Fin.val (congrFun hp a)
    change min (z (a.val,false)) U=(τ a).val at h
    rw [min_eq_left (hz a)] at h
    rw [prefixExtension_at]
    exact h

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RowMajorPrefixFibres
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Row-major word prefixes are the literal physical exposure contexts -/

namespace ContingencyTables.RowMajorEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily
open ExcessContextProfiles SmallGraphProfiles FiniteExposureVariance IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def earlierWordChoices (small : I → J → Bool) (U : ℕ)
    (k : Fin (Fintype.card (Cells small))) :
    (Fin k.val → Fin (U+1)) ≃ (Earlier small (enumeration small k).val → Fin (U+1)) where
  toFun a := a ∘ (earlierEnumeration small k).symm
  invFun a := a ∘ earlierEnumeration small k
  left_inv a := by funext i; exact congrArg a ((earlierEnumeration small k).symm_apply_apply i)
  right_inv a := by funext i; exact congrArg a ((earlierEnumeration small k).apply_symm_apply i)

lemma earlierEnumeration_cell (small : I → J → Bool) (k : Fin (Fintype.card (Cells small)))
    (j : Fin k.val) :
    (earlierEnumeration small k j).val=enumeration small ⟨j.val,lt_trans j.isLt k.isLt⟩ := rfl

lemma wordChoices_prefix (small : I → J → Bool) (U : ℕ) (k : Fin (Fintype.card (Cells small)))
    (a : Fin (Fintype.card (Cells small)) → Fin (U+1)) :
    earlierChoices small (enumeration small k).val U (wordChoices small U a)=
      earlierWordChoices small U k (restriction k.val (Nat.le_of_lt k.isLt) a) := by
  funext b
  obtain ⟨j,rfl⟩ := (earlierEnumeration small k).surjective b
  change a ((enumeration small).symm (earlierEnumeration small k j).val)=
    restriction k.val (Nat.le_of_lt k.isLt) a ((earlierEnumeration small k).symm (earlierEnumeration small k j))
  rw [earlierEnumeration_cell,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rfl

lemma wordChoices_current (small : I → J → Bool) (U : ℕ) (k : Fin (Fintype.card (Cells small)))
    (a : Fin (Fintype.card (Cells small)) → Fin (U+1)) :
    wordChoices small U a (enumeration small k)=a k := by
  exact congrArg a ((enumeration small).symm_apply_apply k)

lemma word_fibre_sum (small : I → J → Bool) (U : ℕ) (k : Fin (Fintype.card (Cells small)))
    (τ : Fin k.val → Fin (U+1)) (j : Fin (U+1)) (F : (Cells small → Fin (U+1)) → ℝ) :
    (∑ a,fibreWeight (fibreWeight (fun a => F (wordChoices small U a))
      (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j a)=
    ∑ x,fibreWeight (fibreWeight F (earlierChoices small (enumeration small k).val U)
      (earlierWordChoices small U k τ)) (fun x => x (enumeration small k)) j x := by
  apply Fintype.sum_equiv (wordChoices small U)
  intro a
  have hp : earlierChoices small (enumeration small k).val U (wordChoices small U a)=
      earlierWordChoices small U k τ ↔ restriction k.val (Nat.le_of_lt k.isLt) a=τ := by
    rw [wordChoices_prefix]
    exact (earlierWordChoices small U k).apply_eq_iff_eq
  unfold fibreWeight
  dsimp only
  have hc : wordChoices small U a (enumeration small k)=j ↔ a k=j := by
    rw [wordChoices_current]
  by_cases hj : a k=j
  · rw [ite_eq_left hj,ite_eq_left (hc.mpr hj)]
    by_cases hτ : restriction k.val (Nat.le_of_lt k.isLt) a=τ
    · rw [ite_eq_left hτ,ite_eq_left (hp.mpr hτ)]
    · rw [ite_eq_right hτ,ite_eq_right (fun h => hτ (hp.mp h))]
  · rw [ite_eq_right hj,ite_eq_right (fun h => hj (hc.mp h))]

end ContingencyTables.RowMajorEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPhysicalVariance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Poincare inequality on the actual feasible small states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal CompletionCounts SmallContextEnumeration FiniteExposureVariance

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def physicalExtension (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (H : PhysicalStates small B r c L → ℝ) : SmallProfile small → ℝ :=
  Function.extend (physicalProfile small B r c L) H (fun _ => 0)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalResidualMargins
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal padded residual completions of each positive physical state -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Thus the marginal used by the variance proof is exactly the number
of ordinary tables on the large rectangle, including empty rectangles. -/
theorem physical_weight_rectangle (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j) :
    hardMarginal (firstPaperSmall r c U) B r c L (physicalProfile _ B r c L z)=
      (Fintype.card (Table
        (fun i : {i // U ≤ r i} => residualRows (firstPaperSmall r c U) B r c L z i.val)
        (fun j : {j // U ≤ c j} => residualColumns (firstPaperSmall r c U) B r c L z j.val)):ℝ) := by
  rw [physical_weight_completions _ B r c L z hcap]
  convert congrArg (fun n : ℕ => (n:ℝ)) (Fintype.card_congr (rectangleCompletionEquiv (firstPaperSmall r c U)
    (fun i => U ≤ r i) (fun j => U ≤ c j) (firstPaperSmall_false_iff r c U)
    (residualRows _ B r c L z) (residualColumns _ B r c L z)
    (physical_residual_row_zero r c U L B z hcap)
    (physical_residual_column_zero r c U L B z hcap))) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals
    congr 3
    all_goals exact Subsingleton.elim _ _

end ContingencyTables.SmallGraphProfiles

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

lemma exchange_observable_difference (a : C → ℤ) (X Y : C → ℕ)
    (hxy : IntegerExchangeAdjacent X Y) :
    ∃ i j,linearObservable a Y-linearObservable a X=a i-a j := by
  obtain ⟨D,i,j,_,hi,hj,rfl,rfl⟩ := hxy
  refine ⟨i,j,?_⟩
  rw [linearObservable_removeOne a D i hi,linearObservable_removeOne a D j hj]
  ring

theorem exchange_observable_abs_le_two (a : C → ℤ) (ha : ∀ i,|a i| ≤ 1)
    (X Y : C → ℕ) (hxy : IntegerExchangeAdjacent X Y) :
    |linearObservable a Y-linearObservable a X| ≤ 2 := by
  obtain ⟨i,j,he⟩ := exchange_observable_difference a X Y hxy
  rw [he]
  exact (abs_sub _ _).trans (by linarith [ha i,ha j])

theorem exchange_selected_sum_abs_le_two (p : C → Prop) (X Y : C → ℕ)
    (hxy : IntegerExchangeAdjacent X Y) :
    |((∑ k,if p k then Y k else 0:ℕ):ℤ)-((∑ k,if p k then X k else 0:ℕ):ℤ)| ≤ 2 := by
  have ha : ∀ k,|(if p k then 1 else 0:ℤ)| ≤ 1 := by
    intro k
    split_ifs <;> norm_num
  have h := exchange_observable_abs_le_two (fun k => if p k then 1 else 0) ha X Y hxy
  simpa only [linearObservable,ite_mul,one_mul,zero_mul,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero] using h

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallCoordinateSums
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected doubled-coordinate sums are the physical small margins -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles PaddedCompletions
open IntegerWeightedTransport CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def selectedRow (small : I → J → Bool) (z : SmallProfile small) (b : Bool) (i : I) : ℕ :=
  ∑ a,if a.1.val.1=i ∧ a.2=b then z a else 0

noncomputable def selectedColumn (small : I → J → Bool) (z : SmallProfile small) (b : Bool) (j : J) : ℕ :=
  ∑ a,if a.1.val.2=j ∧ a.2=b then z a else 0

omit [LinearOrder I] [LinearOrder J] in
lemma selected_bool_sum (small : I → J → Bool) (z : SmallProfile small) (b : Bool)
    (p : Cells small → Prop) :
    (∑ a : Cells small×Bool,if p a.1 ∧ a.2=b then z a else 0)=
      ∑ a : Cells small,if p a then z (a,b) else 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  cases b <;> simp

omit [LinearOrder I] [LinearOrder J] in
lemma cell_sum_as_matrix (small : I → J → Bool) (z : SmallProfile small) (b : Bool)
    (p : I×J → Prop) :
    (∑ a : Cells small,if p a.val then z (a,b) else 0)=
      ∑ a : I×J,if p a then smallView small z b a.1 a.2 else 0 := by
  have hzero (a : I×J) (ha : ¬small a.1 a.2=true) :
      (if p a then smallView small z b a.1 a.2 else 0)=0 := by
    by_cases hp : p a
    · simp only [hp,ite_true, if_true,smallView,dite_eq_right ha]
    · rw [ite_eq_right hp]
  have he := sum_subtype_eq_of_zero (fun a : I×J => small a.1 a.2=true)
    (fun a => if p a then smallView small z b a.1 a.2 else 0) hzero
  calc
    _ = ∑ a : Cells small,if p a.val then smallView small z b a.val.1 a.val.2 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [smallView,a.property,dite_eq_left]
    _ = _ := by
      convert he using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      exact Subsingleton.elim _ _

omit [LinearOrder J] in
lemma selectedRow_eq (small : I → J → Bool) (z : SmallProfile small) (b : Bool) (i : I) :
    selectedRow small z b i=∑ j,smallView small z b i j := by
  unfold selectedRow
  have hb : (∑ a,if a.1.val.1=i ∧ a.2=b then z a else 0)=
      ∑ a : Cells small,if a.val.1=i then z (a,b) else 0 := by
    convert selected_bool_sum small z b (fun a => a.val.1=i) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals
      congr 4
      first | exact Subsingleton.elim _ _ | (funext a; split_ifs <;> rfl)
  rw [hb]
  have hc : (∑ a : Cells small,if a.val.1=i then z (a,b) else 0)=
      ∑ a : I×J,if a.1=i then smallView small z b a.1 a.2 else 0 := by
    convert cell_sum_as_matrix small z b (fun a => a.1=i) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals
      congr 4
      first | exact Subsingleton.elim _ _ | (funext a; split_ifs <;> rfl)
  rw [hc,Fintype.sum_prod_type]
  simp_rw [Finset.sum_ite_irrel]
  simp

omit [LinearOrder I] in
lemma selectedColumn_eq (small : I → J → Bool) (z : SmallProfile small) (b : Bool) (j : J) :
    selectedColumn small z b j=∑ i,smallView small z b i j := by
  unfold selectedColumn
  have hb : (∑ a,if a.1.val.2=j ∧ a.2=b then z a else 0)=
      ∑ a : Cells small,if a.val.2=j then z (a,b) else 0 := by
    convert selected_bool_sum small z b (fun a => a.val.2=j) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals
      congr 4
      first | exact Subsingleton.elim _ _ | (funext a; split_ifs <;> rfl)
  rw [hb]
  have hc : (∑ a : Cells small,if a.val.2=j then z (a,b) else 0)=
      ∑ a : I×J,if a.2=j then smallView small z b a.1 a.2 else 0 := by
    convert cell_sum_as_matrix small z b (fun a => a.2=j) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals
      congr 4
      first | exact Subsingleton.elim _ _ | (funext a; split_ifs <;> rfl)
  rw [hc,Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [Finset.sum_ite_irrel]
  simp

omit [LinearOrder J] in
lemma selectedRow_eq_smallRow (small : I → J → Bool) (z : SmallProfile small) (i : I) :
    selectedRow small z false i=smallRow small (smallView small z false) i := by
  rw [selectedRow_eq]
  unfold smallRow
  apply Finset.sum_congr rfl
  intro j _
  cases hs : small i j <;> simp [smallView,hs]

omit [LinearOrder I] in
lemma smallColumn_cast_selected (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (hz : ∀ a,z a ≤ B a.1.val.1 a.1.val.2) (j : J) :
    (smallColumn small B (smallView small z true) j:ℤ)=
      (∑ i,if small i j then (B i j:ℤ) else 0)-(selectedColumn small z true j:ℤ) := by
  rw [selectedColumn_eq]
  unfold smallColumn
  rw [Nat.cast_sum,Nat.cast_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : small i j=true
  · have hb := hz (⟨(i,j),hs⟩,true)
    simp only [hs,ite_true, if_true,smallView,dite_eq_left]
    exact Nat.cast_sub hb
  · simp only [smallView,dite_eq_right hs,ite_eq_right hs,Nat.cast_zero,sub_zero]

lemma exchange_smallRow_abs (small : I → J → Bool) (X Y : SmallProfile small)
    (hxy : IntegerExchangeAdjacent X Y) (i : I) :
    |(smallRow small (smallView small Y false) i:ℤ)-smallRow small (smallView small X false) i| ≤ 2 := by
  rw [← selectedRow_eq_smallRow,← selectedRow_eq_smallRow]
  unfold selectedRow
  convert exchange_selected_sum_abs_le_two (fun a => a.1.val.1=i ∧ a.2=false) X Y hxy using 1
  all_goals try with_reducible_and_instances rfl
  congr 5 <;> first | exact Subsingleton.elim _ _ | (funext a; split_ifs <;> rfl)

lemma exchange_smallColumn_abs (small : I → J → Bool) (B : I → J → ℕ)
    (X Y : SmallProfile small) (hX : ∀ a,X a ≤ B a.1.val.1 a.1.val.2)
    (hY : ∀ a,Y a ≤ B a.1.val.1 a.1.val.2)
    (hxy : IntegerExchangeAdjacent X Y) (j : J) :
    |(smallColumn small B (smallView small Y true) j:ℤ)-smallColumn small B (smallView small X true) j| ≤ 2 := by
  rw [smallColumn_cast_selected small B Y hY,smallColumn_cast_selected small B X hX]
  have he : (∑ i,if small i j then (B i j:ℤ) else 0)-(selectedColumn small Y true j:ℤ)-
      ((∑ i,if small i j then (B i j:ℤ) else 0)-(selectedColumn small X true j:ℤ))=
      -((selectedColumn small Y true j:ℤ)-selectedColumn small X true j) := by ring
  rw [he,abs_neg]
  unfold selectedColumn
  convert exchange_selected_sum_abs_le_two (fun a => a.1.val.2=j ∧ a.2=true) X Y hxy using 1
  all_goals try with_reducible_and_instances rfl
  congr 5 <;> first | exact Subsingleton.elim _ _ | (funext a; split_ifs <;> rfl)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalExchangeMargins
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual padded residual margins change by at most two on exchange edges -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions SmallContextFibres IntegerWeightedTransport

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma exchange_residual_margins (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (x y : PhysicalStates small B r c L)
    (hxcap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L x k) ≤ B i j)
    (hycap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L y k) ≤ B i j)
    (hxy : IntegerExchangeAdjacent (physicalProfile small B r c L x) (physicalProfile small B r c L y)) :
    (∀ i,|(residualRows small B r c L y i:ℤ)-residualRows small B r c L x i| ≤ 2) ∧
    (∀ j,|(residualColumns small B r c L y j:ℤ)-residualColumns small B r c L x j| ≤ 2) := by
  have hx := physical_original_residuals small B r c L x hxcap
  have hy := physical_original_residuals small B r c L y hycap
  constructor
  · intro i
    unfold residualRows
    rw [nat_residual_difference _ _ _ _ (hy.1 i) (hx.1 i)]
    exact exchange_smallRow_abs small _ _ hxy i
  · intro j
    unfold residualColumns
    rw [nat_residual_difference _ _ _ _ (hy.2 j) (hx.2 j)]
    exact exchange_smallColumn_abs small B _ _ (naturalProfile_bounded x.val.val)
      (naturalProfile_bounded y.val.val) hxy j

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RepairLargeMass
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A repair adds at most one unit outside the retained small cells -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles SmallContextFibres PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [Fintype I] [Fintype J] in
lemma repair_large_value (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (ht : small t.1 t.2=true) (i : I) (j : J) (hij : small i j=false) :
    repairMatrix (smallView small z false) s t i j = if i=t.1 ∧ j=s.2 then 1 else 0 := by
  have hne : ¬(i=t.1 ∧ j=t.2) := by
    rintro ⟨rfl,rfl⟩
    rw [ht] at hij
    contradiction
  have he := repairMatrix_cast hd i j
  have hz : smallView small z false i j=0 := by simp [smallView,hij]
  simp only [transferInt,hz,ite_eq_right hne,Nat.cast_zero,sub_zero,zero_add] at he
  split_ifs at he ⊢ <;> omega

omit [Fintype I] in
lemma repair_large_row_le_one (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (ht : small t.1 t.2=true) (i : I) :
    largeRow small (repairMatrix (smallView small z false) s t) i ≤ 1 := by
  unfold largeRow
  calc
    _ ≤ ∑ j : J,if j=s.2 then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      cases hs : small i j
      · rw [ite_eq_right Bool.false_ne_true,repair_large_value small B z s t hd ht i j hs]
        split_ifs <;> simp_all
      · simp only [ite_true, if_true]
        split_ifs <;> simp_all
    _ = _ := by simp

omit [Fintype J] in
lemma repair_large_column_le_one (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (ht : small t.1 t.2=true) (j : J) :
    largeColumnView small (repairMatrix (smallView small z false) s t) j ≤ 1 := by
  unfold largeColumnView
  calc
    _ ≤ ∑ i : I,if i=t.1 then 1 else 0 := by
      apply Finset.sum_le_sum
      intro i _
      cases hs : small i j
      · rw [ite_eq_right Bool.false_ne_true,repair_large_value small B z s t hd ht i j hs]
        split_ifs <;> simp_all
      · simp only [ite_true, if_true]
        split_ifs <;> simp_all
    _ = _ := by simp

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RepairSmallMargins
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained small margins change by at most one under repair -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles SmallContextFibres SmallContextCoordinates PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [Fintype J] [LinearOrder I] [LinearOrder J] in
lemma smallQ_column_sum (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (j : J) :
    (∑ i,smallQ small B z i j)=smallColumn small B (smallView small z true) j := by
  unfold smallColumn
  apply Finset.sum_congr rfl
  intro i _
  cases hs : small i j <;> simp [smallQ,smallView,hs]

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ReferenceCompletionBlock
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed reference row and column for the physical completion blocks -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- A single pair of reference indices, fixed independently of the state,
reindexes every actual completion block and retains its exact count. -/
theorem physical_weight_reference_block (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j) :
    hardMarginal (firstPaperSmall r c U) B r c L (physicalProfile _ B r c L z)=
      (Fintype.card (Table (referenceRows r c U L B i₀ z) (referenceColumns r c U L B j₀ z)):ℝ) := by
  rw [physical_weight_rectangle r c U L B z hcap]
  convert congrArg (fun n : ℕ => (n:ℝ)) (Fintype.card_congr
    (tableReindex (Equiv.optionSubtypeNe i₀) (Equiv.optionSubtypeNe j₀)
      (fun i : LargeRows r U => residualRows (firstPaperSmall r c U) B r c L z i.val)
      (fun j : LargeColumns c U => residualColumns (firstPaperSmall r c U) B r c L z j.val))) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals congr 3

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalMassBound
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Count the small state and its large completion jointly -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres PhysicalLargeProfiles FirstPaperPhysicalMarginal
open SmallContextFibres LargePairEnumeration CompletionCounts NestedPenaltyApplication

universe u
variable {I J : Type u} [Fintype I] [Fintype J]

lemma hardMarginal_le_assignments (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small) :
    hardMarginal small B r c L z ≤
      (Fintype.card (PhysicalAssignments (fun a : I×J => small a.1 a.2)
        (fun a => B a.1 a.2)):ℝ) := by
  unfold hardMarginal fullHardFamily hardWeight
  rw [Finset.sum_boole,← Fintype.card_subtype]
  exact_mod_cast Fintype.card_subtype_le _

lemma boundedProfile_card_le (small : I → J → Bool) (B : I → J → ℕ)
    (C : ℕ) (hB : ∀ i j,B i j ≤ C) :
    Fintype.card (BoundedProfile small B) ≤
      (C+1)^Fintype.card (SmallView (fun a : I×J => small a.1 a.2)) := by
  change Fintype.card ((a : SmallView (fun a : I×J => small a.1 a.2)) →
    Fin (B a.1.val.1 a.1.val.2+1)) ≤ _
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∏ _a : SmallView (fun a : I×J => small a.1 a.2),(C+1) :=
      Finset.prod_le_prod' (fun a _ => Nat.add_le_add_right (hB _ _) 1)
    _ = _ := by simp

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
open CommonBasesFPRAS PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open SmallContextFibres

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [LinearOrder I] [LinearOrder J] in
lemma stateCapacity_le_bound (r : I → ℕ) (c : J → ℕ) (i : I) (j : J) :
    stateCapacity r c i j ≤ stateBound r c := by
  unfold stateCapacity paperCapacity stateBound
  split_ifs <;> omega

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalChainCast
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent rational walks agree with their real finite kernels -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture CommonBasesFPRAS

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem walkLaw_cast_kernel (K : X → RationalLaw X) (C : FiniteChain X)
    (hK : ∀ x y,((K x).mass y:ℝ)=C.P x y) (n : ℕ) (x y : X) :
    ((walkLaw K x n).mass y:ℝ)=(C.kernel.power n).P x y := by
  induction n generalizing y with
  | zero =>
    simp only [walkLaw,pointLaw,FiniteKernel.power,FiniteKernel.identity]
    by_cases hxy : x=y
    · subst y; simp
    · simp [hxy,Ne.symm hxy]
  | succ n ih =>
    change ((∑ z,(walkLaw K x n).mass z*(K z).mass y:ℚ):ℝ)=_
    simp only [Rat.cast_sum,Rat.cast_mul,ih,hK,
      FiniteKernel.power,FiniteKernel.comp,FiniteChain.kernel]

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSuccessRatio
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The stationary successful-pair ratio of the first sampler -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open FirstPaperPhysicalMarginal PhysicalCompletionFibres PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]


lemma paper_padded_count_le (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i,r i=∑ j,c j) (hd : 14 ≤ dimensionAllowance (I := I) (J := J)) :
    (Fintype.card (Table
      (fun i => r i+rowLargeCount (paperSmall r c) i*((dimensionAllowance (I := I) (J := J))^12))
      (fun j => c j+columnLargeCount (paperSmall r c) j*((dimensionAllowance (I := I) (J := J))^12))):ℝ) ≤
      2*(Fintype.card (Table r c):ℝ) := by
  let d := dimensionAllowance (I := I) (J := J)
  let K := paperLarge r c
  have hK : K.card ≤ d :=
    (Finset.card_filter_le _ _).trans (by simpa only [Finset.card_univ,Fintype.card_prod] using
      (dimension_le_allowance (I := I) (J := J)))
  have hrow : ∀ p ∈ K,d^20 ≤ r p.1 := by
    intro p hp
    exact ((firstPaperSmall_false_iff r c _ _ _).mp (Finset.mem_filter.mp hp).2).1
  have hcol : ∀ p ∈ K,d^20 ≤ c p.2 := by
    intro p hp
    exact ((firstPaperSmall_false_iff r c _ _ _).mp (Finset.mem_filter.mp hp).2).2
  have hr : Fintype.card I ≤ d := by dsimp only [d]; unfold dimensionAllowance; nlinarith
  have hc : Fintype.card J ≤ d := by dsimp only [d]; unfold dimensionAllowance; nlinarith
  have h := padding_success_half r c htotal K d hd hr hc hK hrow hcol
  have htotal' : ∑ i,paddedRows r (largePadding K (d^12)) i=
      ∑ j,paddedColumns c (largePadding K (d^12)) j := by
    unfold paddedRows paddedColumns
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,htotal,Finset.sum_comm]
  have hpos : (0:ℝ) < Fintype.card
      (Table (paddedRows r (largePadding K (d^12))) (paddedColumns c (largePadding K (d^12)))) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (table_nonempty _ _ htotal')
  have hh := (le_div_iff₀ hpos).mp h
  simp only [Fintype.card_eq_nat_card] at hh ⊢
  dsimp only [K,paperLarge] at hh
  rw [large_padding_rows,large_padding_columns] at hh
  change (Nat.card (Table (fun i => r i+rowLargeCount (paperSmall r c) i*d^12)
    (fun j => c j+columnLargeCount (paperSmall r c) j*d^12)):ℝ) ≤ 2*Nat.card (Table r c)
  linarith

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_InverseSmallRepair
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit arithmetic inverse of each labelled repair -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]

/-- Undo the row transfer, using only additions, subtractions and tests
against the two specified cells. -/
def inverseRepairRow (small : I → J → Bool) (v : SmallProfile small) (s t : I×J)
    (i : I) (j : J) : ℕ :=
  (transferInt (smallView small v false) (t.1,s.2) t i j).toNat

def inverseRepairProfile (small : I → J → Bool) (B : I → J → ℕ)
    (v : SmallProfile small) (s t : I×J) : SmallProfile small := fun a =>
  if a.2 then B a.1.val.1 a.1.val.2-
    (transferInt (inverseRepairRow small v s t) t s a.1.val.1 a.1.val.2).toNat
  else inverseRepairRow small v s t a.1.val.1 a.1.val.2

end
end ContingencyTables.SmallGraphProfiles

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
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]
variable (small : I → J → Bool) (B : I → J → ℕ) (z : SmallProfile small)

omit [LinearOrder I] [LinearOrder J] in
lemma view_at_cell (a : Cells small) (b : Bool) :
    smallView small z b a.val.1 a.val.2=z (a,b) := by
  have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
  simp only [smallView,a.property,dite_true,heta]

omit [LinearOrder I] [LinearOrder J] in
lemma q_at_cell (a : Cells small) :
    smallQ small B z a.val.1 a.val.2=B a.val.1 a.val.2-z (a,true) := by
  have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
  simp only [smallQ,a.property,dite_true,heta]

def CellSumBalanced : Prop :=
  ∀ a : Cells small,z (a,false)+z (a,true)=B a.val.1 a.val.2

def CellSumDefect (s t : Cells small) : Prop :=
  s≠t ∧ ∀ a : Cells small,
    z (a,false)+z (a,true)+(if a=s then 1 else 0)=
      B a.val.1 a.val.2+(if a=t then 1 else 0)

omit [LinearOrder I] [LinearOrder J] in
theorem balanced_iff_cellSums
    (hb : ∀ a : Cells small,z (a,true)≤B a.val.1 a.val.2) :
    Balanced small B z ↔ CellSumBalanced small B z := by
  constructor
  · intro h a
    have ha := h a.val.1 a.val.2
    rw [view_at_cell,q_at_cell] at ha
    have hba := hb a
    omega
  · intro h i j
    by_cases hs : small i j=true
    · let a : Cells small := ⟨(i,j),hs⟩
      have ha : z (a,false)+z (a,true)=B i j := h a
      simp only [smallView,smallQ,hs,dite_true]
      change z (a,false)=B i j-z (a,true)
      omega
    · simp [smallView,smallQ,hs]

/-- On bounded coordinates the signed defect equation is precisely an
equality of nonnegative integer sums. This avoids truncated subtraction
in the executable profile-pattern test. -/
theorem defect_iff_cellSums
    (hb : ∀ a : Cells small,z (a,true)≤B a.val.1 a.val.2)
    (s t : Cells small) :
    IsDefect (smallView small z false) (smallQ small B z) s.val t.val ↔
      CellSumDefect small B z s t := by
  constructor
  · intro h
    refine ⟨fun he => h.1 (congrArg Subtype.val he),?_⟩
    intro a
    have ha := h.2 a.val.1 a.val.2
    have hba := hb a
    simp only [transferInt,view_at_cell,q_at_cell,←cell_eq_coordinates] at ha
    split_ifs at ha ⊢ <;> omega
  · rintro ⟨hne,h⟩
    refine ⟨fun he => hne (Subtype.ext he),?_⟩
    intro i j
    by_cases hs : small i j=true
    · let a : Cells small := ⟨(i,j),hs⟩
      have ha := h a
      have hba := hb a
      simp only [cell_eq_coordinates] at ha
      dsimp only [a] at ha hba
      simp only [smallQ,smallView,transferInt,hs,dite_true]
      split_ifs at ha ⊢ <;> omega
    · have hns : ¬(i=s.val.1 ∧ j=s.val.2) := by
        rintro ⟨rfl,rfl⟩
        exact hs s.property
      have hnt : ¬(i=t.val.1 ∧ j=t.val.2) := by
        rintro ⟨rfl,rfl⟩
        exact hs t.property
      simp only [smallQ,smallView,transferInt,hs,hns,hnt,ite_false]
      norm_num

/-- An allowed profile is detected by one balanced test or by one of
the ordered cell-pair tests. This uses at most quadratically many labels. -/
theorem pattern_iff_cellSums
    (hb : ∀ a : Cells small,z (a,true)≤B a.val.1 a.val.2) :
    Pattern small B z ↔ CellSumBalanced small B z ∨
      ∃ s t : Cells small,CellSumDefect small B z s t := by
  constructor
  · rintro (h|⟨s,t,hs,ht,hd⟩)
    · exact Or.inl ((balanced_iff_cellSums small B z hb).mp h)
    · exact Or.inr ⟨⟨s,hs⟩,⟨t,ht⟩,(defect_iff_cellSums small B z hb _ _).mp hd⟩
  · rintro (h|⟨s,t,h⟩)
    · exact Or.inl ((balanced_iff_cellSums small B z hb).mpr h)
    · exact Or.inr ⟨s.val,t.val,s.property,t.property,
        (defect_iff_cellSums small B z hb s t).mpr h⟩

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

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres ProfilePrograms

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]

/-- The binary list test recognizes exactly the manuscript's profile
patterns on the common small-cell box. -/
theorem patternTest_views (small : I → J → Bool) (B : I → J → ℕ)
    {n : ℕ} (e : Fin n ≃ Cells small) (z : SmallProfile small) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U)
    (hb : ∀ a : Cells small,z (a,true)≤B a.val.1 a.val.2) :
    patternTest ((viewList small e z false,viewList small e z true),U)=true ↔
      Pattern small B z := by
  rw [viewList,viewList,patternTest_ofFn,pattern_iff_cellSums small B z hb]
  constructor
  · rintro (h|⟨s,t,hne,h⟩)
    · left
      intro a
      simpa only [Equiv.apply_symm_apply,hU] using h (e.symm a)
    · right
      refine ⟨e s,e t,fun he => hne (e.injective he),?_⟩
      intro a
      have hs : e.symm a=s ↔ a=e s := by
        constructor
        · intro he; rw [←he,Equiv.apply_symm_apply]
        · intro he; rw [he,Equiv.symm_apply_apply]
      have ht : e.symm a=t ↔ a=e t := by
        constructor
        · intro he; rw [←he,Equiv.apply_symm_apply]
        · intro he; rw [he,Equiv.symm_apply_apply]
      simpa only [Equiv.apply_symm_apply,hU,hs,ht] using h (e.symm a)
  · rintro (h|⟨s,t,hne,h⟩)
    · left
      intro i
      simpa only [hU] using h (e i)
    · right
      refine ⟨e.symm s,e.symm t,fun he => hne (e.symm.injective he),?_⟩
      intro i
      have hs : e i=s ↔ i=e.symm s := by
        constructor
        · intro he; rw [←he,Equiv.symm_apply_apply]
        · intro he; rw [he,Equiv.apply_symm_apply]
      have ht : e i=t ↔ i=e.symm t := by
        constructor
        · intro he; rw [←he,Equiv.symm_apply_apply]
        · intro he; rw [he,Equiv.apply_symm_apply]
      simpa only [hU,hs,ht] using h (e i)

end
end ContingencyTables.SmallGraphProfiles

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

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem boundedValues_views (z : SmallProfile small) (U : ℕ) :
    (boundedValues (U,viewList small e z false) &&
      boundedValues (U,viewList small e z true))=true ↔ ∀ a,z a≤U := by
  simp only [Bool.and_eq_true,viewList,boundedValues_ofFn]
  constructor
  · rintro ⟨hx,hy⟩ ⟨a,b⟩
    cases b
    · simpa only [e.apply_symm_apply] using hx (e.symm a)
    · simpa only [e.apply_symm_apply] using hy (e.symm a)
  · intro h
    exact ⟨fun i => h (e i,false),fun i => h (e i,true)⟩

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallViewLookupProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial lookup of the sparse small-cell view -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

/-- Missing large cells yield zero, exactly as required by `smallView`. -/
theorem lookupView_eq (z : SmallProfile small) (b : Bool) (i : Fin m) (j : Fin n) :
    lookupView ((cellCatalog small e,viewList small e z b),(i.val,j.val))=
      smallView small z b i j := by
  unfold lookupView
  rw [cellCatalog_index small e (i,j)]
  by_cases hs : small i j=true
  · simp only [cellIndex,dite_eq_left hs,viewList,List.getD_eq_getElem?_getD,
      List.getElem?_ofFn,(e.symm ⟨(i,j),hs⟩).isLt,dite_true,Option.getD_some,
      smallView]
    change z (e (e.symm ⟨(i,j),hs⟩),b)=z (⟨(i,j),hs⟩,b)
    rw [Equiv.apply_symm_apply]
  · simp only [cellIndex,dite_eq_right hs,viewList,List.getD_eq_getElem?_getD,
      List.getElem?_ofFn,lt_self_iff_false,dite_false,Option.getD_none,smallView]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallLineSumProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary row and column sums of the sparse stored view -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem rowSum_eq (z : SmallProfile small) (b : Bool) (c : Fin n → ℕ) (i : Fin m) :
    lineSum true (((cellCatalog small e,viewList small e z b),List.ofFn c),i.val)=
      ∑ j,smallView small z b i j := by
  apply lineSum_eq_sum true _ List.length_ofFn
  intro j
  exact lookupView_eq small e z b i j

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallComplementProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the complemented small column view -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open PaddedCompletions ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

/-- The arithmetic complement needs no underflow assumption: it agrees
with the natural subtraction already present in the physical view. -/
theorem lookupComplement_eq (B : Fin m → Fin n → ℕ) (z : SmallProfile small) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U) (i : Fin m) (j : Fin n) :
    lookupView ((cellCatalog small e,complementValues (U,viewList small e z true)),(i.val,j.val))=
      smallQ small B z i j := by
  let v : SmallProfile small := fun a => U-z (a.1,true)
  have hc : complementValues (U,viewList small e z true)=viewList small e v false := by
    simp only [viewList,complementValues_ofFn]
    rfl
  rw [hc,lookupView_eq]
  by_cases hs : small i j=true
  · simp only [smallView,smallQ,hs,dite_true,v,hU ⟨(i,j),hs⟩]
  · simp [smallView,smallQ,hs]

theorem complementedColumnSum_eq (B : Fin m → Fin n → ℕ) (z : SmallProfile small)
    (U : ℕ) (hU : ∀ a : Cells small,B a.val.1 a.val.2=U)
    (r : Fin m → ℕ) (j : Fin n) :
    lineSum false (((cellCatalog small e,complementValues (U,viewList small e z true)),
      List.ofFn r),j.val)=smallColumn small B (smallView small z true) j := by
  have he : lineSum false (((cellCatalog small e,complementValues (U,viewList small e z true)),
      List.ofFn r),j.val)=∑ i,smallQ small B z i j := by
    apply lineSum_eq_sum false _ List.length_ofFn
    intro i
    exact lookupComplement_eq small e B z U hU i j
  rw [he]
  unfold smallColumn
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : small i j=true
  · simp only [smallQ,smallView,hs,dite_true,ite_true, if_true]
  · simp [smallQ,hs]

theorem storedRowSum_eq (z : SmallProfile small) (c : Fin n → ℕ) (i : Fin m) :
    lineSum true (((cellCatalog small e,viewList small e z false),List.ofFn c),i.val)=
      smallRow small (smallView small z false) i := by
  rw [rowSum_eq]
  unfold smallRow
  apply Finset.sum_congr rfl
  intro j _
  by_cases hs : small i j=true
  · simp only [hs,ite_true, if_true]
  · simp [smallView,hs]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallResidualTotals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conservation makes the residual-total test redundant -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextFibres FirstPaperProfiles PaddedCompletions CompletionCounts
open FirstPaperPhysicalMarginal PhysicalCompletionFibres

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma pattern_view_totals (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (hz : Pattern small B z) :
    (∑ i,∑ j,smallView small z false i j)=∑ i,∑ j,smallQ small B z i j := by
  rcases hz with h|⟨s,t,_,_,h⟩
  · change ∀ i j,smallView small z false i j=smallQ small B z i j at h
    simp_rw [h]
  · apply Int.natCast_inj.mp
    simp only [Nat.cast_sum]
    symm
    simp_rw [h.2,transferInt]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,ite_and]
    simp

lemma pattern_small_totals (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (hz : Pattern small B z) :
    (∑ i,smallRow small (smallView small z false) i)=
      ∑ j,smallColumn small B (smallView small z true) j := by
  have hrow (i : I) : smallRow small (smallView small z false) i=
      ∑ j,smallView small z false i j := by
    unfold smallRow
    apply Finset.sum_congr rfl
    intro j _
    by_cases hs : small i j=true
    · simp only [hs,ite_true, if_true]
    · simp [smallView,hs]
  have hcol (j : J) : smallColumn small B (smallView small z true) j=
      ∑ i,smallQ small B z i j := by
    unfold smallColumn
    apply Finset.sum_congr rfl
    intro i _
    by_cases hs : small i j=true <;> simp [smallQ,smallView,hs]
  simp_rw [hrow,hcol]
  exact (pattern_view_totals small B z hz).trans Finset.sum_comm

lemma padded_residual_totals (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (hz : Pattern small B z)
    (hr : ∀ i,smallRow small (smallView small z false) i ≤ r i)
    (hc : ∀ j,smallColumn small B (smallView small z true) j ≤ c j) :
    (∑ i,((r i-smallRow small (smallView small z false) i)+rowLargeCount small i*L))=
      ∑ j,((c j-smallColumn small B (smallView small z true) j)+columnLargeCount small j*L) := by
  have hs := pattern_small_totals small B z hz
  have hlarge : (∑ i,rowLargeCount small i)=∑ j,columnLargeCount small j := by
    unfold rowLargeCount columnLargeCount
    exact Finset.sum_comm
  have hrt (i : I) : ((r i-smallRow small (smallView small z false) i:ℕ):ℤ)=
      (r i:ℤ)-(smallRow small (smallView small z false) i:ℤ) := Nat.cast_sub (hr i)
  have hct (j : J) : ((c j-smallColumn small B (smallView small z true) j:ℕ):ℤ)=
      (c j:ℤ)-(smallColumn small B (smallView small z true) j:ℤ) := Nat.cast_sub (hc j)
  apply Int.natCast_inj.mp
  simp only [Nat.cast_sum,Nat.cast_add,Nat.cast_mul]
  simp_rw [hrt,hct]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,←Nat.cast_sum]
  rw [htotal,hs,hlarge]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallMarginSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executable margin tests characterize physical feasibility -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open PaddedCompletions ProfilePrograms FirstPaperPhysicalMarginal

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem validRows_iff (z : SmallProfile small) (r : Fin m → ℕ) (c : Fin n → ℕ) (U : ℕ) :
    validMargins true (((cellCatalog small e,viewList small e z false),
      (List.ofFn r,List.ofFn c)),U)=true ↔
      ∀ i,smallRow small (smallView small z false) i ≤ r i ∧
        (r i<U → smallRow small (smallView small z false) i=r i) := by
  rw [validMargins_iff]
  simp only [marginList,ite_true, if_true,List.length_ofFn]
  constructor
  · intro h i
    have hi := h i.val i.isLt
    simpa only [lineArgument,Bool.not_true,marginList,Bool.false_eq_true,ite_false,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,
      Fin.eta,storedRowSum_eq] using hi
  · intro h i hi
    have hh := h ⟨i,hi⟩
    have he := storedRowSum_eq small e z c (⟨i,hi⟩ : Fin m)
    simpa only [lineArgument,Bool.not_true,marginList,Bool.false_eq_true,ite_false,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hi,Option.getD_some,
      ←he] using hh

theorem validColumns_iff (B : Fin m → Fin n → ℕ) (z : SmallProfile small)
    (r : Fin m → ℕ) (c : Fin n → ℕ) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U) :
    validMargins false (((cellCatalog small e,complementValues (U,viewList small e z true)),
      (List.ofFn r,List.ofFn c)),U)=true ↔
      ∀ j,smallColumn small B (smallView small z true) j ≤ c j ∧
        (c j<U → smallColumn small B (smallView small z true) j=c j) := by
  rw [validMargins_iff]
  simp only [marginList,Bool.false_eq_true,ite_false,List.length_ofFn]
  constructor
  · intro h j
    have hj := h j.val j.isLt
    simpa only [lineArgument,Bool.not_false,marginList,ite_true, if_true,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left j.isLt,Option.getD_some,
      Fin.eta,complementedColumnSum_eq small e B z U hU] using hj
  · intro h j hj
    have hh := h ⟨j,hj⟩
    have he := complementedColumnSum_eq small e B z U hU r (⟨j,hj⟩ : Fin n)
    simpa only [lineArgument,Bool.not_false,marginList,ite_true, if_true,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hj,Option.getD_some,
      ←he] using hh

end
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
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles ProfilePrograms
open IntegerWeightedTransport

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

lemma flatten_profileCode (z : SmallProfile small) :
    flattenViews (profileCode small e z)=List.ofFn (fun i => z (flatViewEquiv small e i)) := by
  rw [List.ofFn_add]
  unfold flattenViews profileCode viewList
  congr 1
  · apply congrArg List.ofFn
    funext i
    change z (e i,false)=z (sumViewEquiv small e (finSumFinEquiv.symm (Fin.castAdd q i)))
    rw [finSumFinEquiv_symm_apply_castAdd]
    rfl
  · apply congrArg List.ofFn
    funext i
    change z (e i,true)=z (sumViewEquiv small e (finSumFinEquiv.symm (Fin.natAdd q i)))
    rw [finSumFinEquiv_symm_apply_natAdd]
    rfl

theorem codeExchange_eq (z : SmallProfile small) (i j : Fin (q+q)) :
    codeExchange (profileCode small e z,(i.val,j.val))=
      profileCode small e (exchangeTarget z (flatViewEquiv small e i) (flatViewEquiv small e j)) := by
  have he : exchangeTarget (fun a => z (flatViewEquiv small e a)) i j=
      fun a => exchangeTarget z (flatViewEquiv small e i) (flatViewEquiv small e j)
        (flatViewEquiv small e a) := by
    funext a
    simp only [exchangeTarget,(flatViewEquiv small e).injective.eq_iff]
  unfold codeExchange
  rw [flatten_profileCode,listExchange_ofFn,he,←flatten_profileCode]
  simpa only [profileCode,viewList,List.length_ofFn] using
    split_flattenViews (profileCode small e
      (exchangeTarget z (flatViewEquiv small e i) (flatViewEquiv small e j)))

end
end ContingencyTables.SmallGraphProfiles

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

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles ProfilePrograms
open IntegerWeightedTransport

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

lemma flat_getD (z : SmallProfile small) (i : Fin (q+q)) :
    (flattenViews (profileCode small e z)).getD i.val 0=z (flatViewEquiv small e i) := by
  rw [flatten_profileCode]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta]

theorem mem_codeExchangeList (z : SmallProfile small) (w : List ℕ×List ℕ) :
    w∈codeExchangeList (profileCode small e z) ↔
      ∃ i j : Cells small×Bool,i≠j ∧ 0<z j ∧
        w=profileCode small e (exchangeTarget z i j) := by
  simp only [codeExchangeList,List.mem_map]
  constructor
  · rintro ⟨⟨i,j⟩,hij,hw⟩
    have hh := (mem_positiveExchangeIndices _ i j).mp hij
    have hi : i<q+q := by
      simpa only [flattenViews,profileCode,viewList,List.length_append,List.length_ofFn] using hh.1
    have hj : j<q+q := by
      simpa only [flattenViews,profileCode,viewList,List.length_append,List.length_ofFn] using hh.2.1
    let a : Fin (q+q) := ⟨i,hi⟩
    let b : Fin (q+q) := ⟨j,hj⟩
    refine ⟨flatViewEquiv small e a,flatViewEquiv small e b,?_,?_,?_⟩
    · intro he
      exact hh.2.2.1 (congrArg Fin.val ((flatViewEquiv small e).injective he))
    · rw [←flat_getD small e z b]
      exact hh.2.2.2
    · exact hw.symm.trans (codeExchange_eq small e z a b)
  · rintro ⟨a,b,hab,hb,rfl⟩
    let i := (flatViewEquiv small e).symm a
    let j := (flatViewEquiv small e).symm b
    refine ⟨(i.val,j.val),?_,?_⟩
    · apply (mem_positiveExchangeIndices _ _ _).mpr
      refine ⟨?_,?_,?_,?_⟩
      · simpa only [flattenViews,profileCode,viewList,List.length_append,List.length_ofFn] using i.isLt
      · simpa only [flattenViews,profileCode,viewList,List.length_append,List.length_ofFn] using j.isLt
      · intro he
        have he' : i=j := Fin.ext he
        exact hab ((flatViewEquiv small e).symm.injective he')
      · simpa only [flat_getD small e z j,j,Equiv.apply_symm_apply] using hb
    · simpa only [i,j,Equiv.apply_symm_apply] using codeExchange_eq small e z i j

end
end ContingencyTables.SmallGraphProfiles

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
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]
variable (small : I → J → Bool) {n : ℕ} (e : Fin n ≃ Cells small)

/-- Exactness holds for all input profiles; neither boundedness nor a
preexisting proof of a defect is needed to execute the inverse formula. -/
theorem backwardViews_eq (B : I → J → ℕ) (v : SmallProfile small) (s t : I×J) :
    backwardViews (viewList small e v false,
      (List.ofFn (fun i => B (e i).val.1 (e i).val.2),
        (cellIndex small e s,(cellIndex small e t,cellIndex small e (t.1,s.2)))))=
      (viewList small e (inverseRepairProfile small B v s t) false,
        viewList small e (inverseRepairProfile small B v s t) true) := by
  let w : Fin n → ℕ := fun i => v (e i,false)+
    (if i.val=cellIndex small e t then 1 else 0)-
      (if i.val=cellIndex small e (t.1,s.2) then 1 else 0)
  have hw (i : Fin n) : w i=inverseRepairRow small v s t (e i).val.1 (e i).val.2 := by
    change w i=(transferInt (smallView small v false) (t.1,s.2) t
      (e i).val.1 (e i).val.2).toNat
    have h := transfer_at_index small e (smallView small v false) (t.1,s.2) t i
    have heta : (⟨((e i).val.1,(e i).val.2),(e i).property⟩ : Cells small)=e i :=
      Subtype.ext (Prod.eta (e i).val)
    simpa only [w,smallView,(e i).property,dite_true,heta] using h.symm
  have hq (i : Fin n) :
      w i+(if i.val=cellIndex small e s then 1 else 0)-
        (if i.val=cellIndex small e t then 1 else 0)=
      (transferInt (inverseRepairRow small v s t) t s (e i).val.1 (e i).val.2).toNat := by
    rw [hw]
    exact (transfer_at_index small e (inverseRepairRow small v s t) t s i).symm
  simp only [backwardViews,backwardRows,backwardColumns,viewList,
    listExchange_ofFn_nat,listDifference_ofFn]
  apply Prod.ext
  · apply congrArg List.ofFn
    funext i
    exact hw i
  · apply congrArg List.ofFn
    funext i
    exact congrArg (fun a => B (e i).val.1 (e i).val.2-a) (hq i)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairCodeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forward and inverse repairs on the stored pair of integer lists -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem inverseRepairCode_eq (B : Fin m → Fin n → ℕ) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U) (z : SmallProfile small)
    (s t : Cells small) :
    inverseRepairCode (((cellCatalog small e,profileCode small e z),U),
      ((e.symm s).val,(e.symm t).val))=
      profileCode small e (inverseRepairProfile small B z s.val t.val) := by
  have hc : capacityList (U,(profileCode small e z).1)=
      List.ofFn (fun i => B (e i).val.1 (e i).val.2) := by
    simp only [profileCode,viewList,capacityList_ofFn,hU]
  unfold inverseRepairCode
  rw [hc,crossingIndex_eq]
  have hs : cellIndex small e s.val=(e.symm s).val := by
    simp only [cellIndex,s.property,dite_true]
  have ht : cellIndex small e t.val=(e.symm t).val := by
    simp only [cellIndex,t.property,dite_true]
  rw [←hs,←ht]
  exact backwardViews_eq small e B z s.val t.val

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallDefectCodeTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The labelled defect predicate on two binary-coded views -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem repairLabelTest_iff (B : Fin m → Fin n → ℕ) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U) (z : SmallProfile small)
    (hb : ∀ a : Cells small,z (a,true)≤B a.val.1 a.val.2) (s t : Cells small) :
    repairLabelTest (((cellCatalog small e,profileCode small e z),U),
      ((e.symm s).val,(e.symm t).val))=true ↔
      IsDefect (smallView small z false) (smallQ small B z) s.val t.val := by
  rw [defect_iff_cellSums small B z hb s t]
  simp only [repairLabelTest,profileCode,viewList,defectTest_ofFn]
  constructor
  · rintro ⟨hne,h⟩
    refine ⟨fun he => hne (congrArg e.symm he),?_⟩
    intro a
    have hs : e.symm a=e.symm s ↔ a=s := e.symm.injective.eq_iff
    have ht : e.symm a=e.symm t ↔ a=t := e.symm.injective.eq_iff
    simpa only [Equiv.apply_symm_apply,hs,ht,hU] using h (e.symm a)
  · rintro ⟨hne,h⟩
    refine ⟨fun he => hne (e.symm.injective he),?_⟩
    intro i
    have hs : e i=s ↔ i=e.symm s := (Equiv.eq_symm_apply e).symm
    have ht : e i=t ↔ i=e.symm t := (Equiv.eq_symm_apply e).symm
    simpa only [hs,ht,hU] using h (e i)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOffsetProgram
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the forest affine offset from the stored cell values

Every summand uses the executed cut flags and coefficient. The input
contains the baseline and the two stored views, rather than an affine
offset supplied by an oracle.
-/

namespace ContingencyTables.RootedOffsetProgram

open MatchingFPRAS.TreeTyped SignedPairProgram
open scoped BigOperators Classical

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation

noncomputable def entry {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (a : Fin m×Fin n) : Entry :=
  ((RootedCoefficientProgram.input A t a,
    (ForestAffineProgram.signedParts (x a.1 a.2),ForestAffineProgram.signedParts (q a.1 a.2))),
    ForestAffineProgram.signedParts (A.X a.1 a.2))

noncomputable def data {m n N : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (e : Fin N ≃ Fin m×Fin n) : Input :=
  (ForestAffineProgram.signedParts (A.X t.val.1 t.val.2),
    List.ofFn (fun i => entry A t x q (e i)))

end ContingencyTables.RootedOffsetProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedForestDataProgram
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing a tree penalty from executed coefficients and offsets

All signed affine data are computed internally from the graph, capacities,
baseline and two stored views. Only ordinary cell indices and values occur
in the input; no affine coefficient or offset is supplied.
-/

namespace ContingencyTables.RootedForestDataProgram

open MatchingFPRAS.TreeTyped SignedPairProgram
open scoped Classical

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation ForestAssignmentSplit

noncomputable def data {m n nc nf : ℕ} (A : Instance (Fin m) (Fin n))
    (B : ℕ) (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (cells : Fin nc ≃ Fin m×Fin n) (free : Fin nf ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) : Input :=
  (((B,A.b t.val.1 t.val.2),RootedOffsetProgram.data A t x q cells),
    List.ofFn (fun i => (RootedCoefficientProgram.input A t (free i).val,v (free i))))

end ContingencyTables.RootedForestDataProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedForestCatalog
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the tree and free-cell catalogs

Both catalogs scan the rectangular cell array. A free cell is selected
by its binary capacity and absence from the supplied forest graph; a
tree cell is selected by graph adjacency. Empty forests need no chosen
edge and are handled by the same program.
-/

namespace ContingencyTables.RootedForestCatalog

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open RootedCoefficientProgram FiniteGraphRootProgram
open scoped Classical

open CompanionFactorialApplication ForestAssignmentSplit GraphCompletionCounts

noncomputable def treeEquiv {m n : ℕ} (A : Instance (Fin m) (Fin n)) :
    Fin (catalog (data A,true)).length ≃ TreeCell A.T :=
  Equiv.ofBijective (catalogCell A true) (catalogCell_bijective A true)

end ContingencyTables.RootedForestCatalog

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTreeInputProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Building tree-local inputs from the common raw arrays

The graph, capacity array, baseline and stored views are shared across
all tree terms. A term uses only its pair of cell indices; the program
builds its offset frame and reads the free-grid coordinates in catalog
order.
-/

namespace ContingencyTables.RootedTreeInputProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

lemma freeCatalog_ofFn {m n : ℕ} (A : Instance (Fin m) (Fin n)) :
    RootedForestCatalog.catalog (RootedForestCatalog.data A,false)=
      List.ofFn (fun i => (((RootedForestCatalog.freeEquiv A) i).val.1.val,
        ((RootedForestCatalog.freeEquiv A) i).val.2.val)) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    exact (RootedForestCatalog.catalogCell_coordinates A false ⟨i,hi⟩).symm

end ContingencyTables.RootedTreeInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedForestPrepareProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the whole selected-root forest penalty

The program takes the four cell arrays and the graph. It computes the
root discrepancy, both catalogs, every cut coefficient and every affine
offset before invoking the rational penalty evaluator.
-/

namespace ContingencyTables.RootedForestPrepareProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

noncomputable def data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (C B : ℕ)
    (x q : Fin m → Fin n → ℕ) (v : FreeCell A.small A.T → ℕ) : Input :=
  (((C,B),RootedDemandProgram.data A x q),
    List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i)))

end ContingencyTables.RootedForestPrepareProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPenaltyEvaluateProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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

noncomputable def data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (C a : ℕ)
    (x q : Fin m → Fin n → ℕ) (v : FreeCell A.small A.T → ℕ) : Input :=
  (((A.d,A.W),(C,a)),(RootedDemandProgram.data A x q,
    List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))))

end ContingencyTables.RootedPenaltyEvaluateProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCatalogGrid
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed catalog coordinates for the oracle grid

The executable free-cell order need not agree with `Fintype.equivFin`.
Explicit reindexing identifies the grid exponent evaluated from the
catalog-ordered list.
-/

namespace ContingencyTables.RootedCatalogGrid

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open RootedCompletion
open scoped Classical

noncomputable section
variable {m n : ℕ}

def naturalValues (A : Instance (Fin m) (Fin n)) {K : ℕ}
    (v : Grid (I := Fin (freeCount A)) K) : FreeCell A.small A.T → ℕ :=
  fun f => (v ((RootedForestCatalog.freeEquiv A).symm f)).val.toNat

end
end ContingencyTables.RootedCatalogGrid

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBinFramesProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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

lemma catalog_data (A : Instance (Fin m) (Fin n)) (h : ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    catalog (data A h v)=List.ofFn (fun i =>
      ((RootedForestCatalog.freeEquiv A i).val.1.val,
        (RootedForestCatalog.freeEquiv A i).val.2.val)) :=
  RootedTreeInputProgram.freeCatalog_ofFn A

lemma cell_data (A : Instance (Fin m) (Fin n)) (h : ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (i : Fin (RootedCatalogGrid.freeCount A)) :
    cell (data A h v,i.val)=
      ((RootedForestCatalog.freeEquiv A i).val.1.val,
        (RootedForestCatalog.freeEquiv A i).val.2.val) := by
  rw [cell,catalog_data]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,
    Option.getD_some,Fin.eta]

lemma rangeSize_data (A : Instance (Fin m) (Fin n)) (h : ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (i : Fin (RootedCatalogGrid.freeCount A)) :
    rangeSize (data A h v,i.val)=CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i) := by
  change matrixEntry (matrixCode A.b,cell (data A h v,i.val))+1=_
  rw [cell_data,matrixEntry_code]
  rfl

lemma item_data (A : Instance (Fin m) (Fin n)) (h : ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (i : Fin (RootedCatalogGrid.freeCount A)) :
    item (data A h v,i.val)=
      (((K,CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i)),
        (v i).val.toNat),(h,A.d)) := by
  rw [item,rangeSize_data]
  simp only [coordinate,data,gridNatCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,dite_true,Option.getD_some,Fin.eta]
  rfl

theorem frames_data (A : Instance (Fin m) (Fin n)) (h : ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    frames (data A h v)=List.ofFn (fun i =>
      (((K,CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i)),
        (v i).val.toNat),(h,A.d))) := by
  apply List.ext_getElem
  · simp only [frames,indices,catalog_data,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hin : i<RootedCatalogGrid.freeCount A := by
      simpa only [List.length_ofFn] using hj
    simp only [frames,indices,catalog_data,List.length_ofFn,
      List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact item_data A h v ⟨i,hin⟩

end
end ContingencyTables.RootedBinFramesProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBinDrawLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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

attribute [local instance] OAI.ContingencyTables.RootedBinDrawLaw.freeCellDecidableEq
abbrev Words (A : Instance (Fin m) (Fin n)) (h : ℕ) :=
  (i : Fin (RootedCatalogGrid.freeCount A)) →
    Fin (offsetBitLength (freeRange A (RootedForestCatalog.freeEquiv A i)) h A.d) → Bool

def freeWordEquiv (A : Instance (Fin m) (Fin n)) (h : ℕ) :
    Words A h ≃ FreeWords A h :=
  Equiv.piCongrLeft (fun t : FreeCell A.small A.T =>
    Fin (offsetBitLength (freeRange A t) h A.d) → Bool) (RootedForestCatalog.freeEquiv A)

def reindexWords (A : Instance (Fin m) (Fin n)) (h : ℕ) :
    Words A h ≃ BinWords A h :=
  (freeWordEquiv A h).trans (originalWordEquiv A h).symm

def wordBits (A : Instance (Fin m) (Fin n)) (h : ℕ) : ℕ :=
  ∑ i : Fin (RootedCatalogGrid.freeCount A),
    offsetBitLength (freeRange A (RootedForestCatalog.freeEquiv A i)) h A.d

def wordEquiv (A : Instance (Fin m) (Fin n)) (h : ℕ) :
    (Fin (wordBits A h) → Bool) ≃ Words A h :=
  (Equiv.arrowCongr finSigmaFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.piCurry (fun _ _ => Bool))

lemma interval_bits_le (K N beta h d : ℕ) (hK : 0 < K) (hN : 0 < N)
    (hb : beta < K) :
    offsetBitLength (intervalSize K N beta) h d ≤ offsetBitLength N h d := by
  simpa only [offsetBitLength,BinVectorProgram.activeWidth,BinVectorProgram.reservedWidth,
    BinIntervalProgram.intervalSize_eq] using
    BinVectorProgram.active_le_reserved K N beta h d hK hN hb

end
end ContingencyTables.RootedBinDrawLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedMultiplierUpdate
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selected-root empirical multiplier and counting updates

The observables and empirical counts are those of the actual labelled
chain. The update cancels the preceding multiplier, and the next-parameter
comparison is derived from the literal bounded forest penalty.
-/

namespace ContingencyTables.RootedMultiplierUpdate

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing TwoLiftStates

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def ratio (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (S : Set (Labels A×Bool)) : ℝ :=
  weight A R (j+1) S/weight A R j S

end ContingencyTables.RootedMultiplierUpdate

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseOracleError
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Error of actual selected-root calls in a rational phase update -/

namespace ContingencyTables.RootedPhaseWords

open CompanionFactorialApplication CompanionOracleDensity CompanionRationalUpdates
open CommonBasesFPRAS FiniteIndependentAverages GridBoundary TwoLiftStates
open CompanionWeightOracle (WeightWord)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

/-- The exact empirical ratio written as the plain-state sum divided
by its integer plain-state population. -/
def exactObservedRatio (A : Instance I J) (R : RootedCompletion.Selection A.T) (j N : ℕ)
    (states : Fin N → Set (Labels A×Bool)) : ℝ :=
  (∑ i,plainObservable pairs (RootedMultiplierUpdate.ratio A R j) (states i))/
    plainCount A (List.ofFn states)

end
end ContingencyTables.RootedPhaseWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleAcceptance
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual selected-root weight calls control the Metropolis decision -/

namespace ContingencyTables.RootedOracleAcceptance

open CompanionFactorialApplication CompanionOracleDensity CompanionRationalUpdates
open RootedPhaseWords CommonBasesFPRAS GridBoundary FairBits TwoLiftStates
open CompanionWeightOracle (WeightWord)
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def targetWeight (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (w : Pair A → Pair A → ℚ)
    (S : Set (Labels A×Bool)) : ℝ :=
  (rationalMultiplier pairs w S:ℝ)*RootedAnnealing.weight A R j S

def targetAcceptance (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (w : Pair A → Pair A → ℚ)
    (S T : Set (Labels A×Bool)) : ℝ := min 1 (targetWeight A R j w T/targetWeight A R j w S)

end
end ContingencyTables.RootedOracleAcceptance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedWarmStart
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual companion transversal masses and adjacent warm starts -/

namespace ContingencyTables.RootedWarmStart

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing
open CompanionInitialization (freeTotal)
open TwoLiftStates LabelledFactorial

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def total (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) : ℝ := slotTotal pairs (weight A R j) ∅

noncomputable def law (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (S : Set (Labels A×Bool)) : ℝ :=
  weight A R j S/total A R j

end ContingencyTables.RootedWarmStart

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBooleanKernel
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-root Boolean row law and full-history perturbation -/

namespace ContingencyTables.RootedBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates RootedOracleAcceptance
open CommonBasesFPRAS FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open FiniteLawMoments RealKernelApproximation
open CompanionBooleanPhase (State proposal proposalBits proposal_codes stepBits stepWordEquiv
  slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil)
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The exact target row is the source Metropolis chain, slowed by its
dyadic neighbor-code padding. The stationary distribution is unchanged. -/
def referenceChain (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) : FiniteChain (State A) :=
  metropolisChain pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
    (fun p q => (w p q:ℝ)) (RootedAnnealing.weight A R j)
    (fun p q => by exact_mod_cast hw p q) (RootedAnnealing.weight_positive A R j)

def targetChain (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) : FiniteChain (State A) :=
  FiniteChainSlowdown.slow (referenceChain A R j hp w hw) (slowdown A)
    (by linarith [(slowdown_bounds A hp).1]) (slowdown_bounds A hp).2

def targetPathMass (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (N n : ℕ) (S : State A) :
    PathState (State A) N → ℝ :=
  ((liftKernel (targetChain A R j hp w hw).kernel
    (fun a : PathState (State A) N => pathRead a)
    (fun (a : PathState (State A) N) (T : State A) => pathPut a T)).power n).P (pathInitial N S)

end
end ContingencyTables.RootedBooleanPhase

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleStepProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of the catalog-order oracle step

The program uses the computed forest exponent twice, one arithmetic
axis proposal and one independent bounded dyadic acceptance word.
-/

namespace ContingencyTables.RootedOracleStepProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FairBits

noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : Data :=
  (K,(((A.d,A.W),(C,a)),
    (RootedDemandProgram.data A (ForestCountIdentification.smallX A.small z)
      (fun i j => A.b i j-ForestCountIdentification.smallY A.small z i j),gridNatCode v)))

end
end ContingencyTables.RootedOracleStepProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed correction equals the analysed rational correction -/

namespace ContingencyTables.RootedCorrectionProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary RootedCompletion
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) : Input :=
  ((RootedOracleWalkProgram.data A C a K z v,
    List.ofFn (fun i => (f (RootedForestCatalog.freeEquiv A i)).val)),(degree,depth))

end
end ContingencyTables.RootedCorrectionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleFlatProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial flat-word program for the actual oracle walk -/

namespace ContingencyTables.RootedOracleWalkProgram

open MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FirstSuccess ResidualMixture

noncomputable section
variable {m n : ℕ}

lemma stepWidth_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    stepWidth (data A C a K z v).1=CompanionOracleDensity.oracleStepBits A C := by
  change Nat.clog 2 (8*A.d)+RootedPenaltyEvaluateProgram.height ((A.d,A.W),(C,a))=_
  rw [RootedPenaltyEvaluateProgram.height_data]
  rfl

end
end ContingencyTables.RootedOracleWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSampleProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing one selected-root correction sample

Separate finite words drive the grid walk and the integer draw. The
computed final bin and sampled integer are then passed to the exact
population and rational-power correction program.
-/

namespace ContingencyTables.RootedCorrectionSampleProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

attribute [local irreducible] walked

attribute [local irreducible] binFrame

attribute [local irreducible] sampled

attribute [local irreducible] prepare

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FairBits
open scoped BigOperators

noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (h : ℕ)
    (degree depth walkBits binBits : List Bool) : Input :=
  ((RootedOracleWalkProgram.data A C a K z v,h),((degree,depth),(walkBits,binBits)))

end
end ContingencyTables.RootedCorrectionSampleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSampleLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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

attribute [local instance] OAI.ContingencyTables.RootedCorrectionSampleLaw.freeCellDecidableEq
abbrev Words (A : Instance (Fin m) (Fin n)) (C N h : ℕ) :=
  (Fin (N*oracleStepBits A C) → Bool) × (Fin (RootedBinDrawLaw.wordBits A h) → Bool)

end
end ContingencyTables.RootedCorrectionSampleLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComputedEstimator
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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

abbrev CorrectionWords (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ) :=
  Fin (sampleCount j delta failure) → RootedCorrectionSampleLaw.Words A C
    (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta)

abbrev Inputs (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ) :=
  (Fin j → RatioWords A C K j delta failure) × CorrectionWords A C K j delta failure

end
end ContingencyTables.RootedComputedEstimator

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorExecution
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal input and output of the executed estimator blocks -/

namespace ContingencyTables.RootedEstimatorExecution

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedComputedEstimator
open MatchingFPRAS FiniteObservableTransport CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def ratioBlock (A : Instance (Fin m) (Fin n)) (C K j a : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (draws : RootedComputedEstimator.RatioWords A C K j delta failure) :
    RootedEstimatorBlockProgram.RatioBlock :=
  List.ofFn (fun i => (RootedOracleWalkProgram.data A C a K z v,List.ofFn (draws i)))

def correctionBlock (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (draws : RootedComputedEstimator.CorrectionWords A C K j delta failure) :
    RootedEstimatorBlockProgram.CorrectionBlock :=
  List.ofFn (fun i => RootedCorrectionSampleProgram.data A C j K z v (offsetAccuracy A delta)
    degree depth (List.ofFn (draws i).1) (List.ofFn (draws i).2))

def data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (draws : Inputs A C K j delta failure) :
    RootedEstimatorBlockProgram.Input :=
  ((assignmentCount A,List.ofFn (fun a : Fin j => ratioBlock A C K j a.val delta failure z v (draws.1 a))),
    correctionBlock A C K j delta failure z v degree depth draws.2)

end
end ContingencyTables.RootedEstimatorExecution

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorLayoutProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed sizes of the estimator's disjoint word banks

The schedule supplies the phase and sample counts and the two walk times.
The catalog itself supplies both the integer-draw widths and the initial
free-assignment count. No list is allocated from a binary count here.
-/

namespace ContingencyTables.RootedEstimatorLayoutProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

attribute [local irreducible] frames

attribute [local irreducible] rangeValue rangeValues

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma frames_data (A : Instance (Fin m) (Fin n)) (C K j S Tr Tc h : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    frames (data A C K j S Tr Tc h z v)=List.ofFn (fun i =>
      (((K,CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i)),
        (v i).val.toNat),(h,A.d))) := by
  unfold frames
  change RootedBinFramesProgram.frames (RootedBinFramesProgram.data A h v)=_
  exact RootedBinFramesProgram.frames_data A h v

lemma binWidth_data (A : Instance (Fin m) (Fin n)) (C K j S Tr Tc h : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    binWidth (data A C K j S Tr Tc h z v)=RootedBinDrawLaw.wordBits A h := by
  rw [binWidth,frames_data]
  simp only [List.map_ofFn,List.sum_ofFn,BinVectorProgram.reservedWidth,
    RootedBinDrawLaw.wordBits,FairBits.offsetBitLength,Function.comp_apply]

lemma ratioWidth_data (A : Instance (Fin m) (Fin n)) (C K j S Tr Tc h : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    ratioWidth (data A C K j S Tr Tc h z v)=Tr*CompanionOracleDensity.oracleStepBits A C := by
  change Tr*RootedOracleWalkProgram.stepWidth (RootedOracleWalkProgram.data A C 0 K z v).1=_
  rw [RootedOracleWalkProgram.stepWidth_data]

lemma correctionWalkWidth_data (A : Instance (Fin m) (Fin n)) (C K j S Tr Tc h : ℕ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    correctionWalkWidth (data A C K j S Tr Tc h z v)=Tc*CompanionOracleDensity.oracleStepBits A C := by
  change Tc*RootedOracleWalkProgram.stepWidth (RootedOracleWalkProgram.data A C 0 K z v).1=_
  rw [RootedOracleWalkProgram.stepWidth_data]

end
end ContingencyTables.RootedEstimatorLayoutProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWordSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed estimator consumes exactly its independent sample banks -/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS RootedEstimatorLayoutProgram
open DensePrograms GridBoundary
open scoped Classical

abbrev Banks (c : Context) := EstimatorWordBanks.Banks c.2.1.1 c.2.1.2
  (ratioWidth c) (correctionWalkWidth c) (binWidth c)

def wordEquiv (c : Context) : (Fin (wordWidth c) → Bool) ≃ Banks c :=
  EstimatorWordBanks.wordEquiv c.2.1.1 c.2.1.2
    (ratioWidth c) (correctionWalkWidth c) (binWidth c)

def input (c : Context) (markers : List Bool×List Bool)
    (bits : Fin (wordWidth c) → Bool) : Input := (c,(markers,List.ofFn bits))

def encodeBanks (state : State) (j h count : ℕ) (markers : List Bool×List Bool)
    {S r t b : ℕ} (banks : EstimatorWordBanks.Banks j S r t b) :
    RootedEstimatorBlockProgram.Input :=
  ((count,List.ofFn (fun a => List.ofFn (fun i =>
      (phase (state,a.val),List.ofFn (banks.1 a i))))),
    List.ofFn (fun i => ((phase (state,j),h),
      (markers,(List.ofFn (banks.2 i).1,List.ofFn (banks.2 i).2)))))

def bankInput (c : Context) (markers : List Bool×List Bool) (banks : Banks c) :
    RootedEstimatorBlockProgram.Input :=
  encodeBanks c.1 c.2.1.1 c.2.2.2 (assignmentCount c) markers banks

end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWordLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-word law of the executed selected-root weight oracle -/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedEstimatorLayoutProgram CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def scheduledEquiv (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    (Fin (wordWidth (scheduledContext A C K j delta failure z v)) → Bool) ≃
      RootedComputedEstimator.Inputs A C K j delta failure :=
  (wordEquiv (scheduledContext A C K j delta failure z v)).trans
    (recodeBanks
      (ratioWidth_data A C K j _ _ _ _ z v)
      (correctionWalkWidth_data A C K j _ _ _ _ z v)
      (binWidth_data A C K j _ _ _ _ z v))

end
end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorMedianLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed inner median is the analysed amplified weight oracle -/

namespace ContingencyTables.RootedEstimatorMedianProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedEstimatorLayoutProgram CommonBasesFPRAS
open FiniteObservableTransport
open scoped Classical

noncomputable section
variable {m n : ℕ}

def value (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (epsilon delta : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool)
    (bits : Fin (repetitionCount delta*wordWidth (context A C K j epsilon z v)) → Bool) : ℚ :=
  TreeFraction.val (output ((context A C K j epsilon z v,repetitionCount delta),
    ((degree,depth),List.ofFn bits)))

end
end ContingencyTables.RootedEstimatorMedianProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhysicalNormalizer
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root factorial normalizer is the literal physical mass -/

namespace ContingencyTables.RootedPhysicalNormalizer

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication TwoLiftStates RootedFactorialApplication
open BalancedCellFibres PhysicalLargeProfiles LargePairEnumeration TreeMarginalSignature
open CompanionPhysicalNormalizer (smallProfilesEquiv )

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def physicalMass (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) : ℝ :=
  ∑ a : Profiles (cellWidth A),RootedPenalty.physicalWeight A R alpha
    (BalancedCellFibres.profile (cellWidth A) a)

end ContingencyTables.RootedPhysicalNormalizer

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

noncomputable def actualWeight (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (a : Profiles (cellWidth A)) : ℝ :=
  RootedPenalty.physicalWeight A R alpha (BalancedCellFibres.profile (cellWidth A) a)

end ContingencyTables.RootedFarMass

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTreeMarginal
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

namespace ContingencyTables.RootedTreeMarginal

open scoped BigOperators Classical Matrix Topology
open Filter CommonBasesFPRAS CompanionFactorialApplication ForestPenaltyApplication
open TreeMarginalSignature (keep singleView enumeration cellWidth otherWidths coordinateEquiv)
open LargePairEnumeration BalancedFamily BalancedBox EqualitySoftening IntegerWeightedTransport RowColumnPenalties

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def soft (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha L : ℝ) (t : I×J) : (Bool → ℕ) → ℝ :=
  eliminate (widths (otherWidths A t)) (fun z =>
    softenedWeight cellLine (RootedPenalty.rootFlag R) (fun _ => alpha)
      (lineOffset (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b) A.r A.c)
      viewSlope (unaryRate A.T A.b alpha) (unaryEll (ForestLiteralCount.lower A.T A.d A.b))
      unarySlope (unaryCap A.b) L (z ∘ (coordinateEquiv A t).symm))

noncomputable def exactMarginal (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J) : (Bool → ℕ) → ℝ :=
  eliminate (widths (otherWidths A t)) (fun z =>
    RootedPenalty.physicalWeight A R alpha (z ∘ (coordinateEquiv A t).symm))

noncomputable def scalarSoft (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha L : ℝ) (t : I×J) (k : ℕ) : ℝ :=
  soft A R alpha L t (childProfile (cellWidth A t) k)

noncomputable def scalarExact (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J) (k : ℕ) : ℝ :=
  exactMarginal A R alpha t (childProfile (cellWidth A t) k)

end ContingencyTables.RootedTreeMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedNearMass
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-root mass in the actual narrow exterior tree region -/

namespace ContingencyTables.RootedNearMass

open scoped BigOperators Classical
open CompanionFactorialApplication RootedPhysicalNormalizer RootedFarMass
open RootedTreeMarginal TreeExteriorPositions BalancedCellFibres
open TreeMarginalSignature (cellWidth)
open CompanionNearMass (cellPositions)

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def nearMass (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J) (gamma : ℝ) : ℝ :=
  ∑ a : Profiles (cellWidth A),if a t ∈ cellPositions A t gamma then actualWeight A R alpha a else 0

end ContingencyTables.RootedNearMass

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTraceWords
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bounded first-return words for the selected-root chain -/

namespace ContingencyTables.RootedTraceWords

open CommonBasesFPRAS CompanionFactorialApplication RootedBooleanPhase
open CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary FirstSuccess ResidualMixture
open CompanionBooleanPhase (State stepBits slowdown slowdown_bounds)
open CompanionPhaseTrajectory (historyPrefix)
open CompanionTraceWords (eventIndicator firstHit )
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def sourceKilled (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) :
    KilledKernel (FiniteChain.Outside (plainPredicate (pairs : List (Pair A)))) :=
  metropolisKilled pairs PairedLabels.fresh (CompanionConcentration.pairs_ne_nil A hp)
    PairedLabels.cover (fun p q => (w p q:ℝ)) (RootedAnnealing.weight A R j)
    (fun p q => by exact_mod_cast hw p q) (RootedAnnealing.weight_positive A R j)

def targetKilled (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) :
    KilledKernel (FiniteChain.Outside (plainPredicate (pairs : List (Pair A)))) :=
  FiniteChainSlowdown.slowKilled (sourceKilled A R j hp w hw) (slowdown A)
    (by linarith [(slowdown_bounds A hp).1]) (slowdown_bounds A hp).2

lemma targetKilled_matches (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) :
    ∀ x y,(targetKilled A R j hp w hw).Q x y=(targetChain A R j hp w hw).P x.val y.val := by
  exact FiniteChainSlowdown.slowKilled_matches (referenceChain A R j hp w hw) _
    (sourceKilled A R j hp w hw) (by intro x y; rfl) (slowdown A)
    (by linarith [(slowdown_bounds A hp).1]) (slowdown_bounds A hp).2

end
end ContingencyTables.RootedTraceWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseTrial
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A complete finite-word selected-root phase trial

The trajectory and its weight queries use disjoint words. The output is
the actual guarded rational multiplier and count update.
-/

namespace ContingencyTables.RootedPhaseTrial

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedAnnealing RootedMultiplierUpdate
open RootedPhaseWords
open CompanionBooleanPhase (State stepBits)
open CompanionPhaseWords (Stored )
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def ValidOutput (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (j : ℕ) (old : Stored A) (xi : ℚ) (eta : ℝ) (next : Stored A) : Prop :=
  (∀ p q,0 < next.multiplier p q) ∧ 0 < next.estimate ∧
    GoodMultipliers pairs (weight A R (j+1)) (fun p q => (next.multiplier p q:ℝ)) ∧
    |Real.log ((next.estimate:ℝ)/((old.estimate:ℝ)*
      (slotTotal pairs (weight A R (j+1)) ∅/slotTotal pairs (weight A R j) ∅)))| ≤
      4*(xi:ℝ)+4*eta

end
end ContingencyTables.RootedPhaseTrial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTargetTrace
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-root dyadic trace return and explicit warm cap estimates -/

namespace ContingencyTables.RootedTargetTrace

open CommonBasesFPRAS CompanionFactorialApplication RootedBooleanPhase RootedTraceWords
open CompanionCappedReturn RootedAnnealing RootedWarmStart TwoLiftStates
open CompanionBooleanPhase (State slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def actualTrace (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (hw : ∀ p q,0<w p q) : FiniteChain (PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) := by
  letI := plainIndex_nonempty (pairs : List (CompanionRationalUpdates.Pair A))
    PairedLabels.fresh PairedLabels.cover
  exact (targetChain A R j hp w hw).traceChain (plainPredicate pairs)
    (targetKilled A R j hp w hw) (targetKilled_matches A R j hp w hw)

end
end ContingencyTables.RootedTargetTrace

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTargetMixing
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual selected-root dyadic trace mixing and warm restart schedule -/

namespace ContingencyTables.RootedTargetMixing

open CommonBasesFPRAS CompanionFactorialApplication RootedBooleanPhase RootedTargetTrace
open RootedTraceWords RootedAnnealing RootedWarmStart CompanionRationalUpdates TwoLiftStates
open DegreeCompletion ObservableBounds
open CompanionBooleanPhase (State slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil )
open CompanionTargetMixing (restartTime )
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def literalTrace (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) :
    FiniteChain (PlainIndex (pairs : List (Pair A))) :=
  metropolisTrace pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
    (fun p q => (w p q:ℝ)) (weight A R j)
    (fun p q => by exact_mod_cast hw p q) (weight_positive A R j)

end
end ContingencyTables.RootedTargetMixing

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRestartStages
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successive selected-root restart stages

The reference law is refreshed by the exact trace at each successive
parameter. Only that reference law is asserted to be warm. The actual
bounded-return law is compared to it by contraction and accumulated error.
-/

namespace ContingencyTables.RootedRestartStages

open CommonBasesFPRAS RealKernelApproximation CompanionFactorialApplication
open CompanionRationalUpdates RootedAnnealing RootedWarmStart RootedTargetTrace
open RootedTargetMixing
open CompanionTargetMixing (restartTime)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def reference (A : Instance I J) (R : RootedCompletion.Selection A.T) (H L : ℕ)
    (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ j p q,0 < w j p q) :
    ℕ → PlainIndex (pairs : List (Pair A)) → ℝ
  | 0 => fun S => law A R 0 S.val.val
  | j+1 => ((actualTrace A R (j+1) hp (w (j+1)) (hw (j+1))).kernel.power
      (restartTime A H L)).push (reference A R H L hp w hw j)

end
end ContingencyTables.RootedRestartStages

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedStoredHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stored rational outputs of the actual outer phases

The initial record is at index zero. Later records are the outputs
stored in the finite history; the initial record also supplies every
unused future entry to the restart's multiplier function.
-/

namespace ContingencyTables.RootedStoredHistory

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionPhaseWords (Stored)
open RootedStoredEstimate RootedPhaseTrial
open CompanionTerminalMass (Endpoints tableCount)
open CompanionTerminalApplication (finalPhase)
open TwoLiftStates
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def Good (A : Instance I J) (R : RootedCompletion.Selection A.T) (xi : ℚ) (eta : ℝ)
    (history : List (Stored A)) : Prop :=
  ∀ i,i < history.length →
    ValidOutput A R i (lookup A history i) xi eta (lookup A history (i+1))

end
end ContingencyTables.RootedStoredHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSmallFibres
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Empty large rectangles have a unique retained completion -/

namespace ContingencyTables.PhysicalCompletionFibres

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

/-- When every cell is retained, both views are fixed by the profile. -/
theorem completionFibre_subsingleton (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small)
    (hsmall : ∀ i j,small i j=true) :
    Subsingleton (CompletionFibre small B r rbar c cbar z) := by
  constructor
  intro X Y
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · funext i j
    exact (X.property.2.2.1 i j (hsmall i j)).1.trans
      (Y.property.2.2.1 i j (hsmall i j)).1.symm
  · funext i j
    exact (X.property.2.2.1 i j (hsmall i j)).2.trans
      (Y.property.2.2.1 i j (hsmall i j)).2.symm

end ContingencyTables.PhysicalCompletionFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitGraphEnergy
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Energy of the unit-weight local-proposal chain -/

namespace ContingencyTables.MetropolisChain

open scoped BigOperators Classical
open CommonBasesFPRAS

noncomputable section
variable {X : Type*} [Fintype X] [Nonempty X]

lemma unit_chain_energy (Adj : X → X → Prop) (hsym : ∀ x y,Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ) (hdegree : ∀ x,(Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D:ℝ)*β ≤ 1/2) (H : X → ℝ) :
    (chain (fun _ => 1) (fun _ => by norm_num) Adj hsym β hβ D hdegree hproposal).energy H=
      (β/(Fintype.card X:ℝ))*((∑ x,∑ y,if Adj x y then (H x-H y)^2 else 0)/2) := by
  unfold chain
  rw [FiniteChain.ofMoves_energy]
  simp only [move,div_self (one_ne_zero : (1:ℝ)≠0),min_self,mul_one,
    normalizer,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hterm (x y : X) :
      (1/(Fintype.card X:ℝ))*(if Adj x y then β else 0)*(H x-H y)^2=
      (β/(Fintype.card X:ℝ))*(if Adj x y then (H x-H y)^2 else 0) := by
    split_ifs <;> ring
  simp_rw [hterm,←Finset.mul_sum]
  ring

end
end ContingencyTables.MetropolisChain

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSmallChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-state walk when no dense completion remains

Every retained completion then has weight one. The same local graph is
sampled by accepting every valid proposal; no reference row is chosen.
-/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CompletionCounts CommonBasesFPRAS FiniteExposureVariance

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
local notation "d" => dimensionAllowance (I := I) (J := J)

local instance instDecidableEqPaperStates_r9a50dd_1 : DecidableEq (PaperStates r c) := Classical.decEq _
omit [LinearOrder I] [LinearOrder J] [Nonempty (PaperStates r c)] in
lemma allowance_fourteen [Nonempty I] [Nonempty J] : 14 ≤ d := by
  have hi := Fintype.card_pos (α := I)
  have hj := Fintype.card_pos (α := J)
  unfold dimensionAllowance
  nlinarith

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableBox
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full original-table box and its unique feasible entries -/

namespace ContingencyTables.OriginalTableBox
open DensePrograms ProfilePrograms
open scoped BigOperators Classical
noncomputable section

def decode {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (z : Box m n N) : Option (Table r c) :=
  if h : HasMargins (matrix z) r c then some ⟨matrix z,h⟩ else none

def encode {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hN : (∑ i,r i)≤N) (T : Table r c) : Box m n N := fun k =>
  ⟨T.val (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2,
    Nat.lt_succ_of_le ((entry_le_total T.property _ _).trans hN)⟩

def index {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hN : (∑ i,r i)≤N) (T : Table r c) : Index m n N := finFunctionFinEquiv (encode r c hN T)

def tableAt {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (k : Index m n N) :
    Option (Table r c) := decode r c (finFunctionFinEquiv.symm k)

end
end ContingencyTables.OriginalTableBox

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerLaw
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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

theorem toRational_bind (p : IntegerLaw A Q) (K : A → IntegerLaw B P)
    (hQ : 0<Q) (hP : 0<P) :
    (p.bind K).toRational (Nat.mul_pos hQ hP)=
      bindLaw (p.toRational hQ) (fun a => (K a).toRational hP) := by
  apply RationalLaw.ext
  funext b
  change ((∑ a,p.count a*(K a).count b:ℕ):ℚ)/((Q*P:ℕ):ℚ)=
    ∑ a,((p.count a:ℚ)/Q)*(((K a).count b:ℚ)/P)
  rw [Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  push_cast
  exact (div_mul_div_comm (p.count a:ℚ) Q ((K a).count b) P).symm

end
end IntegerLaw
end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalBoxLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding original-table laws in their computed finite box -/

namespace ContingencyTables.OriginalBoxLaw
open scoped BigOperators Classical
noncomputable section
variable {m n N Q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
open OriginalTableBox

def law (hN : (∑ i,r i)≤N) (p : IntegerLaw (Option (Table r c)) Q) :
    IntegerLaw (Option (Index m n N)) Q :=
  p.push (Option.map (index r c hN))

end
end ContingencyTables.OriginalBoxLaw

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

lemma weight_false_list (n : ℕ) : weight (List.replicate n false)=2*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ,weight_cons,ih]; change 1+1+(2*n+1)=_; omega
end MatchingFPRAS.LiteralCodec

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

def publicWordCount (as : List MatchingFPRAS.Symbol) : ℕ := parameterWordCount (parsedSampling as)

end ContingencyTables.ProfilePrograms

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

lemma toRational_walk [DecidableEq A] (K : A → IntegerLaw A Q) (hQ : 0<Q)
    (x : A) (n : ℕ) :
    (walk K x n).toRational (pow_pos hQ n)=
      FirstSuccess.walkLaw (fun x => (K x).toRational hQ) x n := by
  apply ResidualMixture.RationalLaw.ext
  funext y
  have hK : IntegerPropagation.kernel (fun x y => (K x).count y) Q hQ
      (fun x => (K x).total)=(fun x => (K x).toRational hQ) := by
    funext a
    apply ResidualMixture.RationalLaw.ext
    rfl
  have he := IntegerPropagation.numerators_walkLaw (fun x y => (K x).count y)
    Q hQ (fun x => (K x).total) x n y
  rw [hK] at he
  simpa only [toRational,walk,Nat.cast_pow] using
    he

end ContingencyTables.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BooleanIntegerLaw
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent Boolean words combined with cached integer laws -/

namespace ContingencyTables.IntegerLaw
open FirstSuccess FairBits ResidualMixture
open scoped BigOperators Classical
noncomputable section

lemma toRational_boolean (n : ℕ) :
    (boolean n).toRational (by positivity)=uniformLaw (α := Fin n → Bool) := by
  apply RationalLaw.ext
  funext x
  simp [toRational,boolean,uniformLaw,uniformMass]

variable {B C : Type*} [Fintype B] [Fintype C] [DecidableEq C]

lemma toRational_booleanFinish {s f : ℕ} (p : IntegerLaw B (2^f))
    (draw : (Fin f → Bool) → B) (finish : (Fin s → Bool) → B → C)
    (hp : p.toRational (by positivity)=mapLaw (uniformLaw (α := Fin f → Bool)) draw) :
    (booleanFinish p finish).toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin (s+f) → Bool))
        (fun bits => finish (splitWordEquiv s f bits).1 (draw (splitWordEquiv s f bits).2)) := by
  classical
  unfold booleanFinish
  rw [toRational_rebase,toRational_push,toRational_product,toRational_boolean,hp]
  have he := mapLaw_product (uniformLaw (α := Fin s → Bool))
    (uniformLaw (α := Fin f → Bool)) id draw
  rw [mapLaw_id] at he
  rw [←he,mapLaw_comp]
  have hs := map_equiv (splitWordEquiv s f)
    (uniformLaw (α := Fin (s+f) → Bool))
    (fun z => finish z.1 (draw z.2))
  rw [uniform_equiv,←uniform_product] at hs
  exact hs
  all_goals positivity

end
end ContingencyTables.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FlowMatrixBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary-size bounds for materialized flow updates -/

namespace ContingencyTables.FlowMatrixBounds

open MatchingFPRAS.TreeTyped ResidualGraphProgram FlowEntryProgram FlowMatrixProgram

def matrixBound (C : NatMatrix) : ℕ := C.length*(C.length*(8*weight C+4)+2)+1

end ContingencyTables.FlowMatrixBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IndexedTableLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding accepted-table laws into the computed completion list -/

namespace ContingencyTables.IndexedTableLaw
open scoped BigOperators Classical
noncomputable section
variable {m n N Q : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)

def index (hN : (∑ i,R i)≤N) (X : Table R P) : Index m n N :=
  finFunctionFinEquiv (BoxCompletion.encode R P hN X)

def tableAt (htotal : ∑ i,R i=∑ j,P j) (k : Index m n N) : Option (Table R P) :=
  BoxCompletion.decode R P htotal N (finFunctionFinEquiv.symm k)

def law (hN : (∑ i,R i)≤N) (p : IntegerLaw (Option (Table R P)) Q) :
    IntegerLaw (Option (Index m n N)) Q :=
  p.push (Option.map (index R P hN))

end
end ContingencyTables.IndexedTableLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerResidualCorrection
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer realization of the exact residual correction law -/

namespace ContingencyTables.IntegerResidualCorrection
open ResidualMixture
open scoped BigOperators Classical
noncomputable section

variable {A : Type*} [Fintype A] [Nonempty A] {Q : ℕ}

lemma cast_count (p : IntegerLaw A Q) (T : ℕ) (hQ : 0<Q) (hT : 0<T)
    (hdom : ∀ x,(1-1/(T:ℚ))*(p.toRational hQ).mass x≤uniformMass (α := A)) (a : A) :
    (count p T a : ℤ)=residualNumerator Q T (fun x => (p.count x : ℤ)) a := by
  apply Int.toNat_of_nonneg
  apply residualNumerator_nonnegative
  · exact_mod_cast hQ
  · exact_mod_cast hT
  · simpa only [IntegerLaw.toRational,Int.cast_natCast] using hdom

/-- The finite integer weights sum to `|A|*Q`; all truncations are exact
because the ordinary law is pointwise dominated by the uniform law. -/
def law (p : IntegerLaw A Q) (T : ℕ) (hQ : 0<Q) (hT : 0<T)
    (hdom : ∀ x,(1-1/(T:ℚ))*(p.toRational hQ).mass x≤uniformMass (α := A)) :
    IntegerLaw A (Fintype.card A*Q) where
  count := count p T
  total := by
    apply Int.ofNat_injective
    change ((∑ a,count p T a : ℕ) : ℤ)=((Fintype.card A*Q : ℕ) : ℤ)
    rw [Nat.cast_sum]
    simp_rw [cast_count p T hQ hT hdom]
    have ht : (∑ x,(p.count x:ℤ))=(Q:ℤ) := by
      rw [←Nat.cast_sum,p.total]
    simpa only [Nat.cast_mul] using residualNumerator_total (Q:ℤ) (T:ℤ)
      (fun x => (p.count x:ℤ)) ht

end
end ContingencyTables.IntegerResidualCorrection

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_MeasuredMap
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Costs for mapping cached computations over a finite list -/

namespace ContingencyTables.MeasuredMap
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def foldMeasure (μ : A×B → ℕ) (z : List B×(A×List C)) : ℕ :=
  weight z+(z.1.map (fun b => μ (z.2.1,b))).sum

end ContingencyTables.MeasuredMap

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalChainMixing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A real pointwise mixing bound for the corresponding rational walk -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture CommonBasesFPRAS

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem rationalWalk_variation (K : X → RationalLaw X) (C : FiniteChain X)
    (hK : ∀ x y,((K x).mass y:ℝ)=C.P x y) (π : RationalLaw X)
    (hπ : ∀ y,(π.mass y:ℝ)=C.π y) (x : X) (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hpoint : ∀ y,|C.iterate n (C.pointDensity y) x-1| ≤ δ) :
    (variation (walkLaw K x n) π:ℝ) ≤ δ := by
  have hp (y : X) : |(C.kernel.power n).P x y-C.π y| ≤ C.π y*δ := by
    have hh := hpoint y
    rw [←C.kernel_power_density] at hh
    calc
      _ = C.π y*|(C.kernel.power n).P x y/C.π y-1| := by
        calc
          _ = |C.π y*((C.kernel.power n).P x y/C.π y-1)| := by
            congr 1
            field_simp [(C.positive y).ne']
          _ = _ := by rw [abs_mul,abs_of_pos (C.positive y)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (C.positive y).le
  have hs := Finset.sum_le_sum (fun y (_ : y∈Finset.univ) => hp y)
  rw [←Finset.sum_mul,C.normalized,one_mul] at hs
  unfold variation
  simp only [Rat.cast_div,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,Rat.cast_ofNat,
    walkLaw_cast_kernel K C hK,hπ]
  linarith

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_UniformPartialRejection
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rejecting a uniform finite object through an explicit successful bijection -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
variable (p : S → Prop) (e : A ≃ {s // p s})

omit [Fintype A] [Nonempty A] in
lemma partialEquiv_success_mass (a : A) :
    successMass (uniformLaw (α := S)) (partialEquivDraw p e) a=uniformMass (α := S) := by
  unfold successMass
  simp only [partialEquivDraw_eq_some,uniformLaw]
  simp

omit [Nonempty A] in
lemma partialEquiv_failure_mass :
    failureMass (uniformLaw (α := S)) (partialEquivDraw p e)=
      1-(Fintype.card A:ℚ)/(Fintype.card S:ℚ) := by
  have ht := success_failure_total (uniformLaw (α := S)) (partialEquivDraw p e)
  simp only [partialEquiv_success_mass,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at ht
  unfold uniformMass at ht
  rw [mul_one_div] at ht
  linarith

/-- The bound applies before any approximate law is introduced, so later
TV errors can be accumulated without conditioning on success. -/
theorem uniform_partial_retry_variation (fallback : A) (n : ℕ) :
    variation (retryLaw (uniformLaw (α := S)) (partialEquivDraw p e) fallback n)
      (uniformLaw (α := A)) ≤ (1-(Fintype.card A:ℚ)/(Fintype.card S:ℚ))^n := by
  let s : ℚ := (Fintype.card A:ℚ)/(Fintype.card S:ℚ)
  have hs0 : 0 ≤ s := by dsimp only [s]; positivity
  have hc : Fintype.card A ≤ Fintype.card S :=
    Fintype.card_le_of_injective (fun a => (e a).val)
      (Subtype.val_injective.comp e.injective)
  have hs1 : s ≤ 1 := by
    apply (div_le_one (by exact_mod_cast Fintype.card_pos (α := S))).mpr
    exact_mod_cast hc
  have he (a : A) : successMass (uniformLaw (α := S)) (partialEquivDraw p e) a=
      s*uniformMass (α := A) := by
    rw [partialEquiv_success_mass]
    dsimp only [s,uniformMass]
    have hn : (Fintype.card A:ℚ)≠0 := by exact_mod_cast (Fintype.card_pos (α := A)).ne'
    field_simp [hn]
  unfold variation
  simp only [retryLaw_mass,outputMass]
  simp_rw [he,partialEquiv_failure_mass]
  exact stationary_variation s hs0 hs1 n fallback

/-- A lower success bound gives the usual exponential failure tail. -/
theorem uniform_partial_retry_exp (fallback : A) (n : ℕ) (K : ℝ)
    (hs : 1/K ≤ (Fintype.card A:ℝ)/(Fintype.card S:ℝ)) :
    (variation (retryLaw (uniformLaw (α := S)) (partialEquivDraw p e) fallback n)
      (uniformLaw (α := A)):ℝ) ≤ Real.exp (-(n:ℝ)/K) := by
  have hv := uniform_partial_retry_variation p e fallback n
  have hc : Fintype.card A ≤ Fintype.card S :=
    Fintype.card_le_of_injective (fun a => (e a).val)
      (Subtype.val_injective.comp e.injective)
  have hj : (0:ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos (α := S)
  have hn : 0 ≤ 1-(Fintype.card A:ℝ)/(Fintype.card S:ℝ) := by
    have hh := (div_le_one hj).mpr (show (Fintype.card A:ℝ) ≤ Fintype.card S by exact_mod_cast hc)
    linarith
  have hv' : (variation (retryLaw (uniformLaw (α := S)) (partialEquivDraw p e) fallback n)
      (uniformLaw (α := A)):ℝ) ≤ (1-(Fintype.card A:ℝ)/(Fintype.card S:ℝ))^n := by
    simpa only [Rat.cast_pow,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_natCast] using
      (Rat.cast_le (K := ℝ)).mpr hv
  apply hv'.trans
  calc
    _ ≤ (Real.exp (-((Fintype.card A:ℝ)/(Fintype.card S:ℝ))))^n := by
      apply pow_le_pow_left₀ hn
      linarith [Real.add_one_le_exp (-((Fintype.card A:ℝ)/(Fintype.card S:ℝ)))]
    _ = Real.exp (-(n:ℝ)*((Fintype.card A:ℝ)/(Fintype.card S:ℝ))) := by
      rw [←Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ n by positivity)
      rw [mul_one_div] at hh
      rw [neg_div]
      nlinarith

end
end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreePostRealization
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreePost
open TreeTyped TreeData TreeFunction TreeMachine RegisterProc Turing Polynomial

def inputStacks {A : Type} [Codec A] (a : A) : Stack (K Reg) :=
  encodeEnv (env (TreeTyped.encode a) .nil .nil)

noncomputable def packed {A : Type} [Codec A] (a : A) : List Symbol :=
  StackWords.encoded (FixedEncoding.enc Alphabet) (inputStacks a) (weight a)
end MatchingFPRAS.TreePost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Packed
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreeFunction TreeMachine TreePost

lemma block_length (a : Alphabet) : (block a).length=width := by
  unfold width block
  exact map_enc_length a
end MatchingFPRAS.LiteralPacked

end OAI
end


