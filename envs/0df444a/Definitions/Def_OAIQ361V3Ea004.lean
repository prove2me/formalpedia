-- Prove2me | Definitions.Def_OAIQ361V3Ea004
-- name    : OAIQ361V3Ea004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T16:33:22.632804+00:00
-- url     : https://prove2.me/theorems/cb362e18-73fc-4668-8277-e280043f9e04
-- title:
--   Definitions bundle OAIQ361V3Ea004 of the split of OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 158 declarations of OpenAI's Lean: 103 definitions, 33 instances and 22 theorems. The definitions and types are `OAI.EditApproximation.computedQueryTemporaryCellsFootprint`, `OAI.EditApproximation.finalProgramValue`, `OAI.EditApproximation.groupFootprintTransportBridge`, `OAI.EditApproximation.groupHeapTransportBridge`, `OAI.EditApproximation.integerAcceptedSpaceTerms`, `OAI.EditApproximation.integerAcceptedSpaceTermsFootprint`, `OAI.EditApproximation.integerBinaryAnswer`, `OAI.EditApproximation.integerBinarySpace`, `OAI.EditApproximation.integerBinarySpaceFootprint`, `OAI.EditApproximation.integerBinaryWork`, `OAI.EditApproximation.integerFinalAllocation`, `OAI.EditApproximation.integerQueryLocalWork`, `OAI.EditApproximation.localCommonDrawLaw`, `OAI.EditApproximation.localCommonFinalLaw`, `OAI.EditApproximation.localCommonFinalToTrace`, `OAI.EditApproximation.localCommonMemoAnswer`, `OAI.EditApproximation.localCommonSample`, `OAI.EditApproximation.localCommonSeed`, `OAI.EditApproximation.localCommonTerminalLaw`, `OAI.EditApproximation.localCommonTerminalSample`, `OAI.EditApproximation.localCommonToScheduled`, `OAI.EditApproximation.localCommonTraceLaw`, `OAI.EditApproximation.localFinalProgramAnswer`, `OAI.EditApproximation.localFinalProgramDrawLaw`, `OAI.EditApproximation.localFinalProgramLaw`, `OAI.EditApproximation.localFinalProgramValue`, `OAI.EditApproximation.localGroupMajorant`, `OAI.EditApproximation.localScheduledSeedDrawLaw`, `OAI.EditApproximation.localScheduledSeedLaw`, `OAI.EditApproximation.localScheduledSeedNext`, `OAI.EditApproximation.localTraceAppendFinal`, `OAI.EditApproximation.localTraceFinalProjection`, `OAI.EditApproximation.localTraceGroup`, `OAI.EditApproximation.localTraceInitial`, `OAI.EditApproximation.localTraceInteger`, `OAI.EditApproximation.localTraceMemoAnswer`, `OAI.EditApproximation.localTraceMemoResult`, `OAI.EditApproximation.localTraceSeed`, `OAI.EditApproximation.localWholeFinalAnswer`, `OAI.EditApproximation.physicalBandHistory` and 63 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `EditApproximation_Binary_IntegerBinaryAccuracy`, `EditApproximation_Binary_IntegerBinarySpace`, `EditApproximation_Binary_IntegerBinaryWork`, `EditApproximation_Binary_IntegerQueryWork`, `EditApproximation_Geometry_ComparisonLiftBounds`, `EditApproximation_Geometry_InitialConeGrid`, `EditApproximation_Geometry_InitialConeTable`, `EditApproximation_Geometry_LocalCommonOutput`, `EditApproximation_Geometry_LocalCommonSeed`, `EditApproximation_Geometry_LocalCommonTrace`, `EditApproximation_Geometry_LocalFinalAccuracy`, `EditApproximation_Geometry_LocalInitialCones`, `EditApproximation_Geometry_LocalMedianDrawLaw`, `EditApproximation_Geometry_LocalRefinementCones`, `EditApproximation_Geometry_LocalSeedSchedule`, `EditApproximation_Geometry_LocalTraceMemoOutput`, `EditApproximation_Geometry_LocalTraceProgram`, `EditApproximation_Geometry_PreparedKernelPolynomial`, `EditApproximation_Geometry_PreparedLocalGroupPolynomial`, `EditApproximation_Probability_ExactSampling`, `EditApproximation_Queries_QueryFamilyMemo`, `EditApproximation_Refinement_PhysicalBoundsAllSeeds`, `EditApproximation_Refinement_PhysicalCoarseExecution`, `EditApproximation_Refinement_PhysicalCoarseSeedLaw`, `EditApproximation_Refinement_PhysicalCommonSource`, `EditApproximation_Refinement_PhysicalFamilyCoarseWork`, `EditApproximation_Refinement_PhysicalFamilyOutput`, `EditApproximation_Refinement_PhysicalFamilyRuntime`, `EditApproximation_Refinement_PhysicalFamilySeedTrace`, `EditApproximation_Refinement_PhysicalFamilyTrace`, `EditApproximation_Refinement_PhysicalFinalAccuracy`, `EditApproximation_Refinement_PhysicalLocalGroupKeys`, `EditApproximation_Refinement_PhysicalLocalGroupProgram`, `EditApproximation_Refinement_PhysicalLocalOnlineEquality`, `EditApproximation_Refinement_PhysicalLocalOnlineKeys`, `EditApproximation_Refinement_PhysicalLocalProgramLaw`, `EditApproximation_Refinement_PhysicalLocalValueLaw`, `EditApproximation_Refinement_PhysicalLocalWarmup`, `EditApproximation_Refinement_PhysicalNodeRegret`, `EditApproximation_Refinement_PhysicalOnlineBand`, `EditApproximation_Refinement_PhysicalParentDraw`, `EditApproximation_Refinement_PhysicalProgramLaw`, `EditApproximation_Refinement_PhysicalRawOnlineProgram`, `EditApproximation_Refinement_PhysicalScalarFamilyLaw`, `EditApproximation_Refinement_PhysicalSeedSchedule`, `EditApproximation_Refinement_PhysicalSelectionProgram`, `EditApproximation_Refinement_PhysicalSpatial`, `EditApproximation_Refinement_PhysicalSubtreeBad`, `EditApproximation_Refinement_PhysicalSubtreeCharges`, `EditApproximation_Refinement_PhysicalSubtreeGeneric`, `EditApproximation_Refinement_PhysicalSubtreeMass`, `EditApproximation_Refinement_PhysicalSubtreePrediction`, `EditApproximation_Refinement_PhysicalSubtreeRegret`, `EditApproximation_Refinement_PhysicalTreeGeneric`, `EditApproximation_Refinement_PhysicalTreeRegret`, `EditApproximation_Refinement_PhysicalUniformAccuracy`, `EditApproximation_Refinement_PhysicalWarmup`, `EditApproximation_Refinement_StageComparisonBad`, `EditApproximation_Refinement_StageComparisonCharges`, `EditApproximation_Refinement_StageComparisonPrediction`, `EditApproximation_Specification_ConcreteFootprintBridges`, `EditApproximation_Specification_FootprintMain`, `EditApproximation_Specification_RawBandPipelineFootprintBridges`.
--
--   **Imports.** It imports the published bundles `Def_EditApproxScheme_01`, `Def_EditApproxScheme_02`, `Def_EditApproxScheme_03`, `Def_EditApproxScheme_04`, `Def_EditApproxScheme_05`, `Def_EditApproxScheme_06`, `Def_EditApproxScheme_08`, `Def_EditApproxScheme_09`, `Def_EditApproxScheme_10`, `Def_EditApproxScheme_11`, `Def_EditApproxScheme_12`, `Def_EditApproxScheme_13`, `Def_EditApproxScheme_14`, `Def_EditApproxScheme_15`, `Def_EditApproxScheme_16` and `Def_EditApproxScheme_17`; the bundles `OAIQ361V3Ea002` and `OAIQ361V3Ea003` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.EditApproximation.integerBinaryAnswer_conditional_accuracy`, `OAI.EditApproximation.integerBinarySpaceFootprintRawBand_eq`, `OAI.EditApproximation.integerBinarySpaceFootprint_eq`, `OAI.EditApproximation.integerBinarySpace_polynomial`, `OAI.EditApproximation.integerBinaryWork_expected_near_linear`, `OAI.EditApproximation.localFinalProgram_accuracy`, `OAI.EditApproximation.local_physical_conditional_accuracy`, `OAI.EditApproximation.physicalBand_prefix_expected_regret`, `OAI.EditApproximation.physicalFamilyRuntimeAnswer_event`, `OAI.EditApproximation.physicalProgram_comparison_node_regret`, `OAI.EditApproximation.physicalProgram_expected_root_excess`, `OAI.EditApproximation.physicalProgram_global_node_regret`, `OAI.EditApproximation.physicalProgram_subtree_node_regret` and `OAI.EditApproximation.subtree_expected_excess_of_good_nodes`; the proofs of `OAI.EditApproximation.BinaryFraction.localWarmupKernelWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.queryEarlierInputsWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork_bounds`, `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, `OAI.EditApproximation.computedActiveQueryBudget_cap`, `OAI.EditApproximation.computedExecutionCoarseSamplingWork_expected_near_linear`, `OAI.EditApproximation.computedExecutionIndexedCoarseWork_expected_near_linear`, `OAI.EditApproximation.computedExecutionNonlocalWork_expected_near_linear`, `OAI.EditApproximation.computedExecutionTotalWork_expected_near_linear`, `OAI.EditApproximation.computedQueryMemoNormalized_correct`, `OAI.EditApproximation.computedQueryMemoNormalized_width`, `OAI.EditApproximation.integerBinaryAnswer_conditional_accuracy`, `OAI.EditApproximation.integerBinarySpaceFootprintRawBand_eq`, `OAI.EditApproximation.integerBinarySpaceFootprint_eq`, `OAI.EditApproximation.integerBinarySpace_polynomial`, `OAI.EditApproximation.integerBinaryWork_expected_near_linear`, `OAI.EditApproximation.localFinalProgram_accuracy`, `OAI.EditApproximation.local_physical_conditional_accuracy`, `OAI.EditApproximation.physicalBand_prefix_expected_regret`, `OAI.EditApproximation.physicalFamilyCoarseInputWork_le`, `OAI.EditApproximation.physicalFamilyMemoCoarseWork_expected_le`, `OAI.EditApproximation.physicalFamilyRuntimeAnswer_event`, `OAI.EditApproximation.physicalProgram_comparison_node_regret`, `OAI.EditApproximation.physicalProgram_expected_root_excess`, `OAI.EditApproximation.physicalProgram_global_node_regret`, `OAI.EditApproximation.physicalProgram_subtree_node_regret`, `OAI.EditApproximation.queryLocalBand_work_bound` and `OAI.EditApproximation.subtree_expected_excess_of_good_nodes`.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_EditApproxScheme_17
import Definitions.Def_OAIQ361V3Ea002
import Definitions.Def_OAIQ361V3Ea003

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_ExactSampling
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.reduceOnlineIntegerWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.triangularChoiceWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Exact fair-bit sampling of the optimizer mixture

The finite-word rejection calculation follows Section 9.
The random trial is encoded from actual Boolean bits. First-success trace
probabilities determine the output law and expected number of trials.
-/

namespace EditApproximation

open Finset


/-- The lookup assigns precisely the `j+1` integers in block `j`. -/
theorem triangularChoice_fiber (K : ℕ) (integer : Fin (optimizerTriangularMass K))
    (j : ℕ) (hj : j < K) :
    (triangularChoice K integer).val = j ↔
      optimizerTriangularMass j ≤ integer.val ∧ integer.val < optimizerTriangularMass (j + 1) := by
  induction K with
  | zero => omega
  | succ K ih =>
    simp only [triangularChoice]
    split_ifs with hprevious
    · by_cases hjK : j < K
      · exact ih ⟨integer.val, hprevious⟩ hjK
      · have hjEq : j = K := by omega
        subst j
        have hchosen := (triangularChoice K ⟨integer.val, hprevious⟩).isLt
        simp only [Fin.val_castSucc]
        constructor
        · intro heq
          omega
        · intro hblock
          omega
    · change K = j ↔ _
      by_cases hjEq : j = K
      · subst j
        exact ⟨fun _ => ⟨by omega, integer.isLt⟩, fun _ => rfl⟩
      · have hjK : j + 1 ≤ K := by omega
        have hupper := optimizerTriangularMass_monotone hjK
        constructor
        · intro heq
          omega
        · intro hblock
          omega

/-- Each triangular lookup fiber is exactly a finite interval of the
claimed integer length. -/
def triangularChoiceFiberEquiv (K j : ℕ) (hj : j < K) :
    {integer : Fin (optimizerTriangularMass K) // (triangularChoice K integer).val = j} ≃ Fin (j + 1) where
  toFun integer := ⟨integer.val.val - optimizerTriangularMass j, by
    have hblock := (triangularChoice_fiber K integer.val j hj).mp integer.property
    rw [optimizerTriangularMass_succ] at hblock
    omega⟩
  invFun offset := ⟨⟨optimizerTriangularMass j + offset.val, by
    have hupper := optimizerTriangularMass_monotone (show j + 1 ≤ K by omega)
    rw [optimizerTriangularMass_succ] at hupper
    have hoffset := offset.isLt
    omega⟩, by
      apply (triangularChoice_fiber K _ j hj).mpr
      constructor
      · simp only
        omega
      · simp only
        rw [optimizerTriangularMass_succ]
        have hoffset := offset.isLt
        omega⟩
  left_inv integer := by
    apply Subtype.ext
    apply Fin.ext
    simp only
    have hblock := (triangularChoice_fiber K integer.val j hj).mp integer.property
    omega
  right_inv offset := by
    apply Fin.ext
    simp

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_InitialConeGrid
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# A rounded eligible center for each positive-cost query

This uses the actual natural division grid and the dyadic scale selected
from the integer edit cost. It supplies a finite-family witness for the
initial cone minimum.
-/

namespace EditApproximation





theorem rounded_initial_cone_witness {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (q : TargetInterval target.length) (hcost : 0 < stateEditCost source target q)
    (hN : stateEditCost source target q ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F)
    (hA : 1 ≤ A) (ha : 1 ≤ a)
    (hseed : ∀ r, stateEditCost source target r ≤ U r ∧
      (U r : ℚ) ≤ A * stateEditCost source target r)
    (hfactor : A ≤ a * F) :
    ∃ b ∈ dyadicScales N, ∃ r : TargetInterval target.length,
      seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi ∧
      (b : ℚ) / 2 ≤ U r ∧ (U r : ℚ) ≤ 4 * A * b ∧
      initialConeValue source target U a (32 * F) q r ≤
        2 * F * stateEditCost source target q := by
  let c := stateEditCost source target q
  let b := 2 ^ Nat.log 2 c
  let r := roundInterval (seedGridSpacing b P) q
  have hscale := cost_dyadicScale c N hcost hN
  have he := rounded_seedGrid_error b P (by omega) q
  have hnumeric := rounded_initial_center_numeric
    (c := (c : ℚ)) (cr := stateEditCost source target r) (Ur := U r)
    (b := (b : ℚ)) (P := (P : ℚ)) (A := A) (F := (F : ℚ))
    (e := targetEndpointDistance q r)
    (by dsimp only [b] <;> positivity) (by exact_mod_cast hscale.2.1)
    (by exact_mod_cast hscale.2.2) (by exact_mod_cast hP) hA (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) he (stateEditCost_distance_abs source target q r)
    ⟨by exact_mod_cast (hseed r).1, (hseed r).2⟩
  have hgap : |rationalStateGap source target r| ≤ (stateEditCost source target r : ℚ) := by
    have h := stateEditCost_length_lower source target r
    rw [← rationalStateGap_cast] at h
    exact_mod_cast h
  have hupper : (U r : ℚ) ≤ a * F * stateEditCost source target r :=
    (hseed r).2.trans (mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg _))
  have hscaled := (scaledSeedValue_bounds (U r) (stateEditCost source target r)
    F a _ ha hF (hseed r).1 hupper hgap).2
  refine ⟨b, hscale.1, r, (roundInterval_on_grid _ q).1,
    (roundInterval_on_grid _ q).2, hnumeric.1, hnumeric.2.1, ?_⟩
  unfold initialConeValue
  linarith [hnumeric.2.2]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalWarmup
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Warmup on physical node labels

The Bellman operator requests only physical children. Distinct child labels
are retained even at repeated cuts. Nodes at the last physical level, and
source intervals of width at most one, retain their initial value.
-/

namespace EditApproximation









noncomputable def physicalBellman {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (value : PhysicalEntry M J target.length → ℝ) (state : PhysicalEntry M J target.length) : ℝ := by
  classical
  let parent := physicalSourceInterval source.length state.1
  exact if hbelow : state.1.1.val < J then
    if parent.hi - parent.lo ≤ 1 then initial state else
      actualWideBellman parent (representatives state.1) P (fun q => initial (state.1, q)) L
        (fun i q => value (physicalChild state.1 hbelow i, q)) state.2
    else initial state

noncomputable def physicalWarmup {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length)) :
    ℕ → PhysicalEntry M J target.length → ℝ :=
  warmup (physicalBellman source target P L initial representatives) initial

noncomputable def physicalWarmupAverage {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (T : ℕ) : PhysicalEntry M J target.length → ℝ :=
  warmupAverage (physicalBellman source target P L initial representatives) initial T

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_InitialConeTable
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite global initial-cone table

Every center is a valid target state. The family includes the zero seed
centers and precisely the eligible grid centers at the finite dyadic scales.
The constant fallback is above a witnessed cone on a good seed.
-/

namespace EditApproximation

theorem initialConeCenters_mem_zero {n N P : ℕ} {A : ℚ} (U : TargetInterval n → ℕ)
    (r : TargetInterval n) (hzero : U r = 0) : r ∈ initialConeCenters N P A U := by
  apply List.mem_append_left
  exact List.mem_filter.mpr ⟨targetStates_complete n r, by simpa using hzero⟩

theorem initialConeCenters_mem_grid {n N P b : ℕ} {A : ℚ}
    (U : TargetInterval n → ℕ) (r : TargetInterval n) (hb : b ∈ dyadicScales N)
    (hr : seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi ∧
      (b : ℚ) / 2 ≤ U r ∧ (U r : ℚ) ≤ 4 * A * b) :
    r ∈ initialConeCenters N P A U := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨b, hb,
    List.mem_filter.mpr ⟨targetStates_complete n r, by simpa using hr⟩⟩

theorem globalInitialConeTable_bounds {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A) (ha : 1 ≤ a)
    (hfactor : A ≤ a * F)
    (hcostN : ∀ r, stateEditCost source target r ≤ N)
    (hseed : ∀ r, stateEditCost source target r ≤ U r ∧
      (U r : ℚ) ≤ A * stateEditCost source target r)
    (q : TargetInterval target.length) :
    max ((stateEditCost source target q : ℚ) / a) |rationalStateGap source target q| ≤
      globalInitialConeTable source target U N P F A a q ∧
    globalInitialConeTable source target U N P F A a q ≤
      2 * F * stateEditCost source target q := by
  have hFQ : (1 : ℚ) ≤ F := by exact_mod_cast hF
  have hgap : |rationalStateGap source target q| ≤ (stateEditCost source target q : ℚ) := by
    have h := stateEditCost_length_lower source target q
    rw [← rationalStateGap_cast] at h
    exact_mod_cast h
  have hcost : (stateEditCost source target q : ℚ) ≤ N := by exact_mod_cast hcostN q
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
  constructor
  · apply (le_rationalMinimum_iff _ _ _).2
    constructor
    · have hdiv : (stateEditCost source target q : ℚ) / a ≤ stateEditCost source target q := by
        apply (div_le_iff₀ (by linarith : 0 < a)).2
        have hc0 : (0 : ℚ) ≤ stateEditCost source target q := Nat.cast_nonneg _
        nlinarith
      apply max_le <;> nlinarith
    · intro v hv
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
      exact initialConeValue_actual_lower source target U a (32 * F) q r ha
        (by linarith) (hseed r).1
  · by_cases hc : stateEditCost source target q = 0
    · have hU : U q = 0 := by
        have h := (hseed q).2
        rw [hc, Nat.cast_zero, mul_zero] at h
        exact_mod_cast (le_antisymm h (Nat.cast_nonneg _))
      have hgap0 : rationalStateGap source target q = 0 := by
        rw [hc, Nat.cast_zero] at hgap
        exact abs_eq_zero.mp (le_antisymm hgap (abs_nonneg _))
      have hmem := initialConeCenters_mem_zero (N := N) (P := P) (A := A) U q hU
      have hvalue := rationalMinimum_le_member ((32 * F + 1) * N)
        ((initialConeCenters N P A U).map (initialConeValue source target U a (32 * F) q))
        (List.mem_map.mpr ⟨q, hmem, rfl⟩)
      simpa only [globalInitialConeTable, initialConeValue, hU, hgap0,
        scaledSeedValue_zero, targetEndpointDistance, Nat.dist_self, zero_add,
        Nat.cast_zero, mul_zero, add_zero, hc] using hvalue
    · obtain ⟨b, hb, r, hgridLo, hgridHi, hlow, hupp, hcone⟩ :=
        rounded_initial_cone_witness source target U N P F A a q (by omega)
          (hcostN q) hP hF hA ha hseed hfactor
      have hmem := initialConeCenters_mem_grid U r hb ⟨hgridLo, hgridHi, hlow, hupp⟩
      exact (rationalMinimum_le_member _ _ (List.mem_map.mpr ⟨r, hmem, rfl⟩)).trans hcone

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalInitialCones
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Exact local evaluation of the initial cones

The local implementation enumerates only the stated dyadic scale interval
and the grid square about the query. Zero cones are never searched at a
positive seed query. Equality with the global family is proved on a good
seed; the local program is finite on every input table.
-/

namespace EditApproximation





theorem localInitialConeCenters_subset {n N P : ℕ} {A : ℚ}
    (U : TargetInterval n → ℕ) (q : TargetInterval n) :
    ∀ r ∈ localInitialConeCenters N P A U q, r ∈ initialConeCenters N P A U := by
  intro r hr
  obtain ⟨b, hb, hgrid⟩ := List.mem_flatMap.mp hr
  have hscale := (List.mem_filter.mp hb).1
  have hlocal := (List.mem_filter.mp hgrid).1
  have heligible : (b : ℚ) / 2 ≤ U r ∧ (U r : ℚ) ≤ 4 * A * b := by
    simpa using (List.mem_filter.mp hgrid).2
  have hdiv := localTargetStates_on_grid q r hlocal
  exact initialConeCenters_mem_grid U r hscale ⟨hdiv.1, hdiv.2, heligible⟩

theorem localInitialConeTable_eq_global {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A) (ha : 1 ≤ a)
    (hfactor : A ≤ a * F)
    (hcostN : ∀ r, stateEditCost source target r ≤ N)
    (hseed : ∀ r, stateEditCost source target r ≤ U r ∧
      (U r : ℚ) ≤ A * stateEditCost source target r)
    (q : TargetInterval target.length) :
    localInitialConeTable source target U N P F A a q =
      globalInitialConeTable source target U N P F A a q := by
  let global := globalInitialConeTable source target U N P F A a q
  have hbounds := globalInitialConeTable_bounds source target U N P F A a
    hP hF hA ha hfactor hcostN hseed q
  have hFQ : (0 : ℚ) < F := by exact_mod_cast (by omega : 0 < F)
  have hnonneg : 0 ≤ global := (abs_nonneg _).trans ((le_max_right _ _).trans hbounds.1)
  by_cases hzero : U q = 0
  · have hc : stateEditCost source target q = 0 := by have h := (hseed q).1; omega
    have hg : global = 0 := by
      have hupper := hbounds.2
      rw [hc, Nat.cast_zero, mul_zero] at hupper
      exact le_antisymm hupper hnonneg
    simpa only [localInitialConeTable, ite_true, if_true, hzero] using hg.symm
  have hc : (0 : ℚ) < stateEditCost source target q := by
    have h := (hseed q).2
    have hU : (0 : ℚ) < U q := by exact_mod_cast (by omega : 0 < U q)
    by_contra hn
    have hc0 : (stateEditCost source target q : ℚ) = 0 :=
      le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
    rw [hc0, mul_zero] at h
    linarith
  rw [localInitialConeTable, ite_eq_right hzero]
  apply le_antisymm
  · rcases rationalMinimum_attained ((32 * F + 1) * N)
      ((initialConeCenters N P A U).map
        (initialConeValue source target U a (32 * F) q)) with hfallback | hmember
    · exact (rationalMinimum_le_fallback _ _).trans_eq hfallback.symm
    · obtain ⟨r, hr, hvalue⟩ := List.mem_map.mp hmember
      have hconeUpper : initialConeValue source target U a (32 * F) q r ≤
          2 * F * stateEditCost source target q := hvalue.le.trans hbounds.2
      have hconeLower : (32 * F : ℚ) * targetEndpointDistance q r ≤
          initialConeValue source target U a (32 * F) q r := by
        unfold initialConeValue scaledSeedValue
        have hscaled : (0 : ℚ) ≤ max (⌈(U r : ℚ) / a⌉₊ : ℚ)
            |rationalStateGap source target r| := (abs_nonneg _).trans (le_max_right _ _)
        linarith
      rcases List.mem_append.mp hr with hzeroCenter | hgridCenter
      · have hUr : U r = 0 := by simpa using (List.mem_filter.mp hzeroCenter).2
        have hcr : stateEditCost source target r = 0 := by have h := (hseed r).1; omega
        have hdist := stateEditCost_distance_abs source target q r
        rw [hcr, Nat.cast_zero, sub_zero, abs_of_pos hc] at hdist
        have hmul := mul_le_mul_of_nonneg_left hdist (by positivity : (0 : ℚ) ≤ 32 * F)
        nlinarith
      · obtain ⟨b, hb, helig⟩ := List.mem_flatMap.mp hgridCenter
        have heligible : seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi ∧
            (b : ℚ) / 2 ≤ U r ∧ (U r : ℚ) ≤ 4 * A * b := by
          simpa using (List.mem_filter.mp helig).2
        have hlocality := initial_cone_locality_numeric hc hA hFQ (Nat.cast_nonneg b)
          ⟨by exact_mod_cast (hseed q).1, (hseed q).2⟩
          ⟨by exact_mod_cast (hseed r).1, (hseed r).2⟩
          (stateEditCost_distance_abs source target q r) heligible.2.2 hconeLower hconeUpper
        have hdist : targetEndpointDistance q r ≤ U q := by exact_mod_cast hlocality.2.2.2.2
        have hmemLocal : r ∈ localInitialConeCenters N P A U q := by
          apply List.mem_flatMap.mpr
          refine ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, List.mem_filter.mpr ⟨?_, ?_⟩⟩
          · simpa using ⟨hlocality.2.2.1, hlocality.2.2.2.1⟩
          · apply localTargetStates_complete (by unfold seedGridSpacing; omega) q r
              (by unfold targetEndpointDistance at hdist; omega)
              (by unfold targetEndpointDistance at hdist; omega)
              ⟨heligible.1, heligible.2.1⟩
          · simpa using heligible.2.2
        exact (rationalMinimum_le_member _ _
          (List.mem_map.mpr ⟨r, hmemLocal, rfl⟩)).trans_eq hvalue
  · apply (le_rationalMinimum_iff _ _ _).2
    constructor
    · exact rationalMinimum_le_fallback _ _
    · intro v hv
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
      exact rationalMinimum_le_member _ _ (List.mem_map.mpr
        ⟨r, localInitialConeCenters_subset U q r hr, rfl⟩)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalBoundsAllSeeds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegativity and size bounds hold on every seed and every sample outcome. -/

namespace EditApproximation

open Finset

 theorem stageWarmup_nonneg_all_seeds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (t : ℕ) (state : PhysicalEntry M J target.length) :
    0 ≤ stageWarmup source target U N P F A t state := by
  induction t generalizing state with
  | zero => exact stageInitial_nonneg_all_seeds source target U N P F A state
  | succ t ih =>
    exact rationalPhysicalBellman_nonneg source target P (128 * F) (by positivity) _ _
      (stageInitial_nonneg_all_seeds source target U N P F A) _ ih state

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSpatial
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial regularity of the actual local initial table and physical warmup. -/

namespace EditApproximation

theorem physicalInitialTable_spatial {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A a : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A) (ha : 1 ≤ a) (hfactor : A ≤ a * F)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (q q' : TargetInterval target.length) :
    physicalInitialTable source target U N P F A a (node, q) ≤
      physicalInitialTable source target U N P F A a (node, q') +
        (32 * F : ℚ) * targetEndpointDistance q q' := by
  unfold physicalInitialTable
  dsimp only
  split_ifs with hleaf
  · rw [shortSourceCost_eq_edit _ _ hleaf, shortSourceCost_eq_edit _ _ hleaf]
    have hcost : (stateEditCost (physicalSource source node) target q : ℚ) ≤
        stateEditCost (physicalSource source node) target q' + targetEndpointDistance q q' := by
      exact_mod_cast stateEditCost_spatial (physicalSource source node) target q q'
    have hFr : (1 : ℚ) ≤ F := by exact_mod_cast hF
    have hcharge : (targetEndpointDistance q q' : ℚ) ≤
        (32 * F : ℚ) * targetEndpointDistance q q' := by
      nlinarith only [hFr, Nat.cast_nonneg (α := ℚ) (targetEndpointDistance q q')]
    change (stateEditCost (physicalSource source node) target q : ℚ) ≤
      stateEditCost (physicalSource source node) target q' + _
    linarith only [hcost, hcharge]
  · rw [localInitialConeTable_eq_global _ _ _ N P F A a hP hF hA ha hfactor
        (fun r => physical_state_cost_le source target N hsize (node, r)) (fun r => hseed (node, r)) q,
      localInitialConeTable_eq_global _ _ _ N P F A a hP hF hA ha hfactor
        (fun r => physical_state_cost_le source target N hsize (node, r)) (fun r => hseed (node, r)) q']
    exact globalInitialConeTable_spatial _ _ _ N P F A a q q'

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalRefinementCones
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Direct local enumeration computes the complete refinement Bellman cone
on a spatially regular initial table. Its finite definition applies to every seed. -/

namespace EditApproximation

open Finset



theorem localRefinementRepresentatives_subset {n : ℕ} (N P F : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) :
    ∀ br ∈ localRefinementRepresentatives N P F a initial q,
      br ∈ representativeList N P F a initial := by
  intro br hbr
  obtain ⟨b, hb, hbr⟩ := List.mem_flatMap.mp hbr
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hbr
  obtain ⟨hr, heligible⟩ := List.mem_filter.mp hr
  have hgrid := localTargetStates_on_grid q r hr
  exact representativeList_mem a initial r (List.mem_filter.mp hb).1 hgrid
    (of_decide_eq_true heligible).1 (of_decide_eq_true heligible).2

/-- Local representatives retain every cone that can improve the initial
fallback. All other complete cones are discarded by their distance charge. -/
theorem localRefinementBellman_eq {nx ny M : ℕ}
    (parent : TargetInterval nx) (N P F : ℕ) (a : ℚ)
    (initial : TargetInterval ny → ℚ) (child : Fin M × TargetInterval ny → ℚ)
    (q : TargetInterval ny) (ha : 1 ≤ a) (hF : 1 ≤ F)
    (hinitial : 0 ≤ initial q) (hchild : ∀ s, 0 ≤ child s)
    (hspatial : ∀ r, |initial q - initial r| ≤ 32 * F * targetEndpointDistance q r) :
    rationalBellman initial (fun q r => targetEndpointDistance q r) (128 * F)
        (rationalActualWideActions parent (localRefinementRepresentatives N P F a initial q) P) child q =
      rationalBellman initial (fun q r => targetEndpointDistance q r) (128 * F)
        (rationalActualWideActions parent (representativeList N P F a initial) P) child q := by
  let complete := rationalActualWideActions (M := M) parent (representativeList N P F a initial) P
  let nearby := rationalActualWideActions (M := M) parent (localRefinementRepresentatives N P F a initial q) P
  let value := rationalActionValue (M := M) (fun q r : TargetInterval ny => (targetEndpointDistance q r : ℚ))
    (128 * F) child q
  have hsubset : ∀ action ∈ nearby, action ∈ complete := rationalActualWideActions_mono parent _ _ P
    (localRefinementRepresentatives_subset N P F a initial q)
  have hnonneg : ∀ action ∈ complete, 0 ≤ value action := by
    intro action ha'
    exact rationalActionValue_pruned_lower _ _ child q action 0 (by positivity)
      (rationalActualWideActions_connection_nonneg parent _ P action ha') (fun _ => hchild _)
  change rationalMinimum (initial q) (nearby.map value) = rationalMinimum (initial q) (complete.map value)
  by_cases hw : 0 < initial q
  · apply rationalMinimum_local_complete complete nearby value (initial q) hsubset
    intro action hacomplete hvalue
    obtain ⟨br, hbr, haction⟩ := List.mem_flatMap.mp hacomplete
    obtain ⟨states, hstates, heq⟩ := List.mem_map.mp haction
    have hcenter : br.2 = action.center := congrArg RationalBellmanAction.center heq
    have hcharge : 128 * (F : ℚ) * targetEndpointDistance q action.center ≤ value action := by
      exact rationalActionValue_pruned_lower _ _ child q action _ le_rfl
        (rationalActualWideActions_connection_nonneg parent _ P action hacomplete) (fun _ => hchild _)
    have hrep := localRefinementRepresentatives_complete initial q action.center hw ha hF
      (hspatial action.center) (by simpa only [← hcenter] using hbr) (hcharge.trans hvalue)
    exact List.mem_flatMap.mpr ⟨br, by simpa only [← hcenter] using hrep,
      List.mem_map.mpr ⟨states, hstates, heq⟩⟩
  · have hzero : initial q = 0 := le_antisymm (le_of_not_gt hw) hinitial
    have hmin (indices : List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
        (hindices : ∀ action ∈ indices, action ∈ complete) : rationalMinimum (initial q) (indices.map value) = 0 := by
      apply le_antisymm
      · exact (rationalMinimum_le_fallback _ _).trans_eq hzero
      · apply (le_rationalMinimum_iff _ _ _).2
        refine ⟨hinitial, ?_⟩
        intro v hv
        obtain ⟨action, haction, rfl⟩ := List.mem_map.mp hv
        exact hnonneg action (hindices action haction)
    exact (hmin nearby hsubset).trans (hmin complete (fun _ h => h)).symm

/-- The actual initial table supplies the spatial hypotheses on a good
seed. Thus the bounded local search computes its literal warmup cone. -/
theorem physical_localRefinementBellman_eq {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (child : Fin M × TargetInterval target.length → ℚ)
    (hchild : ∀ s, 0 ≤ child s) (q : TargetInterval target.length) :
    rationalBellman (fun r => stageInitial source target U N P F A (node, r))
        (fun q r => targetEndpointDistance q r) (128 * F)
        (rationalActualWideActions (physicalSourceInterval source.length node)
          (localRefinementRepresentatives N P F (refinementFactor A F)
            (fun r => stageInitial source target U N P F A (node, r)) q) P) child q =
      rationalBellman (fun r => stageInitial source target U N P F A (node, r))
        (fun q r => targetEndpointDistance q r) (128 * F)
        (rationalActualWideActions (physicalSourceInterval source.length node)
          (stageRepresentatives source target U N P F A node) P) child q := by
  have hfactor := refinementFactor_spec A F (by omega : 0 < F)
  unfold stageRepresentatives
  apply localRefinementBellman_eq (M := M) (physicalSourceInterval source.length node)
    N P F (refinementFactor A F) (fun r => stageInitial source target U N P F A (node, r)) child q hfactor.1 hF
    (stageInitial_nonneg_all_seeds source target U N P F A (node, q)) hchild
  intro r
  have hqr := physicalInitialTable_spatial source target U N P F A (refinementFactor A F)
    hsize hP hF hA hfactor.1 hfactor.2 hseed node q r
  have hrq := physicalInitialTable_spatial source target U N P F A (refinementFactor A F)
    hsize hP hF hA hfactor.1 hfactor.2 hseed node r q
  have hsym : targetEndpointDistance r q = targetEndpointDistance q r := by
    exact congrArg₂ (· + ·) (Nat.dist_comm _ _) (Nat.dist_comm _ _)
  rw [hsym] at hrq
  apply abs_le.mpr
  constructor <;> dsimp only [stageInitial] <;> linarith only [hqr, hrq]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalOnlineBand
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Online actions from the actual physical child histories

The fixed representative band uses the rational warmup-average child
table. Its envelopes scan the literal initial child table. Online gains
and decrements are computed from the full physical refinement histories.
-/

namespace EditApproximation

open Finset


section PhysicalBand

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)

def physicalBandHistory (t : ℕ) (coordinate : Fin M × TargetInterval target.length) : ℚ :=
  physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow coordinate.1) t coordinate.2

variable (b thetaExponent : ℕ) (tau : ℚ) (r : TargetInterval target.length)

local notation "band" => physicalBandActions source target U N P F A T node hbelow b thetaExponent tau r
local notation "mass" => physicalBandEnvelope source target U N P F A T node hbelow b thetaExponent tau r
local notation "history" => physicalBandHistory source target U N P F A T delta choices node hbelow

variable (hM : 0 < M) (hsize : source.length + target.length ≤ N)
  (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (hT : 0 < T)


/-- The exact action sampler retains the order of the literal physical band. -/
def physicalBandOnlineDraw (hband : band ≠ []) (η κ : ℚ) (G K t : ℕ)
    (integer : Fin (optimizerTriangularMass K)) : Fin M → TargetInterval target.length :=
  finiteOptimizerActionDraw band hband mass
    (rationalOnlineLinear η κ (childGain mass history) (childDecrement mass history) t) G K integer


end PhysicalBand

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalNodeRegret
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# First crossing for the literal physical refinement

Online and selected-group candidates are connected to the complete
refinement by membership in its actual finite lists. Group success is the
literal simultaneous estimator-error test, rather than a cone-bound
assumption. The child environment remains fixed throughout this argument.
-/

namespace EditApproximation

open Finset



theorem representativeBandActions_zero_connection {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : ℚ) (child : Fin M → TargetInterval target.length → ℚ)
    (action : Fin M → TargetInterval target.length)
    (haction : action ∈ representativeBandActions source target parent r b P tau theta child) :
    endpointActionConnection r action = 0 := by
  by_cases hwide : wideActionList M parent r b P = []
  · simp only [representativeBandActions, dite_eq_left hwide, List.not_mem_nil] at haction
  · by_cases hZ : 0 < rationalWideActionMinimum parent r b P hwide child
    · simp only [representativeBandActions, dite_eq_right hwide, ite_eq_left hZ] at haction
      exact (computedBandActions_mem parent r b P tau theta _ child action haction).choose_spec.2.2.1
    · simp only [representativeBandActions, dite_eq_right hwide, ite_eq_right hZ, List.not_mem_nil] at haction

theorem sharedBandRationalAction_wide {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (representatives : List (ℕ × TargetInterval target.length)) (b P : ℕ) (tau theta : ℚ)
    (child : Fin M → TargetInterval target.length → ℚ) (hrep : (b, r) ∈ representatives)
    (action : Fin M → TargetInterval target.length)
    (haction : action ∈ representativeBandActions source target parent r b P tau theta child) :
    sharedBandRationalAction r action ∈ rationalActualWideActions parent representatives P := by
  apply List.mem_flatMap.mpr
  refine ⟨(b, r), hrep, List.mem_map.mpr ⟨action,
    representativeBandActions_wide source target parent r b P tau theta child action haction, ?_⟩⟩
  simp only [sharedBandRationalAction,
    representativeBandActions_zero_connection source target parent r b P tau theta child action haction,
    Nat.cast_zero]


section PhysicalNode

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)

def physicalNodeChildren : PhysicalChildTables M target.length := fun i =>
  physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)

def physicalNodeGroups (t : ℕ) : List (PhysicalRationalAction M target.length) :=
  choices.groups node (physicalNodeChildren source target U N P F A T delta choices node hbelow) (t + 1)

def physicalNodeOnline (t : ℕ) (q : TargetInterval target.length) : List (PhysicalRationalAction M target.length) :=
  choices.online node (physicalNodeChildren source target U N P F A T delta choices node hbelow) (t + 1) q

def physicalNodeCone (t : ℕ) (q : TargetInterval target.length) : ℚ :=
  rationalWideStepCone (physicalSourceInterval source.length node)
    (stageRepresentatives source target U N P F A node) P
    (fun r => stageInitial source target U N P F A (node, r)) (128 * F)
    (physicalBandHistory source target U N P F A T delta choices node hbelow t)
    (physicalBandHistory source target U N P F A T delta choices node hbelow (t + 1))
    (physicalNodeGroups source target U N P F A T delta choices node hbelow t) q

def physicalNodeOnlineValue (t : ℕ) (q : TargetInterval target.length) : ℚ :=
  (rationalOnlineMinimum ((physicalNodeOnline source target U N P F A T delta choices node hbelow t q).map
    (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
      (physicalBandHistory source target U N P F A T delta choices node hbelow (t + 1)) q))).getD 0

local notation "history" => physicalBandHistory source target U N P F A T delta choices node hbelow
local notation "parent" => physicalSourceInterval source.length node
local notation "initialParent" => fun r => stageInitial source target U N P F A (node, r)


noncomputable def physicalComparisonClipped
    (comparison : Fin M → TargetInterval target.length) (t : ℕ) : ℝ :=
  ∑ i, max (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (comparison i) : ℝ)
    (history t (i, comparison i) : ℝ)

def physicalNodeCellBands (b thetaExponent : ℕ) (tau : ℚ) (cell : ℕ × ℕ) :=
  cellUnskippedBands source target parent b P F thetaExponent tau (refinementFactor A F)
    initialParent (physicalBandChildMassTable source target U N P F A T node hbelow)
    (physicalBandChildInitial source target U N P F A node hbelow) cell

def physicalNodeSelectedGroup (b thetaExponent Q : ℕ) (tau : ℚ) (cell : ℕ × ℕ)
    (hnonempty : physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell ≠ [])
    (t : ℕ) (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M) :=
  chooseUnskippedGroup Q (fun i s => history (t + 1) (i, s))
    (physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell) hnonempty draw

def physicalNodeGroupFailure (b thetaExponent Q : ℕ) (tau : ℚ) (cell : ℕ × ℕ)
    (t : ℕ) (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M) (gamma : ℚ) : Bool :=
  unskippedGroupFailure source target parent b P thetaExponent tau F
    (physicalBandChildMassTable source target U N P F A T node hbelow)
    (physicalBandChildInitial source target U N P F A node hbelow)
    (fun i s => history (t + 1) (i, s)) Q
    (physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell) draw gamma

end PhysicalNode

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSelectionProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite online and whole-cell candidate programs

Physical selections use the representative and guarded band lists. Each
band has its own finite optimizer stream; every whole cell has shared
per-scale child streams. These streams define coherent finite tables.
-/

namespace EditApproximation

open Finset



section Program

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau η κ : ℚ)

local notation "representatives" => stageRepresentatives source target U N P F A
local notation "theta" => (2 : ℚ) ^ (-(thetaExponent : ℤ))

def physicalProgramOnline {R : ℕ} [NeZero R]
    (stream : PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R)
    (node : PhysicalNode M J) (children : PhysicalChildTables M target.length) (t : ℕ)
    (q : TargetInterval target.length) : List (PhysicalRationalAction M target.length) :=
  if hbelow : node.1.val < J then
    ((List.finRange (representatives node).length).filter fun representative => decide
      (physicalProgramOnlineGuard source target U N P F A node q ((representatives node).get representative))).filterMap fun representative =>
      physicalProgramOnlineCandidate source target U N P F A T thetaExponent H tau η κ
        ⟨node, hbelow⟩ representative children (t - 1)
          (stream ⟨node, hbelow⟩ representative (Fin.ofNat R (t - 1)))
  else []

/-- Every produced online candidate is literally one of the parent wide actions. -/
theorem physicalProgramOnlineCandidate_wide (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) (children : PhysicalChildTables M target.length)
    (t : ℕ)
    (integer : Fin (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative)))
    (action : PhysicalRationalAction M target.length)
    (hselected : physicalProgramOnlineCandidate source target U N P F A T thetaExponent H tau η κ
      node representative children t integer = some action) :
    action ∈ rationalActualWideActions (physicalSourceInterval source.length node.1)
      (representatives node.1) P := by
  let br := (representatives node.1).get representative
  have hrep : br ∈ representatives node.1 := List.get_mem _ _
  unfold physicalProgramOnlineCandidate physicalBandOnlineCandidate at hselected
  dsimp only at hselected
  split_ifs at hselected with hband
  split at hselected
  · cases hselected
  · cases hselected
    exact sharedBandRationalAction_wide source target (physicalSourceInterval source.length node.1) br.2
      (representatives node.1) br.1 P tau theta
      (physicalBandChildMassTable source target U N P F A T node.1 node.2) hrep _
      (finiteOptimizerActionDraw_mem _ hband _ _ _ _ _)

theorem physicalProgramOnline_wide {R : ℕ} [NeZero R]
    (stream : PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R)
    (node : PhysicalNode M J) (children : PhysicalChildTables M target.length) (t : ℕ)
    (q : TargetInterval target.length) (action : PhysicalRationalAction M target.length)
    (hselected : action ∈ physicalProgramOnline source target U N P F A T thetaExponent H tau η κ
      stream node children t q) :
    action ∈ rationalActualWideActions (physicalSourceInterval source.length node)
      (representatives node) P := by
  unfold physicalProgramOnline at hselected
  split_ifs at hselected with hbelow
  · obtain ⟨representative, _, hselected⟩ := List.mem_filterMap.mp hselected
    exact physicalProgramOnlineCandidate_wide source target U N P F A T thetaExponent H tau η κ
      ⟨node, hbelow⟩ representative children _ _ action hselected
  · exact False.elim (List.not_mem_nil hselected)

/-- The actual complete selection interface contains exactly the finite
online and shared whole-cell candidates produced by the streams. -/
def physicalProgramSelections {R : ℕ} [NeZero R]
    (online : PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R)
    (groups : PhysicalGroupStreams source target U N P F A thetaExponent Q R) :
    PhysicalSelections M J source.length target.length P representatives where
  groups := physicalProgramGroups source target U N P F A T thetaExponent Q tau groups
  online := physicalProgramOnline source target U N P F A T thetaExponent H tau η κ online
  groups_mem := physicalProgramGroups_wide source target U N P F A T thetaExponent Q tau groups
  online_mem := physicalProgramOnline_wide source target U N P F A T thetaExponent H tau η κ online


end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalWarmup
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal warmup can be calculated by direct bounded endpoint
loops. Equality with the complete tables is only asserted on good seeds;
the local rules themselves remain finite and bounded on every seed. -/

namespace EditApproximation

open Finset

theorem physicalLocalWarmup_eq {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (t : ℕ) (state : PhysicalEntry M J target.length) :
    physicalLocalWarmup source target U N P F A t state =
      stageWarmup source target U N P F A t state := by
  induction t generalizing state with
  | zero => rfl
  | succ t ih =>
    change _ = rationalPhysicalBellman source target P (128 * F)
      (stageInitial source target U N P F A) (stageRepresentatives source target U N P F A)
      (stageWarmup source target U N P F A t) state
    rw [physicalLocalWarmup]
    unfold rationalPhysicalBellman
    dsimp only
    split_ifs
    · rfl
    · simp_rw [ih]
      exact physical_localRefinementBellman_eq source target U N P F A hsize hP hF hA hseed
        state.1 _ (fun is => stageWarmup_nonneg_all_seeds source target U N P F A t _) state.2
    · rfl

theorem physicalLocalWarmupMass_eq {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (state : PhysicalEntry M J target.length) :
    physicalLocalWarmupMass source target U N P F A T state =
      stageWarmupMass source target U N P F A T state := by
  unfold physicalLocalWarmupMass stageWarmupMass rationalPhysicalWarmupAverage
  simp_rw [physicalLocalWarmup_eq source target U N P F A hsize hP hF hA hseed]
  rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalParentDraw
attribute [-instance] _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parent random streams in a fixed child environment

Finite parent arrays contain independent uniform optimizer integers and
actual shared-group draws. The projection laws are exact. Their use in the
node bound needs only the individual marginals, so no independence between
an online payoff and a group-failure indicator is asserted there.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

instance parentDrawLaw_probability (R O M K : ℕ) [NeZero M] [NeZero O]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] (count : Fin K → ℕ) :
    IsProbabilityMeasure (parentDrawLaw R O M K count) := by
  dsimp only [parentDrawLaw]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalProgramLaw
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The global finite product of actual selection streams

Online slots and whole-cell slots form a finite disjoint union. Each slot
contains its complete finite time array with the prescribed product law.
Mapping the flattened product produces
the actual online/group stream pair without independence hypotheses.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section GlobalLaw

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau : ℚ)
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]

instance physicalProgramCoordinateFintype (key : PhysicalProgramKey source target U N P F A thetaExponent) :
    Fintype (PhysicalProgramCoordinate (R := R) source target U N P F A T thetaExponent H Q tau key) := by
  cases key <;> dsimp only [PhysicalProgramCoordinate] <;> infer_instance

instance physicalProgramCoordinateMeasurableSingleton
    (key : PhysicalProgramKey source target U N P F A thetaExponent) :
    MeasurableSingletonClass
      (PhysicalProgramCoordinate (R := R) source target U N P F A T thetaExponent H Q tau key) := by
  cases key <;> dsimp only [PhysicalProgramCoordinate, physicalProgramCoordinateMeasurableSpace] <;> infer_instance

instance physicalProgramBandMass_nezero (node : PhysicalInternalNode M J)
    (representative : Fin (stageRepresentatives source target U N P F A node.1).length) :
    NeZero (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative)) :=
  ⟨Nat.ne_of_gt (optimizerTriangularMass_positive _
    (physicalProgramBandK_positive source target U N P F A T thetaExponent H tau node representative))⟩


omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
/-- Refresh exactly one online band and one shared whole-cell coordinate. -/
noncomputable def physicalProgramRefresh
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent)
    (fresh : PhysicalOnlineArray (R := R) source target U N P F A T thetaExponent H tau online ×
      PhysicalGroupArray (R := R) source target U N P F A thetaExponent Q group) :
    PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau := by
  classical
  exact Function.update (Function.update draw (.inl online) fresh.1) (.inr group) fresh.2

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
/-- The actual complete selection program evaluated on its global array. -/
def physicalProgramDrawSelections [NeZero R] (η κ : ℚ)
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau) :
    PhysicalSelections M J source.length target.length P (stageRepresentatives source target U N P F A) :=
  let streams := physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau draw
  physicalProgramSelections source target U N P F A T thetaExponent H Q tau η κ streams.1 streams.2


end GlobalLaw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalTreeRegret
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The time and comparison-tree telescope for the actual clipped refinement values. -/

namespace EditApproximation

open Finset

section Refinement

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (rootQ : TargetInterval target.length)

noncomputable def physicalClippedTable (t : ℕ) (state : PhysicalEntry M J target.length) : ℝ :=
  max (stateEditCost (physicalSource source state.1) target state.2)
    (physicalRefinement source target U N P F A T delta choices state.1 t state.2 : ℝ)

noncomputable def physicalClippedLift (t d : ℕ) (path : TreeLayer M d) : ℝ :=
  comparisonPhysicalLift source target hM P hP
    (physicalClippedTable source target U N P F A T delta choices t) rootQ d path

end Refinement

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonLiftBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual stopped-tree warmup masses and their energy telescope bounds. -/

namespace EditApproximation

open Finset

section Warmup

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (rootQ : TargetInterval target.length)

/-- The comparison mass is the actual averaged warmup at active states and
true cost at carried stopped states. -/
noncomputable def stageComparisonMass (d : ℕ) (path : TreeLayer M d) : ℝ :=
  comparisonPhysicalLift source target hM P hP
    (fun state => (stageWarmupMass source target U N P F A T state : ℝ)) rootQ d path

noncomputable def stageComparisonEnergy (d : ℕ) (path : TreeLayer M d) : ℝ :=
  (comparisonStateGap source target (comparisonFrontier source target hM P hP
    (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path)) ^ 2 /
      stageComparisonMass source target hM U N P F A hP T rootQ d path

end Warmup

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparisonCharges
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Curvature and discrepancy are computed from the actual comparison-tree warmup masses. -/

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

noncomputable def stageComparisonCharges (d : Fin J) (path : TreeLayer M d.val) : ℝ × ℝ := by
  classical
  exact match frontier d.val path with
  | none => (0, 0)
  | some (parent, q) => if hstop : comparisonStopped source target parent q then (0, 0) else
      let hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q := by
        unfold comparisonStopped at hstop
        omega
      let node : PhysicalNode M J := ⟨⟨d.val, by omega⟩, path⟩
      let child := fun i s => (stageWarmupMass source target U N P F A T (physicalChild node d.isLt i, s) : ℝ)
      let b := 2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)
      let r := roundInterval (seedGridSpacing b P) q
      let action := comparisonChildren source target hM P hP parent q hc
      let hnonempty : wideActionList M parent r b P ≠ [] := by
        have hmem : action ∈ wideActionList M parent r b P :=
          (comparisonChildren_spec source target hM P hP parent q hc).1
        intro heq
        rw [heq] at hmem
        exact List.not_mem_nil hmem
      (comparisonActionCurvature source target parent r action child,
        comparisonActionMass action child - wideActionMinimum parent r b P hnonempty child)

end Stage

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparisonBad
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exceptional comparison-node costs are bounded by the actual global curvature charge. -/

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

noncomputable def stageComparisonBadCost (ratio : ℝ) : ℝ := by
  classical
  exact ∑ v : (Σ d : Fin J, TreeLayer M d.val) with
    comparisonActiveScale source target (frontier v.1.val v.2) <
      ratio * (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).1 ∨
    comparisonActiveScale source target (frontier v.1.val v.2) <
      ratio * (stageComparisonCharges source target hM U N P F A hP T rootQ v.1 v.2).2,
    comparisonActiveCost source target (frontier v.1.val v.2)

end Stage

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalTreeGeneric
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic cumulative regret at actual comparison-tree slots, including stopped slots. -/

namespace EditApproximation

open Finset

section Tree

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))
local notation "lifted" => physicalClippedLift source target hM U N P F A hP T delta choices rootQ

noncomputable def physicalComparisonTreeRegret (t : ℕ) (d : Fin J) (path : TreeLayer M d.val) : ℝ :=
  lifted (t + 1) d.val path - (128 * (F : ℝ)) * comparisonMovement source target P (frontier d.val path) -
    ∑ i : Fin M, lifted (t + 1) (d.val + 1) (path, i)

end Tree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparisonPrediction
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual comparison charges and rational velocity predictor at a physical slot. -/

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hP : 66 ≤ P) (T : ℕ) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

noncomputable def stageComparisonPrediction (d : Fin J) (path : TreeLayer M d.val) : ℚ := by
  classical
  exact match frontier d.val path with
  | none => 0
  | some (parent, q) => if hstop : comparisonStopped source target parent q then 0 else
      let hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q := by
        unfold comparisonStopped at hstop
        omega
      let node : PhysicalNode M J := ⟨⟨d.val, by omega⟩, path⟩
      let b := 2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)
      let r := roundInterval (seedGridSpacing b P) q
      let action := comparisonChildren source target hM P hP parent q hc
      let hn : wideActionList M parent r b P ≠ [] := by
        have hmem := (comparisonChildren_spec source target hM P hP parent q hc).1
        intro heq
        rw [heq] at hmem
        exact List.not_mem_nil hmem
      rationalStateGap (substring source parent.lo parent.hi) target r /
        rationalWideActionMinimum parent r b P hn
          (physicalBandChildMassTable source target U N P F A T node d.isLt)

end Stage

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeMass
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual original-table warmup masses below an arbitrary physical node. -/

namespace EditApproximation

open Finset

section Warmup

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (root : PhysicalNode M J) (rootQ : TargetInterval target.length)

/-- The comparison mass is the actual averaged warmup at active states and
true cost at carried stopped states. -/
noncomputable def subtreeComparisonMass (d : ℕ) (path : TreeLayer M d) : ℝ :=
  comparisonSubtreeLift source target hM P hP
    (fun state => (stageWarmupMass source target U N P F A T state : ℝ)) root rootQ d path

noncomputable def subtreeComparisonEnergy (d : ℕ) (path : TreeLayer M d) : ℝ :=
  (comparisonStateGap source target (comparisonFrontier source target hM P hP
    (some (physicalSourceInterval source.length root, rootQ)) d path)) ^ 2 /
      subtreeComparisonMass source target hM U N P F A hP T root rootQ d path

end Warmup

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeCharges
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Curvature and discrepancy are computed from the actual comparison-tree warmup masses. -/

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (root : PhysicalNode M J) (K : ℕ)
  (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))

noncomputable def subtreeComparisonCharges (d : Fin K) (path : TreeLayer M d.val) : ℝ × ℝ := by
  classical
  exact match frontier d.val path with
  | none => (0, 0)
  | some (parent, q) => if hstop : comparisonStopped source target parent q then (0, 0) else
      let hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q := by
        unfold comparisonStopped at hstop
        omega
      let node : PhysicalNode M J := physicalSubtreeNode root d.val path (by omega)
      let child := fun i s => (stageWarmupMass source target U N P F A T (physicalChild node (by dsimp only [node, physicalSubtreeNode]; omega) i, s) : ℝ)
      let b := 2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)
      let r := roundInterval (seedGridSpacing b P) q
      let action := comparisonChildren source target hM P hP parent q hc
      let hnonempty : wideActionList M parent r b P ≠ [] := by
        have hmem : action ∈ wideActionList M parent r b P :=
          (comparisonChildren_spec source target hM P hP parent q hc).1
        intro heq
        rw [heq] at hmem
        exact List.not_mem_nil hmem
      (comparisonActionCurvature source target parent r action child,
        comparisonActionMass action child - wideActionMinimum parent r b P hnonempty child)

end Stage

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeBad
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (root : PhysicalNode M J) (K : ℕ)
  (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))

noncomputable def subtreeComparisonBadCost (ratio : ℝ) : ℝ := by
  classical
  exact ∑ v : (Σ d : Fin K, TreeLayer M d.val) with
    comparisonActiveScale source target (frontier v.1.val v.2) <
      ratio * (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).1 ∨
    comparisonActiveScale source target (frontier v.1.val v.2) <
      ratio * (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).2,
    comparisonActiveCost source target (frontier v.1.val v.2)

end Stage

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeRegret
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual clipped refinement telescope below any original physical label. -/

namespace EditApproximation

open Finset

section Refinement

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (root : PhysicalNode M J) (rootQ : TargetInterval target.length)

noncomputable def subtreeClippedLift (t d : ℕ) (path : TreeLayer M d) : ℝ :=
  comparisonSubtreeLift source target hM P hP
    (physicalClippedTable source target U N P F A T delta choices t) root rootQ d path

end Refinement

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeGeneric
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic cumulative regret at actual comparison-tree slots, including stopped slots. -/

namespace EditApproximation

open Finset

section Tree

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (root : PhysicalNode M J) (K : ℕ) (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))
local notation "lifted" => subtreeClippedLift source target hM U N P F A hP T delta choices root rootQ

noncomputable def subtreeComparisonTreeRegret (t : ℕ) (d : Fin K) (path : TreeLayer M d.val) : ℝ :=
  lifted (t + 1) d.val path - (128 * (F : ℝ)) * comparisonMovement source target P (frontier d.val path) -
    ∑ i : Fin M, lifted (t + 1) (d.val + 1) (path, i)

end Tree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreePrediction
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual comparison charges and rational velocity predictor at a physical slot. -/

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hP : 66 ≤ P) (T : ℕ) (root : PhysicalNode M J) (K : ℕ)
  (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))

noncomputable def subtreeComparisonPrediction (d : Fin K) (path : TreeLayer M d.val) : ℚ := by
  classical
  exact match frontier d.val path with
  | none => 0
  | some (parent, q) => if hstop : comparisonStopped source target parent q then 0 else
      let hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q := by
        unfold comparisonStopped at hstop
        omega
      let node : PhysicalNode M J := physicalSubtreeNode root d.val path (by omega)
      let b := 2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)
      let r := roundInterval (seedGridSpacing b P) q
      let action := comparisonChildren source target hM P hP parent q hc
      let hn : wideActionList M parent r b P ≠ [] := by
        have hmem := (comparisonChildren_spec source target hM P hP parent q hc).1
        intro heq
        rw [heq] at hmem
        exact List.not_mem_nil hmem
      rationalStateGap (substring source parent.lo parent.hi) target r /
        rationalWideActionMinimum parent r b P hn
          (physicalBandChildMassTable source target U N P F A T node (by dsimp only [node, physicalSubtreeNode]; omega))

end Stage

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalOnlineEquality
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A proof adapter couples the bounded online query loop to the original
finite product slots. The adapter is used only to compare laws: local
execution uses scale/center keys and never searches a complete table. -/

namespace EditApproximation

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent H T : ℕ) (A tau eta kappa : ℚ)
  (online : PhysicalOnlineStreams source target U N P F A T exponent H tau R)

local notation "representatives" => stageRepresentatives source target U N P F A

noncomputable def physicalOnlineIntegersOfStreams
    (node : PhysicalInternalNode M J) (time : Fin R) (b : ℕ) (r : TargetInterval target.length) : ℕ :=
  if hbr : (b, r) ∈ representatives node.1 then
    (online node (physicalRepresentativeFin source target U N P F A node.1 (b, r) hbr) time).val
  else 0

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalOnlineKeys
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Online random streams have bounded physical keys. The embedding of
the complete representative table is used only in the proof of the law;
the local program requests the scale and rounded center directly. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





section Keys

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ)

def physicalOnlineRawKey
    (key : PhysicalOnlineKey source target U N P F A) :
    PhysicalLocalOnlineKey M J N target.length :=
  (key.1, physicalScaleIndex N
      ((stageRepresentatives source target U N P F A key.1.1).get key.2).1
      (representativeList_scale_mem _ _ (List.get_mem _ key.2)),
    ((stageRepresentatives source target U N P F A key.1.1).get key.2).2)

theorem physicalLocalOnlineBandG_on_key (T exponent H : ℕ) (tau : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (key : PhysicalOnlineKey source target U N P F A) :
    physicalLocalOnlineBandG source target U N P F A T exponent H tau
        (physicalOnlineRawKey source target U N P F A key) =
      physicalProgramBandG source target U N P F A T exponent H tau key.1 key.2 := by
  have hmass : physicalLocalChildMass source target U N P F A T key.1.1 key.1.2 =
      physicalBandChildMassTable source target U N P F A T key.1.1 key.1.2 := by
    funext i r
    exact physicalLocalWarmupMass_eq source target U N P F A hsize hP hF hA hseed T
      (physicalChild key.1.1 key.1.2 i, r)
  simp only [physicalLocalOnlineBandG, physicalOnlineRawKey, physicalScaleIndex_get, hmass,
    keyedOnlineBandG, physicalProgramBandG, physicalBandActions]

theorem physicalLocalOnlineMass_on_key (T exponent H : ℕ) (tau : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (key : PhysicalOnlineKey source target U N P F A) :
    physicalLocalOnlineMass source target U N P F A T exponent H tau
        (physicalOnlineRawKey source target U N P F A key) =
      optimizerTriangularMass
        (physicalProgramBandK source target U N P F A T exponent H tau key.1 key.2) := by
  unfold physicalLocalOnlineMass physicalProgramBandK
  rw [physicalLocalOnlineBandG_on_key source target U N P F A T exponent H tau
    hsize hP hF hA hseed key]

end Keys

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalGroupKeys
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Every whole-cell stream used by the complete program has a bounded
physical key. Its two cell coordinates are at most n*2^exponent. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory



section Keys

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent : ℕ) (A : ℚ)

theorem physicalProgramCells_bounds (node : PhysicalNode M J)
    (b : ℕ) (hb : 1 ≤ b) (cell : ℕ × ℕ)
    (hcell : cell ∈ physicalProgramCells source target U N P F A exponent node b) :
    cell.1 ≤ target.length * 2 ^ exponent ∧ cell.2 ≤ target.length * 2 ^ exponent := by
  obtain ⟨br, _, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp hcell)
  exact targetCell_coordinate_bound exponent b hb br.2

theorem physicalGroupScale_positive
    (key : PhysicalGroupKey source target U N P F A exponent) :
    1 ≤ (dyadicScales N).get key.2.1 := by
  have hm := List.get_mem (dyadicScales N) key.2.1
  obtain ⟨e, _, heq⟩ := List.mem_map.mp hm
  exact heq ▸ Nat.one_le_two_pow

def physicalGroupRawKey (key : PhysicalGroupKey source target U N P F A exponent) :
    PhysicalLocalGroupKey M J N target.length exponent :=
  let cell := (physicalProgramCells source target U N P F A exponent key.1.1
    ((dyadicScales N).get key.2.1)).get key.2.2
  let bounds := physicalProgramCells_bounds source target U N P F exponent A key.1.1
    ((dyadicScales N).get key.2.1) (physicalGroupScale_positive source target U N P F exponent A key)
    cell (List.get_mem _ key.2.2)
  (key.1, key.2.1, ⟨cell.1, Nat.lt_succ_of_le bounds.1⟩, ⟨cell.2, Nat.lt_succ_of_le bounds.2⟩)

end Keys

noncomputable def physicalLocalGroupArrayLaw (M J N n exponent F Q R : ℕ)
    [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (key : PhysicalLocalGroupKey M J N n exponent) :
    Measure (PhysicalLocalGroupArray M J N n exponent F Q R key) :=
  Measure.pi fun _ : Fin R => groupSharedDrawLaw (M := M)
    (fun h => groupSampleCount M Q ((dyadicScales N).get key.2.1)
      (groupDyadicScaleAt M ((dyadicScales N).get key.2.1) F h))

instance physicalLocalGroupArrayLaw_probability (M J N n exponent F Q R : ℕ)
    [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (key : PhysicalLocalGroupKey M J N n exponent) :
    IsProbabilityMeasure (physicalLocalGroupArrayLaw M J N n exponent F Q R key) := by
  unfold physicalLocalGroupArrayLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalProgramLaw
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single bounded-key product supplies both online and whole-cell
streams. Restriction to the complete program preserves their joint law,
including independence between the two kinds of stream. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Law

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q : ℕ) (tau : ℚ)

instance physicalLocalProgramCoordinateFintype
    (key : PhysicalLocalProgramKey M J N target.length exponent) :
    Fintype (PhysicalLocalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau key) := by
  cases key <;> dsimp only [PhysicalLocalProgramCoordinate] <;> infer_instance

instance physicalLocalProgramCoordinateMeasurableSpace
    (key : PhysicalLocalProgramKey M J N target.length exponent) :
    MeasurableSpace (PhysicalLocalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau key) := by
  cases key <;> dsimp only [PhysicalLocalProgramCoordinate] <;> infer_instance

instance physicalLocalProgramCoordinateMeasurableSingleton
    (key : PhysicalLocalProgramKey M J N target.length exponent) :
    MeasurableSingletonClass
      (PhysicalLocalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau key) := by
  cases key <;> dsimp only [physicalLocalProgramCoordinateMeasurableSpace,
    PhysicalLocalProgramCoordinate] <;> infer_instance

noncomputable def physicalLocalProgramCoordinateLaw
    (key : PhysicalLocalProgramKey M J N target.length exponent) :
    Measure (PhysicalLocalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau key) :=
  match key with
  | .inl online => Measure.pi fun _ : Fin R =>
      (PMF.uniformOfFintype
        (Fin (physicalLocalOnlineMass source target U N P F A T exponent H tau online))).toMeasure
  | .inr group => physicalLocalGroupArrayLaw M J N target.length exponent F Q R group

instance physicalLocalProgramCoordinateLaw_probability
    (key : PhysicalLocalProgramKey M J N target.length exponent) :
    IsProbabilityMeasure
      (physicalLocalProgramCoordinateLaw (R := R) source target U N P F A T exponent H Q tau key) := by
  cases key <;> dsimp only [physicalLocalProgramCoordinateLaw,
    physicalLocalProgramCoordinateMeasurableSpace, PhysicalLocalProgramCoordinate] <;> infer_instance

noncomputable def physicalLocalProgramDrawLaw :
    Measure (PhysicalLocalProgramDraw (R := R) source target U N P F A T exponent H Q tau) :=
  Measure.pi (physicalLocalProgramCoordinateLaw (R := R) source target U N P F A T exponent H Q tau)

def physicalLocalProgramOldKey
    (key : PhysicalProgramKey source target U N P F A exponent) :
    PhysicalLocalProgramKey M J N target.length exponent :=
  match key with
  | .inl online => .inl (physicalOnlineRawKey source target U N P F A online)
  | .inr group => .inr (physicalGroupRawKey source target U N P F exponent A group)

variable (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)

def physicalLocalProgramCoordinateImage
    (key : PhysicalProgramKey source target U N P F A exponent) :
    PhysicalLocalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau
        (physicalLocalProgramOldKey source target U N P F A exponent key) →
      PhysicalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau key :=
  match key with
  | .inl online => fun array time => Fin.cast
      (physicalLocalOnlineMass_on_key source target U N P F A T exponent H tau hsize hP hF hA hseed online)
      (array time)
  | .inr _ => id

def physicalLocalProgramToComplete
    (draw : PhysicalLocalProgramDraw (R := R) source target U N P F A T exponent H Q tau) :
    PhysicalProgramDraw (R := R) source target U N P F A T exponent H Q tau :=
  fun key => physicalLocalProgramCoordinateImage source target U N P F A T exponent H Q tau
    hsize hP hF hA hseed key (draw (physicalLocalProgramOldKey source target U N P F A exponent key))

end Law

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalCommonSource
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual bounded physical program can share one source universe
across incoming seed tables. Online coordinates include their requested
range; group coordinates share whole-cell arrays. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory



section Source

variable (M J N n exponent F Q R B : ℕ)
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]

instance physicalCommonCoordinateFintype (key : PhysicalCommonKey M J N n exponent B) :
    Fintype (PhysicalCommonCoordinate M J N n exponent F Q R B key) := by
  cases key <;> dsimp only [PhysicalCommonCoordinate] <;> infer_instance

instance physicalCommonCoordinateMeasurable (key : PhysicalCommonKey M J N n exponent B) :
    MeasurableSpace (PhysicalCommonCoordinate M J N n exponent F Q R B key) := by
  cases key <;> dsimp only [PhysicalCommonCoordinate] <;> infer_instance

instance physicalCommonCoordinateSingleton (key : PhysicalCommonKey M J N n exponent B) :
    MeasurableSingletonClass (PhysicalCommonCoordinate M J N n exponent F Q R B key) := by
  cases key <;> dsimp only [PhysicalCommonCoordinate, physicalCommonCoordinateMeasurable] <;> infer_instance

noncomputable def physicalCommonCoordinateLaw (key : PhysicalCommonKey M J N n exponent B) :
    Measure (PhysicalCommonCoordinate M J N n exponent F Q R B key) :=
  match key with
  | .inl online => Measure.pi fun _ : Fin R =>
      (PMF.uniformOfFintype (Fin online.2.val.val)).toMeasure
  | .inr group => physicalLocalGroupArrayLaw M J N n exponent F Q R group

instance physicalCommonCoordinateLaw_probability (key : PhysicalCommonKey M J N n exponent B) :
    IsProbabilityMeasure (physicalCommonCoordinateLaw M J N n exponent F Q R B key) := by
  cases key <;> dsimp only [physicalCommonCoordinateLaw, PhysicalCommonCoordinate,
    physicalCommonCoordinateMeasurable] <;> infer_instance

noncomputable def physicalCommonLaw : Measure (PhysicalCommonDraw M J N n exponent F Q R B) :=
  Measure.pi (physicalCommonCoordinateLaw M J N n exponent F Q R B)

instance physicalCommonLaw_probability : IsProbabilityMeasure
    (physicalCommonLaw M J N n exponent F Q R B) := by
  unfold physicalCommonLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Source

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalGroupProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite indexed group program has an equivalent cell-keyed
realization. Good initial seeds permit its whole cone to be evaluated
using only the directly enumerated query cells. -/

namespace EditApproximation

section Program

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent Q : ℕ) (A : ℚ)

def physicalGroupStreamsOfKeys {R : ℕ}
    (draw : PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q) :
    PhysicalGroupStreams source target U N P F A exponent Q R :=
  fun node scale cell time => draw node time ((dyadicScales N).get scale)
    ((physicalProgramCells source target U N P F A exponent node.1
      ((dyadicScales N).get scale)).get cell)

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRawOnlineProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local online provider reads a scale/center key directly; the
complete representative index identifies the corresponding action. -/

namespace EditApproximation

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H : ℕ) (tau eta kappa : ℚ)
  (draw : PhysicalLocalOnlineDraw source target U N P F A R T exponent H tau)

variable (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)

def physicalOnlineStreamsOfRaw :
    PhysicalOnlineStreams source target U N P F A T exponent H tau R :=
  fun node representative time =>
    Fin.cast (physicalLocalOnlineMass_on_key source target U N P F A T exponent H tau
      hsize hP hF hA hseed ⟨node, representative⟩)
      (draw (physicalOnlineRawKey source target U N P F A ⟨node, representative⟩) time)

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarFamilyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regrouping the finite physical scalar source gives exactly one fresh
common draw for each pass and copy. This is equality of product laws,
not an assumption about the sampler. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section FamilyLaw

variable {α : Type*} {M J R : ℕ} [NeZero M]
  (target : List α) (N P F exponent H Q passes copies : ℕ)

def physicalFamilyPack (draw : PhysicalFamilyScalarDraw
    (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)
    (pass : Fin (passes + 1)) (copy : Fin (copies + 1)) :=
  physicalScalarPack M J N target.length exponent F Q R (localOnlineMassBound M P H)
    (physicalFamilyCurry target N P F exponent H Q passes copies draw pass copy)

end FamilyLaw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalMedianDrawLaw
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local bounded-key random source implements the same whole-table
median pass as the complete program. Copies are independent, while all
entries within a copy retain their shared online and group draws. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Median

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q : ℕ) (tau eta kappa delta : ℚ)
  (a S copies : ℕ)

/-- The executable local pass: scale and round each full-copy value, take
the upper median, and clamp each result to the common finite seed type. -/
noncomputable def physicalLocalMedianUpdateTable
    (draws : Fin copies → PhysicalLocalProgramDraw (R := R)
      source target U N P F A T exponent H Q tau) :
    ClampedPhysicalSeed M J target.length N := fun state =>
  ⟨finiteMedianSeed N copies
      (fun draw => ⌈(a : ℚ) * physicalLocalJointValue source target U N P F A T exponent H Q
        tau eta kappa delta draw state.1 S state.2⌉₊) draws,
    Nat.lt_succ_of_le (min_le_left _ _)⟩

end Median

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSeedSchedule
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual finite adaptive sequence of median seed passes. Every chosen
incoming table uses its own fresh product of full-table copy streams. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

noncomputable instance scheduledSeedDrawFintype (pass : ℕ) (seed : Seed) :
    Fintype (ScheduledSeedDraw (R := R) source target N P T H pass seed) := by
  classical
  exact Fintype.ofFinite _

noncomputable def scheduledSeedDrawLaw (pass : ℕ) (seed : Seed) :
    Measure (ScheduledSeedDraw (R := R) source target N P T H pass seed) :=
  Measure.pi fun _ : Fin (H ^ 2) => physicalProgramDrawLaw (R := R)
    source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass) T thetaExponent H (ell ^ 80) tau

instance scheduledSeedDrawLaw_probability (pass : ℕ) (seed : Seed) :
    IsProbabilityMeasure (scheduledSeedDrawLaw (R := R) source target N P T H pass seed) := by
  unfold scheduledSeedDrawLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def scheduledSeedNext (pass : ℕ) (seed : Seed)
    (draw : ScheduledSeedDraw (R := R) source target N P T H pass seed) : Seed :=
  physicalMedianUpdateTable source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass) T delta
    (scheduledSeedMultiplier N pass) S (H ^ 2)
    (physicalProgramDrawSelections source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass)
      T thetaExponent H (ell ^ 80) tau eta kappa) draw

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalSeedSchedule
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The seed schedule run with bounded local random keys. A whole incoming
seed chooses one fresh product of full-copy local streams. The failure
bound follows from the actual local median law, rather than a seed oracle. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

noncomputable instance localScheduledSeedDrawFintype (pass : ℕ) (seed : Seed) :
    Fintype (LocalScheduledSeedDraw (R := R) source target N P T H pass seed) := by
  classical
  exact Fintype.ofFinite _

noncomputable def localScheduledSeedDrawLaw (pass : ℕ) (seed : Seed) :
    Measure (LocalScheduledSeedDraw (R := R) source target N P T H pass seed) :=
  Measure.pi fun _ : Fin (H ^ 2) => physicalLocalProgramDrawLaw (R := R)
    source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass)
      T thetaExponent H (ell ^ 80) tau

instance localScheduledSeedDrawLaw_probability (pass : ℕ) (seed : Seed) :
    IsProbabilityMeasure (localScheduledSeedDrawLaw (R := R) source target N P T H pass seed) := by
  unfold localScheduledSeedDrawLaw physicalLocalProgramDrawLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def localScheduledSeedNext (pass : ℕ) (seed : Seed)
    (draw : LocalScheduledSeedDraw (R := R) source target N P T H pass seed) : Seed :=
  physicalLocalMedianUpdateTable source target (clampedSeedNat seed) N P ell
    (scheduledSeedFactor N pass) T thetaExponent H (ell ^ 80) tau eta kappa delta
    (scheduledSeedMultiplier N pass) S (H ^ 2) draw

noncomputable def localScheduledSeedLaw (incoming : Measure Seed) (passes : ℕ) : Measure Seed := by
  classical
  exact adaptiveSeedSequence (localScheduledSeedDrawLaw (R := R) source target N P T H) incoming
    (localScheduledSeedNext (R := R) source target N P T S H) passes

instance localScheduledSeedLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (passes : ℕ) :
    IsProbabilityMeasure (localScheduledSeedLaw (R := R) source target N P T S H incoming passes) := by
  unfold localScheduledSeedLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalCoarseSeedLaw
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The clamped incoming seed table is the image of the actual complete
coarse sampler. Its simultaneous initial accuracy is a derived fact. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section CoarseLaw

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (N B : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)





variable [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]

instance physicalCoarseSeedLaw_probability :
    IsProbabilityMeasure (physicalCoarseSeedLaw source target N B depth) := by
  unfold physicalCoarseSeedLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CoarseLaw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFinalAccuracy
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Accuracy of the final fresh refinement after adaptive median seed passes,
under finite Bernstein bounds and an explicit incoming seed failure bound. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Final

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "terminalFactor" => scheduledSeedFactor N (computedSeedPassCount N)
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

noncomputable def finalProgramValue (rootQ : TargetInterval target.length) (seed : Seed)
    (draw : FinalProgramDraw (R := R) source target N P T H seed) : ℝ :=
  physicalRefinement source target (clampedSeedNat seed) N P ell terminalFactor T delta
    (physicalProgramDrawSelections source target (clampedSeedNat seed) N P ell terminalFactor
      T thetaExponent H (ell ^ 80) tau eta kappa draw)
    (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J) S rootQ

end Final

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalValueLaw
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The direct local program has the same returned-value law as the
complete refinement on each good incoming seed. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section ValueLaw

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q : ℕ) (tau eta kappa delta : ℚ)

instance physicalLocalProgramDrawLaw_probability :
    IsProbabilityMeasure
      (physicalLocalProgramDrawLaw (R := R) source target U N P F A T exponent H Q tau) := by
  unfold physicalLocalProgramDrawLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end ValueLaw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalFinalAccuracy
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final fresh bounded-key local query, following the actual local
median schedule, has the required approximation probability. The incoming
law is supplied by the concrete coarse sampler in the final theorem. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Final

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "terminalFactor" => scheduledSeedFactor N (computedSeedPassCount N)
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

noncomputable def localFinalProgramDrawLaw (seed : Seed) :
    Measure (LocalFinalProgramDraw (R := R) source target N P T H seed) :=
  physicalLocalProgramDrawLaw (R := R) source target (clampedSeedNat seed) N P ell terminalFactor
    T thetaExponent H (ell ^ 80) tau

instance localFinalProgramDrawLaw_probability (seed : Seed) :
    IsProbabilityMeasure (localFinalProgramDrawLaw (R := R) source target N P T H seed) := by
  unfold localFinalProgramDrawLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def localFinalProgramValue (rootQ : TargetInterval target.length) (seed : Seed)
    (draw : LocalFinalProgramDraw (R := R) source target N P T H seed) : ℝ :=
  physicalLocalJointValue source target (clampedSeedNat seed) N P ell terminalFactor
    T thetaExponent H (ell ^ 80) tau eta kappa delta draw
    (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J) S rootQ

noncomputable def localFinalProgramLaw (incoming : Measure Seed) :
    Measure (LocalFinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) := by
  classical
  exact (localScheduledSeedLaw (R := R) source target N P T S H incoming (computedSeedPassCount N)).prod
    (Measure.pi (localFinalProgramDrawLaw (R := R) source target N P T H))

instance localFinalProgramLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming] :
    IsProbabilityMeasure (localFinalProgramLaw (R := R) source target N P T S H incoming) := by
  unfold localFinalProgramLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def localFinalProgramAnswer (rootQ : TargetInterval target.length)
    (pair : LocalFinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) : ℕ :=
  if source = substring target rootQ.lo rootQ.hi then 0 else
    integerAnswer N (freshSeedValue
      (localFinalProgramValue (M := M) (J := J) (R := R) source target N P T S H rootQ) pair)

variable (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
  (hPeq : P = (integerParameters N).P) (hTeq : T = (integerParameters N).T)
  (hSeq : S = (integerParameters N).S) (hHeq : H = inputHeight N)
  (hsize : source.length + target.length ≤ N)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))

noncomputable def localWholeFinalAnswer
    (pair : LocalFinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) : ℕ :=
  localFinalProgramAnswer (R := R) source target N P T S H (finalTargetState target.length) pair

end Final

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCommonSeed
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete common-source seed passes. The sampler range cap is proved
for every seed; no good-seed event is used to define or bound the draws. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section CommonSeed

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "cap" => localOnlineMassBound M P H

noncomputable def localCommonDrawLaw :
    Measure (LocalCommonDraw (M := M) (J := J) (R := R) target N P H) :=
  Measure.pi fun _ : Fin (H ^ 2) =>
    physicalCommonLaw M J N target.length thetaExponent ell (ell ^ 80) R cap

instance localCommonDrawLaw_probability : IsProbabilityMeasure
    (localCommonDrawLaw (M := M) (J := J) (R := R) target N P H) := by
  unfold localCommonDrawLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def localCommonSample (hP : 0 < P) (pass : ℕ) (seed : Seed)
    (draw : LocalCommonDraw (M := M) (J := J) (R := R) target N P H) :
    LocalScheduledSeedDraw (R := R) source target N P T H pass seed :=
  fun copy => physicalCommonSample source target (clampedSeedNat seed) N P ell
    (scheduledSeedFactor N pass) T thetaExponent H (ell ^ 80) R cap tau
    (physicalLocalOnlineMass_le source target (clampedSeedNat seed) N P ell
      (scheduledSeedFactor N pass) T thetaExponent H tau hP) (draw copy)

noncomputable instance localCommonTraceFintype (passes : ℕ) :
    Fintype (LocalCommonTrace (M := M) (J := J) (R := R) target N P H passes) := by
  classical
  exact commonSeedTraceFintype Seed
    (fun _ => LocalCommonDraw (M := M) (J := J) (R := R) target N P H) passes

instance localCommonTraceSingleton (passes : ℕ) :
    MeasurableSingletonClass
      (LocalCommonTrace (M := M) (J := J) (R := R) target N P H passes) := by
  exact commonSeedTraceSingleton Seed
    (fun _ => LocalCommonDraw (M := M) (J := J) (R := R) target N P H) passes

noncomputable def localCommonSeed (hP : 0 < P) (passes : ℕ)
    (trace : LocalCommonTrace (M := M) (J := J) (R := R) target N P H passes) : Seed :=
  commonTraceValue (localCommonSample source target N P T H hP)
    (localScheduledSeedNext (R := R) source target N P T S H) passes trace

noncomputable def localCommonTraceLaw (incoming : Measure Seed) (passes : ℕ) :
    Measure (LocalCommonTrace (M := M) (J := J) (R := R) target N P H passes) :=
  commonTraceLaw (fun _ => localCommonDrawLaw (M := M) (J := J) (R := R) target N P H) incoming passes

instance localCommonTraceLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (passes : ℕ) : IsProbabilityMeasure
      (localCommonTraceLaw (M := M) (J := J) (R := R) target N P H incoming passes) := by
  classical
  unfold localCommonTraceLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CommonSeed

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalTraceProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extract the actual per-pass streams from a finite adaptive draw trace.
Earlier-pass streams are preserved when a new draw is appended, and the
lazy program's seed recurrence is exactly the trace's returned table. -/

namespace EditApproximation

section Trace

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

noncomputable def localTraceSeed (passes : ℕ)
    (trace : LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes) : Seed :=
  adaptiveTraceValue (localScheduledSeedNext (R := R) source target N P T S H) passes trace

def localTraceInitial : (passes : ℕ) → LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes → Seed
  | 0, seed => seed
  | passes + 1, trace => localTraceInitial passes trace.1

noncomputable def localTraceGroup : (passes : ℕ) →
    LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes →
    ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M ell (ell ^ 80)
  | 0, _ => fun _ _ _ _ _ _ _ _ => 0
  | passes + 1, trace => fun pass copy node time =>
    if pass = passes then
      if hcopy : copy < H ^ 2 then
        physicalRawGroupDraws M J N target.length thetaExponent ell (ell ^ 80) R
          (fun key => trace.2 (localTraceSeed source target N P T S H passes trace.1)
            ⟨copy, hcopy⟩ (.inr key)) node time
      else fun _ _ _ _ => 0
    else localTraceGroup passes trace.1 pass copy node time

noncomputable def localTraceInteger : (passes : ℕ) →
    LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes →
    ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ
  | 0, _ => fun _ _ _ _ _ _ => 0
  | passes + 1, trace => fun pass copy =>
    if pass = passes then
      if hcopy : copy < H ^ 2 then
        physicalRawOnlineIntegers source target
          (clampedSeedNat (localTraceSeed source target N P T S H passes trace.1))
          N P ell (scheduledSeedFactor N passes) T thetaExponent H tau
          (fun key => trace.2 (localTraceSeed source target N P T S H passes trace.1)
            ⟨copy, hcopy⟩ (.inl key))
      else fun _ _ _ _ => 0
    else localTraceInteger passes trace.1 pass copy

end Trace

instance localScheduledTrace_measurableSingleton {α : Type*} [DecidableEq α] {M J R : ℕ}
    [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (source target : List α) (N P T H passes : ℕ) :
    MeasurableSingletonClass
      (LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes) := by
  classical
  exact adaptiveSeedTraceSingleton (ClampedPhysicalSeed M J target.length N)
    (LocalScheduledSeedDraw (R := R) source target N P T H) passes

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCommonTrace
attribute [-instance] _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common keyed source gives a lazy functional view of the seed trace.
Only the actual incoming seed is selected during execution. -/

namespace EditApproximation

section Trace

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

noncomputable def localCommonToScheduled (hP : 0 < P) : (passes : ℕ) →
    LocalCommonTrace (M := M) (J := J) (R := R) target N P H passes →
      LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes
  | 0, trace => trace
  | passes + 1, trace =>
    (localCommonToScheduled hP passes trace.1,
      fun seed => localCommonSample source target N P T H hP passes seed trace.2)

end Trace

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalTraceMemoOutput
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The bounded-key adaptive trace drives the actual charged memo program.
Its final root query has the same distribution as the local answer. The program
uses all previous-pass copies from the trace and one fresh terminal copy. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Output

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "passes" => computedSeedPassCount N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

noncomputable def localTraceAppendFinal
    (outcome : LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H) :
    LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H (passes + 1) :=
  (outcome.1, fun seed _ => outcome.2 seed)



noncomputable def localTraceMemoResult (hH : 0 < H) (rootQ : TargetInterval target.length)
    (outcome : LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H) :=
  let trace := localTraceAppendFinal source target N P T H outcome
  chargedMemoEvaluate source target N P ell thetaExponent H (ell ^ 80) T S (passes + 1) (H ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
    (localTraceGroup source target N P T S H (passes + 1) trace)
    (localTraceInteger source target N P T S H (passes + 1) trace)
    (clampedSeedNat (localTraceInitial source target N P T H passes outcome.1))
    (localFinalRootRequest (M := M) (J := J) target N T S H hH rootQ)

noncomputable def localTraceFinalProjection
    (outcome : LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H) :
    LocalFinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H :=
  (localTraceSeed source target N P T S H passes outcome.1, outcome.2)

noncomputable def localTraceMemoAnswer (hH : 0 < H) (rootQ : TargetInterval target.length)
    (outcome : LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H) : ℕ :=
  if source = substring target rootQ.lo rootQ.hi then 0 else
    integerAnswer N ((localTraceMemoResult source target N P T S H hH rootQ outcome).value : ℝ)

end Output

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCommonOutput
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The charged memo answer under one common random source per pass and
one fresh terminal source. Correct marginal laws suffice; hypothetical
seed-indexed draw families are not part of the execution. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Output

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "passes" => computedSeedPassCount N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "cap" => localOnlineMassBound M P H

noncomputable def localCommonTerminalLaw :
    Measure (LocalCommonTerminalDraw (M := M) (J := J) (R := R) target N P H) :=
  physicalCommonLaw M J N target.length thetaExponent ell (ell ^ 80) R cap

instance localCommonTerminalLaw_probability : IsProbabilityMeasure
    (localCommonTerminalLaw (M := M) (J := J) (R := R) target N P H) := by
  unfold localCommonTerminalLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def localCommonTerminalSample (hP : 0 < P) (seed : Seed)
    (draw : LocalCommonTerminalDraw (M := M) (J := J) (R := R) target N P H) :
    LocalFinalProgramDraw (R := R) source target N P T H seed :=
  physicalCommonSample source target (clampedSeedNat seed) N P ell
    (scheduledSeedFactor N passes) T thetaExponent H (ell ^ 80) R cap tau
    (physicalLocalOnlineMass_le source target (clampedSeedNat seed) N P ell
      (scheduledSeedFactor N passes) T thetaExponent H tau hP) draw

noncomputable def localCommonFinalLaw (incoming : Measure Seed) :
    Measure (LocalCommonFinalOutcome (M := M) (J := J) (R := R) target N P H) :=
  (localCommonTraceLaw (M := M) (J := J) (R := R) target N P H incoming passes).prod
    (localCommonTerminalLaw (M := M) (J := J) (R := R) target N P H)

instance localCommonFinalLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming] :
    IsProbabilityMeasure (localCommonFinalLaw (M := M) (J := J) (R := R) target N P H incoming) := by
  unfold localCommonFinalLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def localCommonFinalToTrace (hP : 0 < P)
    (outcome : LocalCommonFinalOutcome (M := M) (J := J) (R := R) target N P H) :
    LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H :=
  (localCommonToScheduled source target N P T H hP passes outcome.1,
    fun seed => localCommonTerminalSample source target N P T H hP seed outcome.2)

noncomputable def localCommonMemoAnswer (hP : 0 < P) (hH : 0 < H)
    (rootQ : TargetInterval target.length)
    (outcome : LocalCommonFinalOutcome (M := M) (J := J) (R := R) target N P H) : ℕ :=
  localTraceMemoAnswer source target N P T S H hH rootQ
    (localCommonFinalToTrace source target N P T H hP outcome)

end Output

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyTrace
attribute [-instance] _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal finite scalar family supplies the independent common
source trace and its final draw, after removing unused extra copies. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section SourceFamily

variable {Seed α : Type} {M J R : ℕ} [NeZero M]
  (target : List α) (N P F exponent H Q passes copies : ℕ)

local notation "Draw" => PhysicalCommonDraw M J N target.length exponent F Q R (localOnlineMassBound M P H)
local notation "Family" => PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
  target N P F exponent H Q passes copies

def physicalFamilyToTrace (input : Seed × Family) :
    CommonSeedTrace Seed (fun _ => Fin copies → Draw) passes × Draw :=
  let packed := physicalFamilyPack target N P F exponent H Q passes copies input.2
  let rows := commonArrayFinal passes (input.1, packed)
  (mapCommonTrace (fun row (copy : Fin copies) => row copy.castSucc) passes rows.1,
    rows.2 0)

end SourceFamily

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilySeedTrace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section SourceFamily

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H passes : ℕ) (hP : 0 < P)

local notation "SeedState" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)

variable (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
  target N P (inputSmallLog N) (40 * smallLogExponent N) H ((inputSmallLog N) ^ 80) passes (H ^ 2))


noncomputable def physicalFamilyPrefix (seed : SeedState) (n : ℕ) (hn : n ≤ passes) :
    LocalCommonTrace (M := M) (J := J) (R := R) target N P H n :=
  let rows : Fin n → LocalCommonDraw (M := M) (J := J) (R := R) target N P H :=
    fun p copy => physicalFamilyPack (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2) draw
      ⟨p.val, Nat.lt_succ_of_le (p.isLt.le.trans hn)⟩ copy.castSucc
  commonArrayToTrace (Seed := SeedState)
    (Ω := LocalCommonDraw (M := M) (J := J) (R := R) target N P H) n (seed, rows)


end SourceFamily

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyOutput
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Output

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ) (hP : 0 < P)

local notation "SeedState" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "Family" => PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)

noncomputable def physicalFamilyFinalValue (rootQ : TargetInterval target.length)
    (input : SeedState × Family) : ℝ :=
  localRequestValue source target N P ell exponent H (ell ^ 80) T S (H ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
    (physicalFamilyGroup target N P ell exponent H (ell ^ 80) passes (H ^ 2) input.2)
    (physicalFamilyInteger source target N P ell exponent H (ell ^ 80) T S passes (H ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta hP input.2
      (clampedSeedNat input.1))
    (clampedSeedNat input.1)
    (PhysicalTableRequest.refinement passes 0
      (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit) T S rootQ)

noncomputable def physicalFamilyFinalAnswer (rootQ : TargetInterval target.length)
    (input : SeedState × Family) : ℕ :=
  if source = substring target rootQ.lo rootQ.hi then 0 else
    integerAnswer N (physicalFamilyFinalValue source target N P T S H hP rootQ input)

end Output

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyRuntime
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The source family is the projection of terminating rejection-sampling executions. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Runtime

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "SeedState" => ClampedPhysicalSeed M J target.length N

instance physicalFamilyRuntimeLaw_probability (incoming : Measure SeedState)
    [IsProbabilityMeasure incoming] :
    IsProbabilityMeasure (physicalFamilyRuntimeLaw (R := R) target N P H incoming) := by
  unfold physicalFamilyRuntimeLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)



end Runtime

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalUniformAccuracy
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory Filter

section Uniform

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H B : ℕ)
  [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : PhysicalEntry M J target.length → ℕ)

instance physicalUniformOutcome_measurableSingleton :
    MeasurableSingletonClass (PhysicalUniformOutcome (M := M) (J := J) (R := R) target N P H) := by
  refine ⟨fun outcome => ?_⟩
  exact measurableSet_sum_iff.mpr
    ⟨(Set.to_countable _).measurableSet, (Set.to_countable _).measurableSet⟩

instance physicalUniformLaw_probability (epsilon : BinaryFraction) :
    IsProbabilityMeasure (physicalUniformLaw (R := R) source target N P H B depth epsilon) := by
  classical
  unfold physicalUniformLaw
  split
  · exact Measure.isProbabilityMeasure_map measurable_inr.aemeasurable
  · infer_instance

end Uniform

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalCoarseExecution
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open MeasureTheory

section Execution
variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H B : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)





variable [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]

noncomputable def physicalCoarseExecutionLaw :
    Measure (PhysicalCoarseExecution (R := R) source target N P H B depth) :=
  (coarseFullSeedMeasure B depth
    (fun entry => physicalSource source entry.1)
    (fun entry => substring target entry.2.lo entry.2.hi)).prod
  (rejectionRuntimeArrayLaw (physicalFamilyRange (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H
      (inputSmallLog N ^ 80) (computedSeedPassCount N) (H ^ 2)))

end Execution
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyCoarseWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Coarse

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw

noncomputable def physicalFamilyCoarseQuery
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    FiniteQuery (PhysicalEntry M J target.length) :=
  chargedRandomCoarseQuery source target N P ell exponent H (ell ^ 80) T S (passes + 1)
    copies factor multiplier tau eta kappa delta readGroup readInteger answer root

variable (B : ℕ) [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : PhysicalEntry M J target.length → ℕ)

noncomputable def physicalFamilyCoarseWork
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S)
    (coarse : PhysicalCoarseDraw source target B depth) : ℝ :=
  coarseFirstRequestWork N B depth
    (fun entry => physicalSource source entry.1)
    (fun entry => substring target entry.2.lo entry.2.hi)
    (physicalFamilyCoarseQuery source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw root) coarse

end Coarse

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyMemo
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! One binary memo stores independent scalar draws, coarse values, and
all recursive tables.  The raw implementation preserves the exact
reference trace; normalization is justified on its reachable values. -/

namespace EditApproximation

section Family
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)





def queryFamilyMemoNormalized (base : List Bool) (hbase : 0 < bitWordValue base)
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :=
  rankedNormalizeBody (SourceRanked.rank ChargedPhysicalRequest.rank)
    (queryFamilyMemoRaw source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw)
    base hbase (queryFamilyMemoRemaining (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) key

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedLocalGroupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree cap on all whole-cell loops at a query. Distance scales
enter through their bit length; their numeric size is never charged. -/

namespace EditApproximation

def localGroupMajorant (F thetaPow B eM eF X : ℕ) : ℕ :=
  let K := (32 * F + 2) * thetaPow + 2
  let scale := 2000 * (B + 4) ^ 2 + 500 * (B + 1) ^ 2 +
    BinaryFraction.targetCellsBitBudget K K (4 * B + 40) +
    K ^ 2 * (BinaryFraction.groupScalesBitBudget eM B eF + X ^ preparedCellGroupBitDegree + 4) + B + 4
  (B + 1) * (BinaryFraction.localEligibilityBitBudget (B + 3) + scale + B + 4 + K ^ 2 + 3) +
    (B + 1) + B + 2

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedKernelPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One fixed degree bounds every Boolean operation of the complete local
refinement kernel, after primitive word and finite-grid bounds are supplied. -/

namespace EditApproximation

attribute [local irreducible] representativeShellDegree preparedLocalGroupBitDegree
  onlineShellDegree physicalShellDegree

def preparedKernelBitDegree : ℕ :=
  max representativeShellDegree (max preparedLocalGroupBitDegree (max onlineShellDegree physicalShellDegree)) + 3

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerQueryWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter MeasureTheory

def integerQueryLocalWork (source target : List ℤ) (N : ℕ) :=
  computedQueryLocalWork (source.map integerSymbolCode) (target.map integerSymbolCode) N
    (integerOccurrenceIndex source target) (integerInputSymbolBits source target) (integerInputPositionBits target)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerBinaryAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open MeasureTheory

/-- The uniform implementation uses exact dynamic programming below the
proved cutoff and the evaluated binary memo above it. -/
noncomputable def integerBinaryAnswer (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) : ℕ :=
  if physicalLargeInput N epsilon then
    match outcome with
    | .inl _ => exactSuffixAnswer (source.map integerSymbolCode) (target.map integerSymbolCode)
    | .inr execution => bitWordValue (integerBinaryOutput source target N
        (computedExecutionAccepted _ _ N execution)).1
  else exactSuffixAnswer (source.map integerSymbolCode) (target.map integerSymbolCode)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerBinaryWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter MeasureTheory

/-- Full integer-input runtime with concrete local, setup, and final-output routines. -/
noncomputable def integerBinaryWork (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction) :=
  computedFullOutputWork (source.map integerSymbolCode) (target.map integerSymbolCode) N
    (integerQueryLocalWork source target N) (integerPreevaluationWork source target N epsilon)
    (computedQuerySetupWithWork N).2 (fun input => (integerBinaryOutput source target N input).2)
    (N + 1)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerBinarySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

/-- Final conversion allocates only its division and clamping workspace. -/
def integerFinalAllocation (source target : List ℤ) (N : ℕ)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) : ℕ :=
  if source.map integerSymbolCode = target.map integerSymbolCode then 0 else
    BinaryFraction.finalAnswerAllocation N
      (computedQueryMemoResult (source.map integerSymbolCode) (target.map integerSymbolCode) N
        (integerOccurrenceIndex source target) (integerInputSymbolBits source target)
        (integerInputPositionBits target) input).value

/-- Scans and word-RAM preprocessing reserve eight scalar/control cells per
charged step. Retained input/index cells are counted separately. Numerical
setup, local programs and coarse initialization use their explicit allocation
counters. Streaming samplers reuse a bounded buffer, without storing failed
trial counts or failed words. -/
noncomputable def integerAcceptedSpaceTerms (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) : List ℕ :=
  let x := source.map integerSymbolCode
  let y := target.map integerSymbolCode
  [8 * integerPreevaluationWork source target N epsilon,
   2 * integerStoredDataSpace source target,
   computedQuerySetupAllocation N,
   (computedQueryMemoResult x y N (integerOccurrenceIndex source target)
     (integerInputSymbolBits source target) (integerInputPositionBits target) input).memory.fractionStorage,
   computedQueryTemporaryCells x y N (integerOccurrenceIndex source target)
     (integerInputSymbolBits source target) (integerInputPositionBits target) input,
   computedFamilyCoarseCopyStorage x y N input,
   computedFamilyCoarseArrayCapacity x y N input,
   computedFamilyCoarseScratchCapacity x y N input,
   computedFamilyCoarseControlCapacity x y N input,
   4 * (inputHeight N + (integerParameters N).B + 4),
   integerFinalAllocation source target N input,
   8 * (N + 1)]

/-- The space bound applies to all outcomes, including null-probability
outcomes. The exact branch uses the concrete suffix-DP allocation counter. -/
noncomputable def integerBinarySpace (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) : ℕ :=
  if physicalLargeInput N epsilon then
    match outcome with
    | .inl _ => 8 * integerPreevaluationWork source target N epsilon +
        2 * integerStoredDataSpace source target +
        suffixDPAllocation (source.map integerSymbolCode) (target.map integerSymbolCode) + 8 * (N + 1)
    | .inr execution => (integerAcceptedSpaceTerms source target N epsilon
        (computedExecutionAccepted _ _ N execution)).sum
  else 8 * integerPreevaluationWork source target N epsilon +
    2 * integerStoredDataSpace source target +
    suffixDPAllocation (source.map integerSymbolCode) (target.map integerSymbolCode) + 8 * (N + 1)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_ConcreteFootprintBridges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.EditApproximation

universe u_1 u_2

def groupHeapTransportBridge (M J N n exponent F Q R B b c : ℕ) (h : b = c)
    (actual : BitPhysicalGroupQueries M J N n exponent F Q R B b)
    (heap : ∀ s j, BitQuery.Heap (actual s j)) :
    ∀ s j, BitQuery.Heap
      ((Eq.mp (congrArg (BitPhysicalGroupQueries M J N n exponent F Q R B) h) actual) s j) := by
  cases h
  exact heap

def groupFootprintTransportBridge (M J N n exponent F Q R B b c : ℕ) (h : b = c)
    (actual : BitPhysicalGroupQueries M J N n exponent F Q R B b)
    (heap : ∀ s j, BitQuery.Footprint (actual s j)) :
    ∀ s j, BitQuery.Footprint
      ((Eq.mp (congrArg (BitPhysicalGroupQueries M J N n exponent F Q R B) h) actual) s j) := by
  cases h
  exact heap

-- Supply case arguments directly so inference does not normalize indexed branch values.
universe u

set_option maxHeartbeats 2000000

def scalarGroupFootprintBridge (M J N n exponent F Q R B : ℕ)
    (node : PhysicalInternalNode M J) (time : Fin R) (b : ℕ) (cell : ℕ × ℕ) :
    ∀ s j, BitQuery.Footprint (queryPhysicalScalarGroupQueries M J N n exponent F Q R B node time b cell s j) := by
  intro s j
  refine (congrArg BitQuery.Footprint (congrArg
    (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j)
    (queryPhysicalScalarGroupQueries.eq_1 M J N n exponent F Q R B node time b cell))).mpr ?_
  split
  · rename_i hb
    split
    · rename_i hc
      let key : PhysicalLocalGroupKey M J N n exponent :=
        (node, physicalScaleIndex N b ((queryScalePresentWithWork_value N b).mp hb),
          ⟨cell.1, Nat.lt_succ_of_le ((queryCellValidWithWork_value n exponent cell).mp hc).1⟩,
          ⟨cell.2, Nat.lt_succ_of_le ((queryCellValidWithWork_value n exponent cell).mp hc).2⟩)
      exact groupFootprintTransportBridge M J N n exponent F Q R B _ _
        (physicalScaleIndex_get N b ((queryScalePresentWithWork_value N b).mp hb))
        (queryPhysicalScalarGroupQueriesAt M J N n exponent F Q R B key time)
        (fun s j => (congrArg BitQuery.Footprint
          (queryPhysicalScalarGroupQueriesAt.eq_1 M J N n exponent F Q R B key time s j)).mpr
            (queryPhysicalScalarReadFootprint M J N n exponent F Q R B
              ⟨Sum.inr key, ⟨time, ⟨s, j⟩⟩⟩)) s j
    · exact .done _
  · exact .done _

def scalarOnlineFootprintBridge (M J N n exponent F Q R B : ℕ)
    (node : PhysicalInternalNode M J) (time : Fin R) (key : ℕ × TargetInterval n) (range : ℕ) :
    BitQuery.Footprint (queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range) := by
  refine (congrArg BitQuery.Footprint
    (queryPhysicalScalarOnlineRead.eq_1 M J N n exponent F Q R B node time key range)).mpr ?_
  refine BitQuery.Footprint.chargeOf
    (queryScalePresentAllocation N key.1 + queryRangeValidAllocation B range) ?_
  split
  · rename_i hb
    split
    · rename_i hr
      exact queryPhysicalScalarReadFootprint M J N n exponent F Q R B
        ⟨.inl ((node, physicalScaleIndex N key.1 ((queryScalePresentWithWork_value N key.1).mp hb), key.2),
          positiveDrawRangeOfLE B range ((queryRangeValidWithWork_value B range).mp hr).1
            ((queryRangeValidWithWork_value B range).mp hr).2), time⟩
    · exact .done _
  · exact .done _

end OAI.EditApproximation
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_FootprintMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.EditApproximation
open Filter MeasureTheory
attribute [local instance] queryRoundsNeZero

def computedQueryTemporaryCellsFootprint (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) : ℕ :=
  BitQuery.Footprint.rankedBitMemoCells (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input)
    (computedQueryMemoFootprint source target N occurrence symbolBits positionBits input)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (fun key => (computedFamilyMemoCodeWithWork source target N (inputHeight N ^ 2) key).2)
    (.inr (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
      (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length))) .empty

noncomputable def integerAcceptedSpaceTermsFootprint (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) : List ℕ :=
  let x := source.map integerSymbolCode
  let y := target.map integerSymbolCode
  [8 * integerPreevaluationWork source target N epsilon,
   2 * integerStoredDataSpace source target,
   computedQuerySetupAllocation N,
   (computedQueryMemoResult x y N (integerOccurrenceIndex source target)
     (integerInputSymbolBits source target) (integerInputPositionBits target) input).memory.fractionStorage,
   computedQueryTemporaryCellsFootprint x y N (integerOccurrenceIndex source target)
     (integerInputSymbolBits source target) (integerInputPositionBits target) input,
   computedFamilyCoarseCopyStorage x y N input,
   computedFamilyCoarseArrayCapacity x y N input,
   computedFamilyCoarseScratchCapacity x y N input,
   computedFamilyCoarseControlCapacity x y N input,
   4 * (inputHeight N + (integerParameters N).B + 4),
   integerFinalAllocation source target N input,
   8 * (N + 1)]

noncomputable def integerBinarySpaceFootprint (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) : ℕ :=
  if physicalLargeInput N epsilon then
    match outcome with
    | .inl _ => 8 * integerPreevaluationWork source target N epsilon +
        2 * integerStoredDataSpace source target +
        suffixDPAllocation (source.map integerSymbolCode) (target.map integerSymbolCode) + 8 * (N + 1)
    | .inr execution => (integerAcceptedSpaceTermsFootprint source target N epsilon
        (computedExecutionAccepted _ _ N execution)).sum
  else 8 * integerPreevaluationWork source target N epsilon +
    2 * integerStoredDataSpace source target +
    suffixDPAllocation (source.map integerSymbolCode) (target.map integerSymbolCode) + 8 * (N + 1)

end OAI.EditApproximation
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_RawBandPipelineFootprintBridges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false



namespace OAI.EditApproximation

universe u v

def queryChargedFamilyTableGen
    (qfba : type_of% @queryFamilyBoundedActive.{0})
    {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
    (source target : List ℕ) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF) (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction)
    (multiplier : ℕ → ℕ) (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S}) :
    BitQuery (ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent)) BinaryFraction :=
  let index := wordLEWithWork parent.val.index.bits T.bits
  .charge (index.2 + 1)
    (if hi : index.1 = true then
      BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
        (queryChargedWarmup source target N P F (A parent.val.pass) (a parent.val.pass) multiplier
          parent occurrence symbolBits positionBits)
    else let depth := binaryNaturalCompareWithWork parent.val.node.1.val J
      .charge (depth.2 + 1)
        (if hb : depth.1 = .lt then
          let interval := physicalSourceInterval source.length parent.val.node
          let length := saturatingSubtractWithWork interval.hi interval.lo
          let short := wordLEWithWork length.1 [true]
          .charge (length.2 + short.2 + 1)
            (if short.1 then
              BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
                (queryPhysicalInitial source target N P F (A parent.val.pass) (a parent.val.pass)
                  multiplier parent occurrence symbolBits positionBits parent.val.state)
            else BitQuery.mapKeysWithWork
              (fun key => (Sum.map id (fun child =>
                ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩)
                key, 1))
              (qfba (R := R) source target N P F exponent H Q eM eF hP hM hF
                tau (a parent.val.pass) eta kappa delta T S passes copies parent
                (Nat.lt_of_not_ge (fun h => hi ((queryNaturalLEWithWork_value parent.val.index T).mpr h)))
                ((binaryNaturalCompareWithWork_lt _ _).mp hb)))
        else BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
          (queryPhysicalInitial source target N P F (A parent.val.pass) (a parent.val.pass)
            multiplier parent occurrence symbolBits positionBits parent.val.state)))

def queryChargedFamilyTableFootprintGen
    (qfba : type_of% @queryFamilyBoundedActive.{0})
    (qfbaF : QueryFamilyBoundedActiveFootprintType qfba)
    {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
    (source target : List ℕ) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF) (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction)
    (multiplier : ℕ → ℕ) (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (parent : { r : PhysicalTableRequest M J target.length //
      PhysicalTableRequest.Bounded (passes + 1) copies T S r }) :
    (queryChargedFamilyTableGen qfba (R := R) source target N P F exponent H Q eM eF hP hM hF A a
      tau eta kappa delta multiplier occurrence symbolBits positionBits parent).Footprint := by
  have hinit := queryPhysicalInitialFootprint source target N P F (A parent.val.pass) (a parent.val.pass)
    multiplier parent occurrence symbolBits positionBits parent.val.state
  unfold queryChargedFamilyTableGen
  refine BitQuery.Footprint.chargeOf (naturalWordLEAllocation parent.val.index.bits T.bits) ?_
  split
  · exact (queryChargedWarmupFootprint source target N P F (A parent.val.pass) (a parent.val.pass)
      multiplier parent occurrence symbolBits positionBits).mapKeysWithWork _ (fun _ => 1)
  · refine BitQuery.Footprint.chargeOf (parent.val.node.1.val.bits.length + J.bits.length) ?_
    split
    · let interval := physicalSourceInterval source.length parent.val.node
      refine BitQuery.Footprint.chargeOf (saturatingSubtractAllocation interval.hi interval.lo +
        naturalWordLEAllocation (saturatingSubtractWithWork interval.hi interval.lo).1 [true]) ?_
      split
      · exact hinit.mapKeysWithWork _ (fun _ => 1)
      · exact (qfbaF (R := R) source target N P F exponent H Q eM eF hP hM hF
          tau (a parent.val.pass) eta kappa delta T S passes copies parent _ _).mapKeysWithWork _
          (fun _ => 1)
    · exact hinit.mapKeysWithWork _ (fun _ => 1)

end OAI.EditApproximation
end


