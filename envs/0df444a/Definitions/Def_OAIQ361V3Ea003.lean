-- Prove2me | Definitions.Def_OAIQ361V3Ea003
-- name    : OAIQ361V3Ea003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T16:27:19.547211+00:00
-- url     : https://prove2.me/theorems/a5ea0488-95c1-4b59-9a82-7db81a6ddd9e
-- title:
--   Definitions bundle OAIQ361V3Ea003 of the split of OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 39 declarations of OpenAI's Lean: 23 definitions, 2 instances and 14 theorems. The definitions and types are `OAI.EditApproximation.BinaryFraction.historyChildRun`, `OAI.EditApproximation.BinaryFraction.onlineCostCore`, `OAI.EditApproximation.BinaryFraction.preparedOnlineBandReference`, `OAI.EditApproximation.BinaryFraction.preparedOnlineReadCore`, `OAI.EditApproximation.initialWarmupEnvironment`, `OAI.EditApproximation.mapCommonTrace`, `OAI.EditApproximation.materializedBandActionWithWork`, `OAI.EditApproximation.parentGroupDraw`, `OAI.EditApproximation.parentOnlineDraw`, `OAI.EditApproximation.physicalCurrentReadWeight`, `OAI.EditApproximation.physicalEarlierReadWeight`, `OAI.EditApproximation.physicalFamilyLaw`, `OAI.EditApproximation.physicalProgramOnlineGuard`, `OAI.EditApproximation.physicalRepresentativeFin`, `OAI.EditApproximation.physicalSeedGood`, `OAI.EditApproximation.queryActiveChildMap`, `OAI.EditApproximation.queryActiveOracle`, `OAI.EditApproximation.queryActiveReadWork`, `OAI.EditApproximation.queryGatherEnvironment`, `OAI.EditApproximation.queryGridPointsWithWork`, `OAI.EditApproximation.queryGroupKeySize`, `OAI.EditApproximation.queryInitialConeProgram`, `OAI.EditApproximation.queryRestrictedPhysicalReadWork`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `EditApproximation_Binary_BinaryOnlineReadCosts`, `EditApproximation_Binary_BinaryPreparedOnline`, `EditApproximation_Binary_BinaryPreparedOnlineReads`, `EditApproximation_Geometry_BandOptimizerWork`, `EditApproximation_Geometry_CommonArrayFinal`, `EditApproximation_Geometry_Leaves`, `EditApproximation_Geometry_LocalGrid`, `EditApproximation_Geometry_LocalRefinementCones`, `EditApproximation_Geometry_ParameterNumericalConstruction`, `EditApproximation_Queries_QueryActiveCost`, `EditApproximation_Queries_QueryBoundedWork`, `EditApproximation_Queries_QueryFamilyNormalize`, `EditApproximation_Queries_QueryGatherPolynomial`, `EditApproximation_Queries_QueryGridCost`, `EditApproximation_Queries_QueryHistoryBounds`, `EditApproximation_Queries_QueryInitialConeProgram`, `EditApproximation_Queries_QueryInitialWarmupPolynomial`, `EditApproximation_Queries_QuerySourceBufferBounds`, `EditApproximation_Refinement_PhysicalBoundsAllSeeds`, `EditApproximation_Refinement_PhysicalInitial`, `EditApproximation_Refinement_PhysicalLocalOnlineEquality`, `EditApproximation_Refinement_PhysicalOnlineLocality`, `EditApproximation_Refinement_PhysicalParentDraw`, `EditApproximation_Refinement_PhysicalRefinementReadWork`, `EditApproximation_Refinement_PhysicalScalarFamilyLaw`, `EditApproximation_Refinement_PhysicalSeedTables`, `EditApproximation_Refinement_PhysicalSelectionProgram`.
--
--   **Imports.** It imports the published bundles `Def_EditApproxScheme_01`, `Def_EditApproxScheme_02`, `Def_EditApproxScheme_03`, `Def_EditApproxScheme_04`, `Def_EditApproxScheme_05`, `Def_EditApproxScheme_06`, `Def_EditApproxScheme_07`, `Def_EditApproxScheme_08`, `Def_EditApproxScheme_10`, `Def_EditApproxScheme_11`, `Def_EditApproxScheme_12`, `Def_EditApproxScheme_13`, `Def_EditApproxScheme_14`, `Def_EditApproxScheme_15` and `Def_EditApproxScheme_16`; the bundles `OAIQ361V3Ea000` and `OAIQ361V3Ea001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ361V3Ea004`; the statements `OAI.EditApproximation.queryFamilyBoundedActive_work_bound`, `OAI.EditApproximation.queryLocalBand_work_bound` and `OAI.EditApproximation.queryLocalRandomSources_work_bound`; the proofs of `OAI.EditApproximation.BinaryFraction.queryLocalRefinement_finish_bounds`, `OAI.EditApproximation.BinaryFraction.queryRawCentersWithWork_bounds`, `OAI.EditApproximation.computedFamilyResult_requests_le`, `OAI.EditApproximation.computedFamilyTree_valid`, `OAI.EditApproximation.computedPhysicalCoarseWork_expected_le`, `OAI.EditApproximation.computedQueryTable_work_width`, `OAI.EditApproximation.computed_chargedRandomGlobalQuery_earlier_reads`, `OAI.EditApproximation.queryChargedFamilyTable_semantic_width`, `OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound`, `OAI.EditApproximation.queryChargedWarmup_refines`, `OAI.EditApproximation.queryFamilyBoundedActive_work_bound`, `OAI.EditApproximation.queryInitialConeProgramAt_work_bound`, `OAI.EditApproximation.queryLocalRandomSources_refines`, `OAI.EditApproximation.queryLocalRandomSources_work_bound` and `OAI.EditApproximation.queryLocalRefinement_work_bound`.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea000
import Definitions.Def_OAIQ361V3Ea001

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Leaves
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Exact interval-tree leaves

An occurrence query gives the exact unit-cost edit distance at a source
leaf of width one (Section 2 of the manuscript).
-/

namespace EditApproximation

open EditDistortion

universe u

/-- One edit can increase the occurrence deficit by at most one. -/
theorem occurrenceDeficit_step {α : Type u} [DecidableEq α]
    (a : α) {x y : List α} (h : Step true x y) :
    occurrenceDeficit a y ≤ occurrenceDeficit a x + 1 := by
  cases h with
  | insert p q b =>
    by_cases ha : a ∈ p ++ q
    · have ha' : a ∈ p ++ b :: q := by
        simp only [List.mem_append, List.mem_cons] at ha ⊢
        tauto
      simp only [occurrenceDeficit, ite_eq_left ha, ite_eq_left ha',
        List.length_append, List.length_cons]
      omega
    · have hup := occurrenceDeficit_le_length a (p ++ b :: q)
      simp only [occurrenceDeficit, ite_eq_right ha, Nat.sub_zero,
        List.length_append, List.length_cons] at hup ⊢
      omega
  | delete p q b =>
    have hup := occurrenceDeficit_le_length a (p ++ q)
    have hlo := length_le_occurrenceDeficit_add_one a (p ++ b :: q)
    simp only [List.length_append, List.length_cons] at hup hlo
    omega
  | substitute _ p q b c =>
    have hup := occurrenceDeficit_le_length a (p ++ c :: q)
    have hlo := length_le_occurrenceDeficit_add_one a (p ++ b :: q)
    simp only [List.length_append, List.length_cons] at hup hlo
    omega

theorem occurrenceDeficit_script {α : Type u} [DecidableEq α]
    (a : α) {x y : List α} {n : ℕ} (h : Script true n x y) :
    occurrenceDeficit a y ≤ occurrenceDeficit a x + n := by
  induction h with
  | nil => omega
  | cons step rest ih =>
    have hs := occurrenceDeficit_step a step
    omega

theorem occurrenceDeficit_le_singleton_edit {α : Type u} [DecidableEq α]
    (a : α) (word : List α) : occurrenceDeficit a word ≤ edit [a] word := by
  have h := occurrenceDeficit_script a (cost_spec (s := true) [a] word)
  simpa [occurrenceDeficit, cost, edit] using h

/-- Executable exact answer for a source interval containing one symbol. -/


theorem singletonCost_eq_edit {α : Type u} [DecidableEq α]
    (a : α) (word : List α) : singletonCost a word = edit [a] word := by
  by_cases hempty : word = []
  · subst word
    have hlo := (cost_length_bounds (s := true) [a] []).1
    have hup := edit_le_max_length [a] ([] : List α)
    have hlo' : 1 ≤ edit [a] ([] : List α) := by
      simpa [cost, edit] using hlo
    have hup' : edit [a] ([] : List α) ≤ 1 := by simpa using hup
    simpa [singletonCost] using Nat.le_antisymm hlo' hup'
  · rw [singletonCost, ite_eq_right hempty]
    apply Nat.le_antisymm (occurrenceDeficit_le_singleton_edit a word)
    by_cases ha : a ∈ word
    · have hs : [a].Sublist word := List.singleton_sublist.mpr ha
      have hedit : edit [a] word = edit word [a] := cost_symm _ _
      rw [hedit]
      simpa only [occurrenceDeficit, ite_eq_left ha, List.length_singleton] using
        edit_sublist_le hs
    · have hlen : 1 ≤ word.length := by
        have hpos := List.length_pos_iff.mpr hempty
        omega
      have hup := edit_le_max_length [a] word
      simpa only [occurrenceDeficit, ite_eq_right ha, Nat.sub_zero,
        List.length_singleton, max_eq_right hlen] using hup

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Direct enumeration of a local grid square

The algorithm enumerates bounded ranges of grid indices. It does not
scan the unrelated target positions. The completeness theorem includes
boundary states and intervals with equal endpoints.
-/

namespace EditApproximation



theorem localTargetStates_complete {n g radius : ℕ} (hg : 0 < g)
    (q r : TargetInterval n) (hlo : Nat.dist q.lo r.lo ≤ radius)
    (hhi : Nat.dist q.hi r.hi ≤ radius) (hgrid : g ∣ r.lo ∧ g ∣ r.hi) :
    r ∈ localTargetStates n g radius q := by
  have hlo' : q.lo - radius ≤ r.lo ∧ r.lo ≤ q.lo + radius := by
    unfold Nat.dist at hlo
    omega
  have hhi' : q.hi - radius ≤ r.hi ∧ r.hi ≤ q.hi + radius := by
    unfold Nat.dist at hhi
    omega
  apply List.mem_flatMap.mpr
  refine ⟨r.lo, gridPointsBetween_complete hg hlo'.1 hlo'.2 hgrid.1, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨r.hi, gridPointsBetween_complete hg hhi'.1 hhi'.2 hgrid.2, ?_⟩
  rw [makeTargetState, dite_eq_left (show r.lo ≤ r.hi ∧ r.hi ≤ n from ⟨r.ordered, r.valid⟩)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandOptimizerWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Reindexing the exact finite optimizer onto an explicit, duplicate-free
coordinate array. The array order is retained throughout the evaluation. -/

namespace EditApproximation

open Finset

def materializedBandActionWithWork {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) (mass : Fin M → ℚ)
    (linear : Fin M × σ → ℚ) (G j : ℕ) : Option (Fin M → σ) × ℕ :=
  let coordinates := listedBandCoordinateVector band
  let vertices := band.map fun action =>
    (action, restrictOptimizerVector coordinates (actionVector mass action))
  materializedSelectionWithWork vertices (restrictOptimizerVector coordinates linear) G j

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual initial table uses exact empty/singleton leaves and local cones elsewhere. -/

namespace EditApproximation

open EditDistortion



theorem shortSourceCost_eq_edit {α : Type*} [DecidableEq α] (source target : List α)
    (hsource : source.length ≤ 1) : shortSourceCost source target = edit source target := by
  cases source with
  | nil =>
    exact (edit_nil_left target).symm
  | cons a rest =>
    have hrest : rest = [] := List.length_eq_zero_iff.mp (by
      simp only [List.length_cons] at hsource
      omega)
    subst rest
    exact singletonCost_eq_edit a target

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalBoundsAllSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegativity and size bounds hold on every seed and every sample outcome. -/

namespace EditApproximation

open Finset

 theorem stageInitial_nonneg_all_seeds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (state : PhysicalEntry M J target.length) :
    0 ≤ stageInitial source target U N P F A state := by
  unfold stageInitial physicalInitialTable
  dsimp only
  split_ifs
  · exact Nat.cast_nonneg _
  · exact localInitialConeTable_nonneg _ _ _ _ _ _ _ _ _

 theorem rationalPhysicalBellman_nonneg {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (hL : 0 ≤ L) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (hinitial : ∀ state, 0 ≤ initial state)
    (value : PhysicalEntry M J target.length → ℚ) (hvalue : ∀ state, 0 ≤ value state)
    (state : PhysicalEntry M J target.length) :
    0 ≤ rationalPhysicalBellman source target P L initial representatives value state := by
  unfold rationalPhysicalBellman
  dsimp only
  split_ifs
  · exact hinitial state
  · apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨hinitial state, ?_⟩
    intro v hv
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
    unfold rationalActionValue
    exact add_nonneg (add_nonneg (mul_nonneg hL (Nat.cast_nonneg _))
      (rationalActualWideActions_connection_nonneg _ _ _ action ha)) (sum_nonneg fun i _ => hvalue _)
  · exact hinitial state

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalRefinementCones
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Direct local enumeration computes the complete refinement Bellman cone
on a spatially regular initial table. Its finite definition applies to every seed. -/

namespace EditApproximation

open Finset



theorem representativeList_conditions {n N P F : ℕ} (a : ℚ)
    (initial : TargetInterval n → ℚ) {b : ℕ} {r : TargetInterval n}
    (hrep : (b, r) ∈ representativeList N P F a initial) :
    b ∈ dyadicScales N ∧ seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi ∧
      (b : ℚ) / (4 * a) ≤ initial r ∧ initial r ≤ 8 * F * b := by
  obtain ⟨b', hb', hrep⟩ := List.mem_flatMap.mp hrep
  obtain ⟨r', hr', heq⟩ := List.mem_map.mp hrep
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact ⟨hb', of_decide_eq_true (List.mem_filter.mp hr').2⟩

theorem localRefinementRepresentatives_complete {n N P F b : ℕ} {a : ℚ}
    (initial : TargetInterval n → ℚ) (q r : TargetInterval n)
    (hw : 0 < initial q) (ha : 1 ≤ a) (hF : 1 ≤ F)
    (hspatial : |initial q - initial r| ≤ 32 * F * targetEndpointDistance q r)
    (hrep : (b, r) ∈ representativeList N P F a initial)
    (hcompetitive : 128 * (F : ℚ) * targetEndpointDistance q r ≤ initial q) :
    (b, r) ∈ localRefinementRepresentatives N P F a initial q := by
  have hconditions := representativeList_conditions a initial hrep
  have hnumeric := refinement_cone_locality_numeric hw ha (show (1 : ℚ) ≤ F by exact_mod_cast hF)
    (Nat.cast_nonneg (α := ℚ) (targetEndpointDistance q r)) hspatial hconditions.2.2.2
    le_rfl hcompetitive
  have hdist : targetEndpointDistance q r ≤ ⌈initial q⌉₊ := by
    have hceil : initial q ≤ (⌈initial q⌉₊ : ℚ) := Nat.le_ceil _
    exact_mod_cast hnumeric.2.2.trans hceil
  apply List.mem_flatMap.mpr
  refine ⟨b, List.mem_filter.mpr ⟨hconditions.1, decide_eq_true ⟨hnumeric.1, hnumeric.2.1⟩⟩, ?_⟩
  apply List.mem_map.mpr
  refine ⟨r, List.mem_filter.mpr ⟨?_, decide_eq_true hconditions.2.2.2⟩, rfl⟩
  apply localTargetStates_complete (by unfold seedGridSpacing; omega) q r
    (by unfold targetEndpointDistance at hdist; omega)
    (by unfold targetEndpointDistance at hdist; omega)
    ⟨hconditions.2.1, hconditions.2.2.1⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSelectionProgram
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

/-- The literal online query uses its one rounded center at each allowed
scale, with the scale window tested against the literal initial table. -/
def physicalProgramOnlineGuard (node : PhysicalNode M J) (q : TargetInterval target.length)
    (br : ℕ × TargetInterval target.length) : Prop :=
  br.2 = roundInterval (seedGridSpacing br.1 P) q ∧
    stageInitial source target U N P F A (node, q) / (16 * F) ≤ br.1 ∧
    (br.1 : ℚ) ≤ 8 * refinementFactor A F * stageInitial source target U N P F A (node, q)

instance physicalProgramOnlineGuard_decidable (node : PhysicalNode M J) (q : TargetInterval target.length)
    (br : ℕ × TargetInterval target.length) :
    Decidable (physicalProgramOnlineGuard source target U N P F A node q br) := by
  unfold physicalProgramOnlineGuard
  infer_instance


end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalOnlineLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal query-filtered online loop has at most one candidate per scale. -/

namespace EditApproximation

open Finset

theorem representativeList_scale_mem {n N P F : ℕ} (a : ℚ)
    (initial : TargetInterval n → ℚ) {br : ℕ × TargetInterval n}
    (hbr : br ∈ representativeList N P F a initial) : br.1 ∈ dyadicScales N := by
  obtain ⟨b, hb, hbr⟩ := List.mem_flatMap.mp hbr
  obtain ⟨r, _, heq⟩ := List.mem_map.mp hbr
  exact (congrArg Prod.fst heq) ▸ hb

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedOnline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The keyed online branch executes the actual endpoint grids before
its guard and optimizer. The original finite source range is preserved. -/

namespace EditApproximation
namespace BinaryFraction

def preparedOnlineBandReference {M n : ℕ} (center : TargetInterval n) (b G : ℕ) (hG : 0 < G)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ []) (t integer : ℕ) :
    PhysicalRationalAction M n :=
  sharedBandRationalAction center
    (finiteOptimizerActionDraw band hne (bandChildEnvelope b band (fun i q => (initial i q).value))
      (rationalOnlineLinear eta.value kappa.value
        (childGain (bandChildEnvelope b band (fun i q => (initial i q).value))
          (fun s coordinate => (table s coordinate).value))
        (childDecrement (bandChildEnvelope b band (fun i q => (initial i q).value))
          (fun s coordinate => (table s coordinate).value)) t)
      G (G ^ 80) (boundedOnlineInteger _ (optimizerTriangularMass_positive _ (pow_pos hG _)) integer))

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedOnlineReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prepared online candidate executes its band reads, guard reads,
and historical reads. The accepted source integer and counted coordinate
representation are exactly the original ones. -/

namespace EditApproximation
namespace BinaryFraction

def preparedOnlineReadCore {n M : ℕ} {Action : Type*} (H integer : ℕ)
    (band : List (Fin M → TargetInterval n) × ℕ) (guard : Bool × ℕ)
    (sample : (xs : List (Fin M → TargetInterval n)) → xs ≠ [] → (G : ℕ) →
      Fin (optimizerTriangularMass (G ^ 80)) → Action × ℕ) : Option Action × ℕ :=
  let setup := onlineIndexSetupWithWork H band.1
  let accepted := reduceOnlineIntegerWithWork (setup.1 ^ 80) (by
    rw [onlineIndexSetupWithWork_value]
    positivity) integer
  if hband : band.1 = [] then (none, band.2 + setup.2 + accepted.2 + 1) else
    if guard.1 then
      let sampled := sample band.1 hband setup.1 accepted.1
      (some sampled.1, band.2 + setup.2 + accepted.2 + guard.2 + sampled.2 + 2)
    else (none, band.2 + setup.2 + accepted.2 + guard.2 + 1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineReadCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Online sampler arithmetic and lookup costs share one linear read factor. -/

namespace EditApproximation
namespace BinaryFraction

def onlineCostCore {n M : ℕ} {Action : Type*} (H integer : ℕ)
    (band : List (Fin M → TargetInterval n) × ℕ) (guard : Bool × ℕ)
    (sample : (xs : List (Fin M → TargetInterval n)) → xs ≠ [] → (G : ℕ) →
      Fin (optimizerTriangularMass (G ^ 80)) → Action × ℕ) : Option Action × ℕ :=
  let setup := onlineIndexSetupWithWork H band.1
  let accepted := reduceOnlineIntegerWithWork (setup.1 ^ 80) (by
    rw [onlineIndexSetupWithWork_value]
    positivity) integer
  if hband : band.1 = [] then (none, band.2 + setup.2 + accepted.2 + 1) else
    if guard.1 then
      let sampled := sample band.1 hband setup.1 accepted.1
      (some sampled.1, band.2 + setup.2 + accepted.2 + guard.2 + sampled.2 + 2)
    else (none, band.2 + setup.2 + accepted.2 + guard.2 + 1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalParentDraw
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

def parentOnlineDraw {R O M K : ℕ} [NeZero R] {count : Fin K → ℕ}
    (ω : ParentRandomSpace R O M K count) (t : ℕ) : Fin O := ω.1 (Fin.ofNat R t)

def parentGroupDraw {R O M K : ℕ} [NeZero R] {count : Fin K → ℕ}
    (ω : ParentRandomSpace R O M K count) (t : ℕ) : ParentGroupDraw M K count := ω.2 (Fin.ofNat R t)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CommonArrayFinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A final independent draw may be stored as the last array row. These
maps expose the literal product law used by the scheduled seed passes. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

variable {Seed Ω Δ : Type}

def mapCommonTrace (f : Ω → Δ) : (n : ℕ) →
    CommonSeedTrace Seed (fun _ => Ω) n → CommonSeedTrace Seed (fun _ => Δ) n
  | 0, seed => seed
  | n + 1, trace => (mapCommonTrace f n trace.1, f trace.2)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementReadWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Split the literal recursive reads by the unified table index. The
current-index reads are physical-child requests; initial data, warmup
mass and old history have strictly smaller indices. -/

namespace EditApproximation

def physicalCurrentReadWeight {M J ny : ℕ} (index : ℕ)
    (request : PhysicalTableRequest M J ny) : ℕ := if request.index = index then 1 else 0

def physicalEarlierReadWeight {M J ny : ℕ} (index : ℕ)
    (request : PhysicalTableRequest M J ny) : ℕ := if request.index < index then 1 else 0

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalOnlineEquality
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

variable {α : Type*}
  [DecidableEq α]
  {M J R : ℕ}
  [NeZero R]
  (source target : List α)
  (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent H T : ℕ)
  (A tau eta kappa : ℚ)

local notation "representatives" => stageRepresentatives source target U N P F A

noncomputable def physicalRepresentativeFin (node : PhysicalNode M J)
    (br : ℕ × TargetInterval target.length) (hbr : br ∈ representatives node) :
    Fin (representatives node).length := Classical.choose (List.mem_iff_get.mp hbr)

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterNumericalConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



 @[simp] theorem rationalParametersWithWork_value (ell : ℕ) :
    (rationalParametersWithWork ell).1 = rationalParameters ell := by
  simp only [rationalParametersWithWork, parameterPowerWithWork_spec, rationalParameters, Nat.cast_pow]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGridCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A scale guard bounds the number of grid points even when the center
radius is as large as the input.  These bounds include construction of
all points, before subsequent eligibility filtering. -/

namespace EditApproximation

def queryGridPointsWithWork {n : ℕ} (P b radius : ℕ) (q : TargetInterval n) :
    List (TargetInterval n) × ℕ :=
  let spacing := seedGridSpacingWithWork b P
  let points := gridStateBoxWithWork n (bitWordValue spacing.1) radius q.lo q.hi
  (points.1, spacing.2 + points.2 + 1)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistoryBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cost of generating the earlier-history input list from child grids.
The bound counts the actual nested lists before duplicate removal. -/

namespace EditApproximation

namespace BinaryFraction

section History
variable {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx) (P history : ℕ)
  (representatives : List (ℕ × TargetInterval ny)) (G C : ℕ)
  (hgrid : ∀ br ∈ representatives, ∀ i : Fin M,
    (wideChildGridWithWork parent br.2 br.1 P i).1.length ≤ G)
  (hwork : ∀ br ∈ representatives, ∀ i : Fin M,
    (wideChildGridWithWork parent br.2 br.1 P i).2 ≤ C)

def historyChildRun (br : ℕ × TargetInterval ny) (i : Fin M) :=
  let states := wideChildGridWithWork parent br.2 br.1 P i
  let times := arithmeticFlatMapWithWork (fun t =>
    arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1) (List.range history)
  (times.1, states.2 + times.2 + history + 2)

end History
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceBufferBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Random-source lookups are charged at the bounded coordinates actually
consumed by the local loops. No bound is assumed on all natural keys. -/

namespace EditApproximation

def queryGroupKeySize {M F Q : ℕ} (key : GroupScalarKey M F Q) : ℕ :=
  Nat.size key.1.1 + Nat.size key.1.2.1 + Nat.size key.1.2.2 +
    Nat.size key.2.1.val + Nat.size key.2.2.val

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBoundedWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section Body
variable {σ : Type*} {M J n : ℕ} (passes copies T S : ℕ)
  (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})

def queryRestrictedPhysicalReadWork (readWork : QueryBoundedChild (σ := σ) passes copies T S parent → ℕ) :
    QueryPhysicalChild (σ := σ) passes copies T S parent → ℕ :=
  BitQuery.restrictedReadWork _ (querySupportedChildWithWork passes copies T S parent)
    (querySupportedChildWithWork_value passes copies T S parent)
    (fun key => 1 + readWork (SourceRanked.supportedChildMap (PhysicalTableRequest.combinedRank T S)
      (PhysicalTableRequest.Bounded passes copies T S) parent key))

end Body
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryActiveCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Transport
variable {M J n : ℕ} (T : ℕ) (request : PhysicalTableRequest M J n)
  (hindex : T < request.index)

include hindex in
theorem queryRefinementRequest_eq :
    PhysicalTableRequest.refinement request.pass request.copy request.node T (request.index - T)
      request.state = request := by
  have hi : T + (request.index - T) = request.index := by omega
  unfold PhysicalTableRequest.refinement
  rw [hi]

def queryActiveChildMap {σ : Type*} (S : ℕ) :
    Sum σ {child : PhysicalTableRequest M J n // child.combinedRank T S <
      (PhysicalTableRequest.refinement request.pass request.copy request.node T (request.index - T)
        request.state).combinedRank T S} →
    Sum σ {child : PhysicalTableRequest M J n // child.combinedRank T S < request.combinedRank T S} :=
  Sum.map id (fun child => ⟨child.val, by simpa only [queryRefinementRequest_eq T request hindex] using child.property⟩)

def queryActiveOracle {σ : Type*} (S : ℕ)
    (oracle : Sum σ {child : PhysicalTableRequest M J n // child.combinedRank T S < request.combinedRank T S} →
      BinaryFraction) := fun key => oracle (queryActiveChildMap T request hindex S key)

def queryActiveReadWork {σ : Type*} (S : ℕ)
    (readWork : Sum σ {child : PhysicalTableRequest M J n // child.combinedRank T S < request.combinedRank T S} →
      ℕ) := fun key => 1 + readWork (queryActiveChildMap T request hindex S key)

end Transport

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialConeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The initial-cone program first reads its seed, constructs the actual
raw-center list, gathers its answers, and executes the cached Boolean
initial kernel with that finite buffer. -/

namespace EditApproximation

section Initial
variable {ι α : Type*} (source target : List α)
  (N P F : ℕ) (hP : 0 < P) (A a : BinaryFraction)
  (reader : TargetInterval target.length → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)



def queryInitialConeProgram : BitQuery ι BinaryFraction :=
  queryInitialConeProgramAt source.length N P F A a reader q

end Initial
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete mixed memo is normalized on the physical
table grid.  Its actual ranked binary values and adaptive reference trace
agree on every coarse seed and every finite scalar draw. -/

namespace EditApproximation

theorem familyBase_pos (ell : ℕ) (base : List Bool)
    (hbase : bitWordValue base = ell ^ 10 + 1) : 0 < bitWordValue base := by
  rw [hbase]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGatherPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite polynomial certificate for the complete adaptive gather cost.
The four kernel bounds and the two Cartesian counts
are explicit inputs. Every remaining operation is addition, multiplication,
fixed natural power, or bit length. -/

namespace EditApproximation

def queryGatherEnvironment (M N P F exponent eM eF B S t W : ℕ) : Fin 16 → ℕ :=
  ![M, P, F, exponent, eM, eF, B, t, W, 2 ^ exponent,
    (40 * P + 2) ^ (2 * M), ((40 * P + 2) ^ 2 + 1) ^ (M + 1),
    BinaryFraction.preparedLocalGroupsBitBudget N M P F exponent eM eF B,
    BinaryFraction.preparedLocalOnlineBitBudget M P B S,
    BinaryFraction.physicalContinuationBitBudget M P ((B + 1) * (64 * F * P + 2) ^ 2)
      ((B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2) (B + 1) (B + 4),
    BinaryFraction.representativeCompleteBitBudget M ((40 * P + 2) ^ (2 * M)) (4 * (B + 1) + 20)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialWarmupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial certificate for the complete initial and warmup dispatch,
including actual gathers, buffer scans, and the previous-pass median. -/

namespace EditApproximation

def initialWarmupEnvironment (M P F Amax copies J symbolBits positionBits B C : ℕ) : Fin 13 → ℕ :=
  ![M, P, F, Amax, copies, J, symbolBits, positionBits, B, C,
    BinaryFraction.cachedInitialProgramBitBudget P Amax (B + 2),
    BinaryFraction.seedMedianBitBudget copies B, BinaryFraction.localWarmupBitBudget M P F B]

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

local notation "range" => physicalScalarRange M J N target.length exponent F Q R (localOnlineMassBound M P H)

noncomputable def physicalFamilyLaw : Measure (PhysicalFamilyScalarDraw
    (M := M) (J := J) (R := R) target N P F exponent H Q passes copies) :=
  Measure.pi fun key => (PMF.uniformOfFintype (Fin (range key.2.2))).toMeasure

instance physicalFamilyLaw_probability : IsProbabilityMeasure
    (physicalFamilyLaw (M := M) (J := J) (R := R) target N P F exponent H Q passes copies) := by
  unfold physicalFamilyLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end FamilyLaw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSeedTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite clamped seed tables and the exact table returned by a median pass. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





def physicalSeedGood {α : Type*} {M J N : ℕ} (source target : List α) (A : ℚ)
    (seed : ClampedPhysicalSeed M J target.length N) : Prop :=
  ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ clampedSeedNat seed state ∧
    (clampedSeedNat seed state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2

end EditApproximation

end OAI
end


