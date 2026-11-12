-- Prove2me | Definitions.Def_Q238L012
-- name    : Q238L012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:22:10.704202+00:00
-- url     : https://prove2.me/theorems/cec49fa3-815e-45b1-888c-bc26bfb7de0b
-- title:
--   Definitions bundle Q238L012 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 40 declarations of OpenAI's Lean: 13 definitions, 1 inductive type or structure and 26 theorems. The definitions and types are `OAI.MetricKMedianRecovery.Sampling.Comparison.instDecidableEqAction_2`, `OAI.MetricKMedianRecovery.SortedIndex.equiv`, `OAI.MetricKMedianRecovery.SortedIndex.representative`, `OAI.MetricKMedianRecovery.Surplus.clusterCost`, `OAI.MetricKMedianRecovery.Surplus.partCharge`, `OAI.MetricKMedianRecovery.Surplus.partCost`, `OAI.MetricKMedianRecovery.ValidExecution`, `OAI.MetricKMedianRecovery.ValidExecution.Contributor`, `OAI.MetricKMedianRecovery.ValidExecution.finalBudget`, `OAI.MetricKMedianRecovery.ValidExecution.precedes`, `OAI.MetricKMedianRecovery.ValidExecution.removal`, `OAI.MetricKMedianRecovery.clientSlack`, `OAI.MetricKMedianRecovery.initialState`, `OAI.MetricKMedianRecovery.totalSlack`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Algorithms_IntegralPrecision`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralPrecision.lean), [`KMedianRecovery_Branching_RationalBranch`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/RationalBranch.lean), [`KMedianRecovery_Encoding_SortedRepresentative`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/SortedRepresentative.lean), [`KMedianRecovery_Geometry_ClusterCost`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/ClusterCost.lean), [`KMedianRecovery_Geometry_MetricArrays`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/MetricArrays.lean), [`KMedianRecovery_Recovery_ExecutionState`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/ExecutionState.lean), [`KMedianRecovery_Recovery_Removal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Removal.lean), [`KMedianRecovery_Strictness_RegularDualWitness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/RegularDualWitness.lean).
--
--   **Imports.** It imports the bundles `Q238L000`, `Q238L001`, `Q238L002` and `Q238L003` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q238L021`; the statements `OAI.MetricKMedianRecovery.Surplus.protected_partition_cost_s238r` and `OAI.MetricKMedianRecovery.valid_execution_bounded_price_strictness_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.completion_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rowInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.realize_le_surrogate_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.cost_le_start_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.cost_le_surplus_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.lift_probability_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.cost_le_call_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.designated_recovery_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.cost_le_designated_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.polynomial_recovery_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.anchorInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.result_success_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238r`, `OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238r` and `OAI.MetricKMedianRecovery.Surplus.protected_partition_cost_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_Q238L000
import Definitions.Def_Q238L001
import Definitions.Def_Q238L002
import Definitions.Def_Q238L003

section
-- module Solutions.Q238_KM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ExecutionState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

noncomputable def initialState (D X : Type*) : ExecutionState D X :=
  ⟨∅, 1, fun _ => 1⟩

structure ValidExecution (D X : Type*) [Fintype D] [PseudoMetricSpace X]
    [DecidableEq X] (steps : ℕ) (v lam eta : ℝ) where
  location : D → X
  regular : Finset X
  far_initially : ∀ j i, i ∈ regular → 1 ≤ dist i (location j)
  state : ℕ → ExecutionState D X
  initial : state 0 = initialState D X
  transition : ∀ n, n < steps → AtomicStep location regular v lam eta (state n) (state (n + 1))
  terminated : ∀ j, ¬activeAt location (1 - 3 * v) (state steps).phase (state steps).opened j

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable local instance instDecidableEqAction_2 (D : Finset V) (M E J : ℕ) : DecidableEq (Action D M E J) := Classical.decEq _

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {α : Type*} [LinearOrder α]
lemma enum_mem (S : Finset α) (i : Fin S.card) : enum S i∈S := S.orderEmbOfFin_mem rfl i
lemma enum_injective (S : Finset α) : Function.Injective (enum S) := (S.orderEmbOfFin rfl).injective
lemma enum_list (S : Finset α) : List.ofFn (enum S)=S.sort (·≤·) := by
  rw [List.ofFn_eq_map]
  exact S.listMap_orderEmbOfFin_finRange rfl
end MetricKMedianRecovery.SortedIndex

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {α : Type*} [LinearOrder α]
noncomputable def equiv (S : Finset α) : Fin S.card≃S :=
  Equiv.ofBijective (fun i=>⟨enum S i,enum_mem S i⟩) (by
    constructor
    · intro i j h
      exact enum_injective S (congrArg Subtype.val h)
    · rintro ⟨x,hx⟩
      have hh : x∈List.ofFn (enum S) := by rw [enum_list];simpa only [Finset.mem_sort] using hx
      obtain ⟨i,hi⟩:=List.mem_ofFn.mp hh
      exact ⟨i,Subtype.ext hi⟩)
end MetricKMedianRecovery.SortedIndex

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_SortedRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {V : Type*} [LinearOrder V]
noncomputable def representative (S T : Finset V) : Finset (Fin S.card) :=
  Finset.univ.filter (fun i=>enum S i∈T)
end MetricKMedianRecovery.SortedIndex

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_ClusterCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

noncomputable def clusterCost (D : Finset V) (assign : V → V) (i : V) : ℝ :=
  ∑ p ∈ cluster D assign i, dist p i
noncomputable def partCost (D I : Finset V) (assign : V → V) : ℝ :=
  ∑ i ∈ I, clusterCost D assign i
noncomputable def partCharge (D I : Finset V) (assign proxy : V → V) : ℝ :=
  ∑ i ∈ I, ∑ p ∈ cluster D assign i, dist p (proxy i)

end MetricKMedianRecovery.Surplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Removal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

lemma phase_pos (n : ℕ) (hn : n ≤ steps) : 0 < (E.state n).phase := by
  induction n with
  | zero => simp only [E.initial, initialState] <;> norm_num
  | succ n ih =>
    exact (E.transition n (by omega)).positive_phase (ih (by omega))

lemma opened_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) :
    (E.state a).opened ⊆ (E.state b).opened := by
  induction b, hab using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ b hab ih =>
    exact (ih (by omega)).trans ((E.transition b (by omega)).opened_subset)

lemma phase_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) :
    (E.state a).phase ≤ (E.state b).phase := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    exact (ih (by omega)).trans ((E.transition b (by omega)).phase_le (E.phase_pos b (by omega)).le)

lemma active_antitone {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) (j : D)
    (hj : activeAt E.location (1 - 3 * v) (E.state b).phase (E.state b).opened j) :
    activeAt E.location (1 - 3 * v) (E.state a).phase (E.state a).opened j := by
  intro f hf
  exact lt_of_le_of_lt (E.phase_mono hab hb) (hj f (E.opened_mono hab hb hf))

lemma inactive_persists {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) (j : D)
    (hj : ¬activeAt E.location (1 - 3 * v) (E.state a).phase (E.state a).opened j) :
    ¬activeAt E.location (1 - 3 * v) (E.state b).phase (E.state b).opened j :=
  fun h => hj (E.active_antitone hab hb j h)

lemma budget_frozen {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) (j : D)
    (hj : ¬activeAt E.location (1 - 3 * v) (E.state a).phase (E.state a).opened j) :
    (E.state b).budget j = (E.state a).budget j := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    exact ((E.transition b (by omega)).inactive_frozen j
      (E.inactive_persists hab (by omega) j hj)).trans (ih (by omega))

lemma initial_active (j : D) :
    activeAt E.location (1 - 3 * v) (E.state 0).phase (E.state 0).opened j := by
  rw [E.initial]
  intro f hf
  simp [initialState] at hf

lemma exists_removal (j : D) : ∃ n : ℕ, n < steps ∧
    activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j ∧
    ¬activeAt E.location (1 - 3 * v) (E.state (n + 1)).phase (E.state (n + 1)).opened j := by
  classical
  have hex : ∃ n : ℕ, n ≤ steps ∧
      ¬activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j :=
    ⟨steps, le_rfl, E.terminated j⟩
  let b := Nat.find hex
  have hb : b ≤ steps ∧
      ¬activeAt E.location (1 - 3 * v) (E.state b).phase (E.state b).opened j := Nat.find_spec hex
  have hbpos : 0 < b := by
    by_contra h
    have heq : b = 0 := by omega
    exact hb.2 (heq ▸ E.initial_active j)
  refine ⟨b - 1, by omega, ?_, ?_⟩
  · by_contra hnot
    exact Nat.find_min hex (show b - 1 < b by omega) ⟨by omega, hnot⟩
  · simpa only [Nat.sub_add_cancel (show 1 ≤ b by omega)] using hb.2

noncomputable def removal (j : D) : Fin steps :=
  ⟨Classical.choose (E.exists_removal j), (Classical.choose_spec (E.exists_removal j)).1⟩

lemma removal_active (j : D) :
    activeAt E.location (1 - 3 * v) (E.state (E.removal j)).phase
      (E.state (E.removal j)).opened j :=
  (Classical.choose_spec (E.exists_removal j)).2.1

lemma removal_inactive (j : D) :
    ¬activeAt E.location (1 - 3 * v) (E.state ((E.removal j).val + 1)).phase
      (E.state ((E.removal j).val + 1)).opened j :=
  (Classical.choose_spec (E.exists_removal j)).2.2

lemma active_iff_before_removal (n : ℕ) (hn : n ≤ steps) (j : D) :
    activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j ↔
      n ≤ (E.removal j).val := by
  constructor
  · intro ha
    by_contra h
    exact E.removal_inactive j
      (E.active_antitone (show (E.removal j).val + 1 ≤ n by omega) hn j ha)
  · intro h
    exact E.active_antitone h (Nat.le_of_lt (E.removal j).isLt) j (E.removal_active j)

lemma final_cap (j : D) :
    (E.state steps).budget j ≤ (1 + v ^ 2) * (E.state (E.removal j)).phase := by
  rw [E.budget_frozen (Nat.succ_le_of_lt (E.removal j).isLt) le_rfl j (E.removal_inactive j)]
  exact (E.transition _ (E.removal j).isLt).active_budget_cap
    (E.phase_pos _ (E.removal j).isLt.le).le j (E.removal_active j)

end ValidExecution

noncomputable def clientSlack {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t : ℝ) (s : ExecutionState D X) (j : D) : ℝ :=
  s.budget j - clippedAt loc t s.phase s.opened j

noncomputable def totalSlack {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t : ℝ) (s : ExecutionState D X) : ℝ :=
  ∑ j, clientSlack loc t s j

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_RegularDualWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

noncomputable def finalBudget (j : D) : ℝ := (E.state steps).budget j

def Contributor (i : X) (j : D) : Prop := 2 * dist i (E.location j) < E.finalBudget j

def precedes (j k : D) : Prop :=
  (E.removal j).val < (E.removal k).val ∨
    ((E.removal j).val = (E.removal k).val ∧ E.finalBudget j < E.finalBudget k)

end ValidExecution

end MetricKMedianRecovery

end OAI
end


