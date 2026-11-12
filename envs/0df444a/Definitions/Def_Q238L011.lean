-- Prove2me | Definitions.Def_Q238L011
-- name    : Q238L011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:22:12.768206+00:00
-- url     : https://prove2.me/theorems/5ae1fe71-1501-4d77-a99d-6e4912a61e06
-- title:
--   Definitions bundle Q238L011 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 93 declarations of OpenAI's Lean: 64 definitions, 2 inductive types or structures and 27 theorems. The definitions and types are `OAI.MetricKMedianRecovery.RadiusMenus.menuConstant`, `OAI.MetricKMedianRecovery.RationalMetricInput.outputBits`, `OAI.MetricKMedianRecovery.RationalOpenability.dualForm`, `OAI.MetricKMedianRecovery.RationalOpenability.paymentForm`, `OAI.MetricKMedianRecovery.RationalOpenability.system`, `OAI.MetricKMedianRecovery.RationalPhase.State.real`, `OAI.MetricKMedianRecovery.RationalSampling.State.Height`, `OAI.MetricKMedianRecovery.RationalSampling.State.assignment`, `OAI.MetricKMedianRecovery.RationalSampling.State.center`, `OAI.MetricKMedianRecovery.RationalSampling.State.radius`, `OAI.MetricKMedianRecovery.RationalSampling.fromArrays`, `OAI.MetricKMedianRecovery.RegularDualWitness`, `OAI.MetricKMedianRecovery.RemovalReplay`, `OAI.MetricKMedianRecovery.RemovalReplay.boundaryBid`, `OAI.MetricKMedianRecovery.Rounding.metric`, `OAI.MetricKMedianRecovery.Sampling.Comparison.Correct`, `OAI.MetricKMedianRecovery.Sampling.Comparison.IntegralBits`, `OAI.MetricKMedianRecovery.Sampling.Comparison.IsBall`, `OAI.MetricKMedianRecovery.Sampling.Comparison.IsThird`, `OAI.MetricKMedianRecovery.Sampling.Comparison.MainAction`, `OAI.MetricKMedianRecovery.Sampling.Comparison.MainEntry`, `OAI.MetricKMedianRecovery.Sampling.Comparison.Terminal`, `OAI.MetricKMedianRecovery.Sampling.Comparison.actionMenuWeight`, `OAI.MetricKMedianRecovery.Sampling.Comparison.bad`, `OAI.MetricKMedianRecovery.Sampling.Comparison.ballLeader`, `OAI.MetricKMedianRecovery.Sampling.Comparison.ballSteps`, `OAI.MetricKMedianRecovery.Sampling.Comparison.blindUpdate`, `OAI.MetricKMedianRecovery.Sampling.Comparison.blueDestination`, `OAI.MetricKMedianRecovery.Sampling.Comparison.conditionalClients`, `OAI.MetricKMedianRecovery.Sampling.Comparison.counter`, `OAI.MetricKMedianRecovery.Sampling.Comparison.covered`, `OAI.MetricKMedianRecovery.Sampling.Comparison.coveredCenter`, `OAI.MetricKMedianRecovery.Sampling.Comparison.coveredIndex`, `OAI.MetricKMedianRecovery.Sampling.Comparison.designatedDestination`, `OAI.MetricKMedianRecovery.Sampling.Comparison.destinations`, `OAI.MetricKMedianRecovery.Sampling.Comparison.entryIndex`, `OAI.MetricKMedianRecovery.Sampling.Comparison.leaderPair`, `OAI.MetricKMedianRecovery.Sampling.Comparison.mainActual`, `OAI.MetricKMedianRecovery.Sampling.Comparison.near`, `OAI.MetricKMedianRecovery.Sampling.Comparison.nearEligible` and 26 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_IntegralPrecision`, `KMedianRecovery_Encoding_EntryIndex`, `KMedianRecovery_Geometry_LeafDistances`, `KMedianRecovery_Geometry_Metric`, `KMedianRecovery_Geometry_Nearest`, `KMedianRecovery_Machines_FirstSize`, `KMedianRecovery_Recovery_BlindUpdate`, `KMedianRecovery_Recovery_Cluster`, `KMedianRecovery_Recovery_CommonL`, `KMedianRecovery_Recovery_CoveredCenter`, `KMedianRecovery_Recovery_DestinationFacility`, `KMedianRecovery_Recovery_Destinations`, `KMedianRecovery_Recovery_Guide`, `KMedianRecovery_Recovery_NearEligible`, `KMedianRecovery_Recovery_ReferenceBridge`, `KMedianRecovery_Recovery_RemovalReplay`, `KMedianRecovery_Recovery_SingleRadiusRatio`, `KMedianRecovery_Recovery_State2`, `KMedianRecovery_Recovery_StoredForms`, `KMedianRecovery_Recovery_VirtualCast`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Strictness_RegularDualWitness`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L000`, `Q238L002`, `Q238L003`, `Q238L004` and `Q238L005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L020` and `Q238L021`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.successful_probability_s238r`, `OAI.MetricKMedianRecovery.IntegralCandidates.separated_comparison_s238r`, `OAI.MetricKMedianRecovery.RationalSampling.trace_probability_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.covered_completion_sum_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.covered_cost_aggregate_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision_spec_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.successful_completion_charge_s238r` and `OAI.MetricKMedianRecovery.Sampling.Comparison.surrogate_success_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion_s238r`, `OAI.MetricKMedianRecovery.IntegralCandidates.separated_comparison_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.covered_completion_sum_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.covered_cost_aggregate_s238r` and `OAI.MetricKMedianRecovery.Sampling.Comparison.successful_completion_charge_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L000
import Definitions.Def_Q238L002
import Definitions.Def_Q238L003
import Definitions.Def_Q238L004
import Definitions.Def_Q238L005

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FirstSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RadiusMenus

lemma upward_radius_bounds (kappa q r : ℝ) (hk : 0 < kappa) (hq : 0 < q)
    (hr : 0 ≤ r) :
    r ≤ additiveRadius kappa q (upwardIndex kappa q r) ∧
      additiveRadius kappa q (upwardIndex kappa q r) ≤ r+kappa*q := by
  have hkq : 0 < kappa*q := mul_pos hk hq
  have hcast : (upwardIndex kappa q r : ℝ) = max 1 (Nat.ceil (r/(kappa*q)) : ℝ) := by
    simp only [upwardIndex, Nat.cast_max, Nat.cast_one]
  have hlow : r/(kappa*q) ≤ (upwardIndex kappa q r : ℝ) := by
    rw [hcast]
    exact (Nat.le_ceil _).trans (le_max_right _ _)
  have hu := Nat.ceil_lt_add_one_of_gt_neg_one (show (-1 : ℝ) < r/(kappa*q) by
    have := div_nonneg hr hkq.le
    linarith)
  have hu' : (upwardIndex kappa q r : ℝ) ≤ r/(kappa*q)+1 := by
    rw [hcast]
    exact max_le (by have := div_nonneg hr hkq.le; linarith) hu.le
  constructor
  · have hh := (div_le_iff₀ hkq).mp hlow
    simpa only [additiveRadius, mul_assoc] using hh
  · have hh := mul_le_mul_of_nonneg_right hu' hkq.le
    have he : (r/(kappa*q)+1)*(kappa*q) = r+kappa*q := by field_simp
    rw [he] at hh
    simpa only [additiveRadius, mul_assoc] using hh

lemma first_menu_available (kappa q r : ℝ) (hk : 0 < kappa) (hq : 0 < q)
    (hr : 0 ≤ r) (hsmall : r ≤ 10*q) :
    1 ≤ upwardIndex kappa q r ∧ upwardIndex kappa q r ≤ firstSize kappa ∧
      r ≤ additiveRadius kappa q (upwardIndex kappa q r) ∧
      additiveRadius kappa q (upwardIndex kappa q r) ≤ (1+kappa)*r+kappa*q := by
  have hrq : r/(kappa*q) ≤ 10/kappa := by
    apply (div_le_div_iff₀ (mul_pos hk hq) hk).mpr
    nlinarith
  have hceil := Nat.ceil_mono hrq
  have hbound : upwardIndex kappa q r ≤ firstSize kappa := by
    unfold upwardIndex firstSize
    omega
  have hb := upward_radius_bounds kappa q r hk hq hr
  exact ⟨le_max_left _ _, hbound, hb.1, hb.2.trans (by nlinarith [mul_nonneg hk.le hr])⟩

lemma third_menu_available (kappa q r : ℝ) (m : ℕ) (hk : 0 < kappa)
    (hq : 0 < q) (hr : 0 < r) (hbudget : r/q ≤ (10/9 : ℝ)*m) :
    1 ≤ Nat.ceil (r/(kappa*q)) ∧ Nat.ceil (r/(kappa*q)) ≤ thirdSize kappa m ∧
      r ≤ additiveRadius kappa q (Nat.ceil (r/(kappa*q))) ∧
      additiveRadius kappa q (Nat.ceil (r/(kappa*q))) ≤ (1+kappa)*r+kappa*q := by
  have hj : 0 < Nat.ceil (r/(kappa*q)) := Nat.ceil_pos.mpr (div_pos hr (mul_pos hk hq))
  have he : r/(kappa*q) = (r/q)/kappa := by ring
  have hratio : r/(kappa*q) ≤ 2*m/kappa := by
    rw [he]
    apply div_le_div_of_nonneg_right _ hk.le
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hm := Nat.ceil_mono hratio
  have hidx : upwardIndex kappa q r = Nat.ceil (r/(kappa*q)) := max_eq_right hj
  have hu := upward_radius_bounds kappa q r hk hq hr.le
  rw [hidx] at hu
  refine ⟨hj, ?_, hu.1, hu.2.trans ?_⟩
  · dsimp [thirdSize]
    omega
  · nlinarith [mul_nonneg hk.le hr.le]

noncomputable def menuConstant (kappa : ℝ) (hk : 0 < kappa) : ℝ :=
  min (1/(3*(firstSize kappa : ℝ)))
    (min (1/(3*((geometricCap kappa hk : ℝ)+1))) (1/3))

end MetricKMedianRecovery.RadiusMenus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling

namespace State
variable {V : Type*}
def initial : State V := ⟨∅, []⟩
noncomputable def remove (s : State V) (v : V) : State V := by
  classical
  exact ⟨insert v s.deleted, s.leaves⟩
def add (s : State V) (w : V) (R : ℝ) : State V :=
  ⟨s.deleted, s.leaves ++ [(w,R)]⟩
end State

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable def tagDistance (Δ : ℝ) (s : State V) (x : V) (t : Tag V) : ℝ :=
  match ofLex t with
  | .inl v => dist x v
  | .inr 0 => Δ
  | .inr (j+1) => match s.leaves[j]? with
    | some z => dist x z.1 + z.2
    | none => Δ

noncomputable def chosen (S : Finset V) (Δ : ℝ) (s : State V) (x : V) : Tag V :=
  Classical.choose (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))

noncomputable def reference (S : Finset V) (Δ : ℝ) (s : State V) (x : V) : ℝ :=
  tagDistance Δ s x (chosen S Δ s x)

lemma reference_nonneg (S : Finset V) (Δ : ℝ) (s : State V) (x : V)
    (hΔ : 0 ≤ Δ) (hr : ∀ z ∈ s.leaves, 0 ≤ z.2) : 0 ≤ reference S Δ s x := by
  unfold reference
  generalize chosen S Δ s x = t
  cases ht : ofLex t with
  | inl v => simpa only [tagDistance, ht] using (dist_nonneg (x := x) (y := v))
  | inr j =>
    cases j with
    | zero => simpa only [tagDistance, ht] using hΔ
    | succ j =>
      cases hz : s.leaves[j]? with
      | none => simpa only [tagDistance, ht, hz] using hΔ
      | some z =>
        simp only [tagDistance, ht, hz]
        exact add_nonneg dist_nonneg (hr z (List.mem_of_getElem? hz))

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LeafDistances
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
open RadiusMenus
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable def leafDistances (s : State V) (w : V) : Finset ℝ :=
  s.leaves.toFinset.image (fun z => dist w z.1+z.2)

noncomputable def nearestLeaf (s : State V) (w : V) : Option ℝ :=
  if h : (leafDistances s w).Nonempty then some ((leafDistances s w).inf' h id) else none

lemma nearestLeaf_of_mem (s : State V) (w : V) (z : V × ℝ) (hz : z ∈ s.leaves) :
    ∃ r, nearestLeaf s w = some r ∧ r ≤ dist w z.1+z.2 := by
  classical
  have hm : dist w z.1+z.2 ∈ leafDistances s w :=
    Finset.mem_image.mpr ⟨z,List.mem_toFinset.mpr hz,rfl⟩
  have hn : (leafDistances s w).Nonempty := ⟨_,hm⟩
  refine ⟨_,?_,Finset.inf'_le id hm⟩
  simp only [nearestLeaf, dite_eq_left hn]

lemma nearestLeaf_lower (s : State V) (w : V) (r a : ℝ)
    (hr : nearestLeaf s w = some r) (ha : ∀ z ∈ s.leaves, a ≤ dist w z.1+z.2) : a ≤ r := by
  classical
  unfold nearestLeaf at hr
  split_ifs at hr with hn
  · cases Option.some.inj hr
    apply Finset.le_inf'
    intro d hd
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hd
    exact ha z (List.mem_toFinset.mp hz)

noncomputable def clientWeight (S : Finset V) (Δ : ℝ) (s : State V) (w : V) : ℝ :=
  max 0 (reference S Δ s w)

noncomputable def totalWeight (D S : Finset V) (Δ : ℝ) (s : State V) : ℝ :=
  ∑ w ∈ D, clientWeight S Δ s w

lemma clientWeight_nonneg (S : Finset V) (Δ : ℝ) (s : State V) (w : V) :
    0 ≤ clientWeight S Δ s w := le_max_left _ _

lemma clientWeight_eq (S : Finset V) (Δ : ℝ) (s : State V) (w : V)
    (hΔ : 0 ≤ Δ) (hr : ∀ z ∈ s.leaves, 0 ≤ z.2) :
    clientWeight S Δ s w = reference S Δ s w :=
  max_eq_right (reference_nonneg S Δ s w hΔ hr)

lemma menuWeight_nonneg (M E J : ℕ) (a : Entry M E J) : 0 ≤ menuWeight M E J a := by
  rcases a with i | (i | i)
  · simp only [menuWeight] <;> positivity
  · simp only [menuWeight] <;> positivity
  · simp only [menuWeight]
    apply mul_nonneg (by norm_num)
    apply div_nonneg (by positivity)
    exact Finset.sum_nonneg (fun _ _ => by positivity)

noncomputable def transitionWeight (D S : Finset V) (Δ : ℝ) (M E J : ℕ)
    (s : Option (State V)) (a : Action D M E J) : ℝ :=
  match s with
  | none => if a = Sum.inl () then 1 else 0
  | some s => if 0 < totalWeight D S Δ s then
      match a with
      | .inl _ => 0
      | .inr (.inl w) => clientWeight S Δ s w/(2*totalWeight D S Δ s)
      | .inr (.inr (w,e)) => clientWeight S Δ s w/(2*totalWeight D S Δ s)*menuWeight M E J e
    else if a = Sum.inl () then 1 else 0

lemma transitionWeight_nonneg (D S : Finset V) (Δ : ℝ) (M E J : ℕ)
    (s : Option (State V)) (a : Action D M E J) : 0 ≤ transitionWeight D S Δ M E J s a := by
  classical
  cases s with
  | none => simp only [transitionWeight]; split_ifs <;> norm_num
  | some s =>
    simp only [transitionWeight]
    split_ifs with h
    · rcases a with u | (w | ⟨w,e⟩)
      · exact le_rfl
      · exact div_nonneg (clientWeight_nonneg S Δ s w) (by positivity)
      · exact mul_nonneg (div_nonneg (clientWeight_nonneg S Δ s w) (by positivity))
          (menuWeight_nonneg M E J e)
    · norm_num
    · norm_num

lemma transitionWeight_total (D S : Finset V) (Δ : ℝ) (M E J : ℕ)
    (hM : 0 < M) (hJ : 0 < J) (s : Option (State V)) :
    ∑ a : Action D M E J, transitionWeight D S Δ M E J s a = 1 := by
  classical
  cases s with
  | none => simp [transitionWeight]
  | some s =>
    by_cases h : 0 < totalWeight D S Δ s
    · simp only [transitionWeight, ite_eq_left h, Fintype.sum_sum_type, Fintype.sum_prod_type,
        Finset.sum_const_zero, zero_add, ← Finset.mul_sum, menuWeight_total M E J hM hJ, mul_one]
      rw [← Finset.sum_div, Finset.sum_coe_sort]
      change totalWeight D S Δ s/(2*totalWeight D S Δ s) +
        totalWeight D S Δ s/(2*totalWeight D S Δ s) = 1
      field_simp
      ring
    · simp [transitionWeight, h]

noncomputable def actualKernel (D S : Finset V) (Δ : ℝ) (M E J : ℕ)
    (hM : 0 < M) (hJ : 0 < J) : Guided.Kernel (Option (State V)) (Action D M E J) :=
  ⟨transitionWeight D S Δ M E J, transitionWeight_nonneg D S Δ M E J,
    transitionWeight_total D S Δ M E J hM hJ⟩

noncomputable def menuRadius (D : Finset V) (hD : D.Nonempty) (P kappa : ℝ)
    (m M E J : ℕ) (s : State V) (w : V) : Entry M E J → Option ℝ
  | .inl j => some ((j.val+1)*kappa*Population.radius D hD P m w)
  | .inr (.inl e) => (nearestLeaf s w).map (fun r => r/(1+kappa)^e.val)
  | .inr (.inr j) => some ((j.val+1)*kappa*Population.radius D hD P m w)

noncomputable def retain (m : ℕ) (s : State V) : Option (State V) :=
  if s.leaves.length ≤ m ∧ s.deleted.card ≤ m then some s else none

noncomputable def update (D F S : Finset V) (hD : D.Nonempty) (Δ P kappa : ℝ)
    (m M E J : ℕ) (s : Option (State V)) (a : Action D M E J) : Option (State V) :=
  match s with
  | none => none
  | some s => if 0 < totalWeight D S Δ s then
      match a with
      | .inl _ => none
      | .inr (.inl w) =>
        match ofLex (chosen S Δ s w) with
        | .inl v => retain m (s.remove v)
        | .inr _ => none
      | .inr (.inr (w,e)) =>
        match menuRadius D hD P kappa m M E J s w e with
        | none => none
        | some R => if (F.filter (fun v => dist w.val v ≤ R)).Nonempty then
            retain m (s.add w R) else none
    else none

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cluster
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable def clusterMean (D : Finset V) (c : V → V) (o : V) : ℝ :=
  clusterCost D c o / (cluster D c o).card

namespace Comparison
variable {D S O : Finset V}
noncomputable def bad (C : Comparison D S O) : Finset V := O \ C.good
noncomputable def nonproxy (C : Comparison D S O) : Finset V := S \ C.good.image C.proxy
noncomputable def covered (C : Comparison D S O) (s : State V) : Finset V :=
  (s.leaves.map (fun z => C.assign z.1)).toFinset
noncomputable def near (C : Comparison D S O) (o : V) : Finset V :=
  (cluster D C.assign o).filter (fun p => dist p o ≤ (6/5 : ℝ)*clusterMean D C.assign o)
noncomputable def nearTotal (C : Comparison D S O) (Δ : ℝ) (s : State V) : ℝ :=
  ∑ o ∈ C.bad \ C.covered s, ∑ p ∈ C.near o, reference S Δ s p
noncomputable def removalTotal (C : Comparison D S O) (Δ : ℝ) (s : State V) : ℝ :=
  ∑ p ∈ D.filter (fun p => ∃ o ∈ C.nonproxy \ s.deleted, chosen S Δ s p = realTag o),
    reference S Δ s p

def Correct (C : Comparison D S O) (hD : D.Nonempty) (kappa : ℝ) (s : State V) : Prop :=
  s.deleted ⊆ C.nonproxy ∧
  (s.leaves.map (fun z => C.assign z.1)).Nodup ∧
  ∀ z ∈ s.leaves,
    z.1 ∈ D ∧ C.assign z.1 ∈ C.bad ∧
    dist z.1 (C.assign z.1) ≤ (6/5 : ℝ)*clusterMean D C.assign (C.assign z.1) ∧
    0 < z.2 ∧ dist z.1 (C.assign z.1) ≤ z.2 ∧
    z.2 ≤ (1+kappa)*dist z.1 (C.assign z.1) +
      kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card z.1

lemma correct_radii_nonneg (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) : ∀ z ∈ s.leaves, 0 ≤ z.2 := by
  intro z hz
  exact (hs.2.2 z hz).2.2.2.1.le

lemma covered_witness (C : Comparison D S O) (s : State V) (o : V)
    (ho : o ∈ C.covered s) : ∃ z ∈ s.leaves, C.assign z.1 = o := by
  exact List.mem_map.mp (List.mem_toFinset.mp ho)

lemma comparison_triangle (C : Comparison D S O) (w p : V) (hw : w ∈ D) (hp : p ∈ D) :
    dist w (C.assign w) ≤ dist w p + dist p (C.assign p) :=
  (C.nearest w hw (C.assign p) (C.assigned p hp)).trans (dist_triangle w p (C.assign p))

lemma correct_leaf_dominates (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (w : V) (hw : w ∈ D) (z : V × ℝ) (hz : z ∈ s.leaves) :
    dist w (C.assign w) ≤ dist w z.1+z.2 := by
  have hh := C.comparison_triangle w z.1 hw (hs.2.2 z hz).1
  have hr := (hs.2.2 z hz).2.2.2.2.1
  linarith

lemma correct_nearestLeaf_lower (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (w : V) (hw : w ∈ D) (r : ℝ) (hr : nearestLeaf s w = some r) :
    dist w (C.assign w) ≤ r :=
  nearestLeaf_lower s w r _ hr (fun z hz => C.correct_leaf_dominates hD kappa s hs w hw z hz)

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SingleRadiusRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

noncomputable def leaderPair (C : Comparison D S O) (s : State V) (o : V) : V × ℝ :=
  if h : o ∈ C.covered s then Classical.choose (C.covered_witness s o h) else (o,0)

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoveredCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}
noncomputable def coveredCenter (C : Comparison D S O) (s : State V)
    (i : Fin s.leaves.length) : V := C.assign s.leaves[i.val].1
lemma exists_coveredCenter (C : Comparison D S O) (s : State V) (o : V)
    (ho : o ∈ C.covered s) : ∃ i, C.coveredCenter s i = o := by
  obtain ⟨z,hz,hzo⟩ := List.mem_map.mp (List.mem_toFinset.mp ho)
  obtain ⟨j,hj,hjz⟩ := List.mem_iff_getElem.mp hz
  refine ⟨⟨j,hj⟩,?_⟩
  simp only [coveredCenter,hjz,hzo]

noncomputable def coveredIndex (C : Comparison D S O) (s : State V) (o : V)
    (ho : o ∈ C.covered s) : Fin s.leaves.length :=
  Classical.choose (C.exists_coveredCenter s o ho)
end MetricKMedianRecovery.Sampling.Comparison
namespace MetricKMedianRecovery.Sampling
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

def leafCenter (s : State V) (i : Fin s.leaves.length) : V := s.leaves[i.val].1
def leafRadius (s : State V) (i : Fin s.leaves.length) : ℝ := s.leaves[i.val].2

def toVirtual (s : State V) (t : Tag V) : Virtual V s.leaves.length :=
  match ofLex t with
  | .inl v => .real v
  | .inr 0 => .permanent
  | .inr (j+1) => if h : j < s.leaves.length then .ball ⟨j,h⟩ else .permanent

noncomputable def completionAssignment (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :=
  toVirtual s (chosen S Δ s x)

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Destinations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

noncomputable def destinations (C : Comparison D S O) (s : State V) :
    Finset (Destination V s.leaves.length) :=
  C.good.image (fun o => Destination.proxy (C.proxy o)) ∪
    Finset.univ.image Destination.covered ∪
    (C.bad \ C.covered s).image Destination.uncovered

noncomputable def ownDestination (C : Comparison D S O) (s : State V) (p : V) :
    Destination V s.leaves.length :=
  if C.assign p ∈ C.good then .proxy (C.proxy (C.assign p))
  else if h : C.assign p ∈ C.covered s then .covered (C.coveredIndex s (C.assign p) h)
  else .uncovered (C.assign p)

lemma ownDestination_mem (C : Comparison D S O) (s : State V) (p : V) (hp : p ∈ D) :
    C.ownDestination s p ∈ C.destinations s := by
  classical
  unfold ownDestination destinations
  split_ifs with hg hc
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hg, rfl⟩))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨_, Finset.mem_univ _, rfl⟩))
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨_, Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨C.assigned p hp, hg⟩, hc⟩, rfl⟩)

lemma destinations_nonempty (C : Comparison D S O) (hD : D.Nonempty) (s : State V) :
    (C.destinations s).Nonempty := by
  obtain ⟨p, hp⟩ := hD
  exact ⟨_, C.ownDestination_mem s p hp⟩

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DestinationFacility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

@[simp] lemma destinations_proxy (C : Comparison D S O) (s : State V) (v : V) :
    Destination.proxy v ∈ C.destinations s ↔ v ∈ C.good.image C.proxy := by
  simp [destinations]

@[simp] lemma destinations_uncovered (C : Comparison D S O) (s : State V) (v : V) :
    Destination.uncovered v ∈ C.destinations s ↔ v ∈ C.bad \ C.covered s := by
  simp [destinations]

noncomputable def designatedDestination (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (v : V) : Destination V s.leaves.length :=
  selectedDestination theta (C.coveredCenter s) (leafCenter s) (leafRadius s)
    (C.destinations s) (C.destinations_nonempty hD s) v

noncomputable def blueDestination (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (u : V) : V :=
  destinationFacility (C.coveredCenter s) (C.designatedDestination hD s theta u)

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NearEligible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus

noncomputable def nearEligible (C : Comparison D S O) (s : State V) : Finset V :=
  D.filter (fun p => C.assign p ∈ C.bad \ C.covered s ∧
    dist p (C.assign p) ≤ (6/5 : ℝ)*clusterMean D C.assign (C.assign p))

noncomputable def removalEligible (C : Comparison D S O) (Δ : ℝ) (s : State V) : Finset V :=
  D.filter (fun p => ∃ o ∈ C.nonproxy \ s.deleted, chosen S Δ s p = realTag o)

lemma nearTotal_eq (C : Comparison D S O) (Δ : ℝ) (s : State V) :
    C.nearTotal Δ s = ∑ p ∈ C.nearEligible s, reference S Δ s p := by
  classical
  simp only [nearTotal, near, cluster, Finset.filter_filter, nearEligible, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have he : ∀ o, (if C.assign p = o ∧ dist p o ≤ (6/5 : ℝ)*clusterMean D C.assign o
      then reference S Δ s p else 0) =
      (if o = C.assign p then
        (if dist p (C.assign p) ≤ (6/5 : ℝ)*clusterMean D C.assign (C.assign p)
        then reference S Δ s p else 0) else 0) := by
    intro o
    by_cases h : o = C.assign p
    · subst o
      simp
    · simp [h, Ne.symm h]
  simp_rw [he]
  simp only [Finset.sum_ite_eq']
  split_ifs <;> simp_all

def Terminal (C : Comparison D S O) (kappa Δ : ℝ) (s : State V) : Prop :=
  C.nearTotal Δ s ≤ kappa*comparisonCost D C.assign ∧
    C.removalTotal Δ s ≤ kappa*comparisonCost D C.assign

noncomputable def counter (C : Comparison D S O) (s : State V) : ℕ :=
  2*C.bad.card-(s.leaves.length+s.deleted.card)

open scoped Classical

noncomputable def conditionalClients (D S : Finset V) (Δ : ℝ) (s : State V)
    (E : Finset V) (hE : E ⊆ D) (T : ℝ) (hT : 0 < T)
    (he : ∑ p ∈ E, clientWeight S Δ s p = T) : Guided.Kernel Unit D := by
  classical
  refine ⟨fun _ w => if w.val ∈ E then clientWeight S Δ s w/T else 0, ?_, ?_⟩
  · intro u w
    split_ifs
    · exact div_nonneg (clientWeight_nonneg S Δ s w) hT.le
    · exact le_rfl
  · intro u
    have hh : (∑ w : D, if w.val ∈ E then clientWeight S Δ s w/T else 0) =
        (∑ w : D, if w.val ∈ E then clientWeight S Δ s w else 0)/T := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> simp
    rw [hh,Finset.sum_coe_sort D (fun p => if p ∈ E then clientWeight S Δ s p else 0),
      ← Finset.sum_filter,Finset.filter_mem_eq_of_subset hE,he]
    exact div_self (ne_of_gt hT)

abbrev MainEntry (m : ℕ) := Entry (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos)
  (thirdSize mainKappa m)
abbrev MainAction (D : Finset V) (m : ℕ) :=
  Action D (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa m)

lemma eligible_near_weight (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (s : State V) (hs : C.Correct hD mainKappa s) :
    (∑ p ∈ C.nearEligible s, clientWeight S Δ s p) = C.nearTotal Δ s := by
  rw [C.nearTotal_eq]
  exact Finset.sum_congr rfl (fun p _ => clientWeight_eq S Δ s p hΔ
    (C.correct_radii_nonneg hD mainKappa s hs))

lemma eligible_removal_weight (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (s : State V) (hs : C.Correct hD mainKappa s) :
    (∑ p ∈ C.removalEligible Δ s, clientWeight S Δ s p) = C.removalTotal Δ s :=
  Finset.sum_congr rfl (fun p _ => clientWeight_eq S Δ s p hΔ
    (C.correct_radii_nonneg hD mainKappa s hs))

noncomputable abbrev mainActual (D S : Finset V) (Δ : ℝ) (m : ℕ) :=
  actualKernel D S Δ (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos)
    (thirdSize mainKappa m) (by unfold firstSize; omega) (by unfold thirdSize; omega)

noncomputable def stop (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ) : Option (State V) → Prop
  | none => False
  | some s => C.Correct hD mainKappa s ∧ C.Terminal mainKappa Δ s

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Guide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus
open scoped Classical

noncomputable def actionMenuWeight (m : ℕ) : MainAction D m → ℝ
  | .inr (.inr (_,e)) => menuWeight (firstSize mainKappa)
      (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa m) e
  | _ => 1

def IsBall {m : ℕ} (a : MainAction D m) : Prop := ∃ w e, a = .inr (.inr (w,e))
def IsThird {m : ℕ} (a : MainAction D m) : Prop := ∃ w j, a = .inr (.inr (w,.inr (.inr j)))

noncomputable def ballLeader (hD : D.Nonempty) {m : ℕ} : MainAction D m → D
  | .inr (.inr (w,_)) => w
  | _ => ⟨hD.choose,hD.choose_spec⟩

noncomputable def ballSteps {m n : ℕ} (seed : Fin n → MainAction D m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => IsBall (seed i))

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_EntryIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus
open scoped Classical

def entryIndex {m : ℕ} : MainAction D m → ℕ
  | .inr (.inr (_,.inr (.inr j))) => j.val+1
  | _ => 0

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BlindUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus Guided FixedDyadic FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable local instance instDecidableEqAction_1_r3d01be_1 (D : Finset V) (M E J : ℕ) : DecidableEq (Action D M E J) := Classical.decEq _
noncomputable abbrev blindUpdate (D F S : Finset V) (hD : D.Nonempty)
    (Δ P : ℝ) (m : ℕ) :=
  update D F S hD Δ P mainKappa m (firstSize mainKappa)
    (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa m)

end MetricKMedianRecovery.Sampling.Comparison

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
open MetricKMedianRecovery RadiusMenus Guided FixedDyadic FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable local instance instDecidableEqAction_2_r3d01be_1 (D : Finset V) (M E J : ℕ) : DecidableEq (Action D M E J) := Classical.decEq _
noncomputable abbrev IntegralBits (D : Finset V) (Δ : ℝ) (m : ℕ) :=
  Fin (2*m) → Fin (integralPrecision D Δ m) → Bool

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_Nearest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalOpenability
open RationalLinearFeasibility
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

noncomputable def paymentForm (loc : D → X) (d : X → D → ℚ) (F W : Finset X)
    (v z : ℚ) (i : X) : Form (Variables D F) := by
  classical
  exact Form.sum (fun j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then
    if dist i (loc j) ≤ (v:ℝ)*(z:ℝ) then (bid F j).sub (Form.const ((1-3*v)*d i j))
    else Form.const (max (z-(1-3*v)*d i j) 0)
    else Form.const (max ((1-3*v)*nearest d W j-(1-3*v)*d i j) 0))

noncomputable def dualForm (loc : D → X) (d : X → D → ℚ) (F W : Finset X)
    (v z : ℚ) (f : F) (a j : D) : Form (Variables D F) := by
  classical
  exact if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then
    (bid F j).sub (Form.const (d f j))
    else (bid F a).sub (Form.const (2*d f j+d f a))

noncomputable def system (loc : D → X) (d : X → D → ℚ) (F W : Finset X)
    (v z lam eta : ℚ) (i : X) : Kind D W F → Form (Variables D F) := by
  classical
  exact fun k => match k with
  | .lower j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then (Form.const z).sub (bid F j) else Form.const 0
  | .upper j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then (bid F j).sub (Form.const ((1+v^2)*z)) else Form.const 0
  | .cap j f => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then (bid F j).sub (Form.const ((1-3*v)*d f j)) else Form.const 0
  | .far j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j ∧ (v:ℝ)*(z:ℝ)<dist i (loc j) then (bid F j).sub (Form.const z) else Form.const 0
  | .payment => (Form.const (lam-(Fintype.card D:ℚ)*eta)).sub (paymentForm loc d F W v z i)
  | .slackZero f a j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a then (Form.const 0).sub (slack f a j) else Form.const 0
  | .slackTerm f a j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a then (dualForm loc d F W v z f a j).sub (slack f a j) else Form.const 0
  | .dual f a => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a then (Form.sum (fun j => slack f a j)).sub (Form.const lam) else Form.const 0

end MetricKMedianRecovery.RationalOpenability

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StoredForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability

noncomputable def State.real {m d : ℕ} (s : State m d) : ExecutionState (Fin d) (Fin m) :=
  ⟨s.opened,(s.phase:ℝ),fun j => (s.budget[j]:ℝ)⟩

end MetricKMedianRecovery.RationalPhase

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

structure RegularDualWitness {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (F : Finset X) (v lam : ℝ) (s s' : ExecutionState D X) where
  facility : X
  witness : Finset X
  bid : D → ℝ
  contains : s.opened ⊆ witness
  admissible : admissibleBids loc (1 - 3 * v) (1 + v ^ 2) v s.phase witness facility bid
  dual : ∀ i ∈ F, ∀ a, activeAt loc (1 - 3 * v) s.phase witness a →
    openingDual loc (1 - 3 * v) s.phase witness i bid a ≤ lam
  updated : s' = regularUpdate loc (1 - 3 * v) s facility witness bid

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RemovalReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

structure RemovalReplay (D X : Type*) [Fintype D] [PseudoMetricSpace X]
    (steps : ℕ) (t K lam : ℝ) where
  location : D → X
  regular : Finset X
  before : Fin steps → Finset X
  after : Fin steps → Finset X
  phase : Fin steps → ℝ
  removal : D → Fin steps
  budget : D → ℝ
  phase_nonneg : ∀ n, 0 ≤ phase n
  before_mono : Monotone before
  after_in_later : ∀ n m, n < m → after n ⊆ before m
  active_threshold : ∀ j f, f ∈ before (removal j) →
    phase (removal j) ≤ t * dist (location j) f
  post_removal : ∀ j, ∃ f ∈ after (removal j),
    t * dist (location j) f ≤ K * phase (removal j)
  final_cap : ∀ j, budget j ≤ K * phase (removal j)
  no_overbid : ∀ n i, i ∈ regular →
    (∑ j, max ((if removal j < n then t * nearestDistance (location j) (before n)
      else phase n) - dist i (location j)) 0) ≤ lam

namespace RemovalReplay

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]
  {steps : ℕ} {t K lam : ℝ} (R : RemovalReplay D X steps t K lam)

noncomputable def boundaryBid (n : Fin steps) (j : D) : ℝ :=
  if R.removal j < n then t * nearestDistance (R.location j) (R.before n)
  else R.phase n

end RemovalReplay

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalMetricInput

def outputBits (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) : List Bool :=
  List.ofFn (fun i : Fin I.pointCount => decide (i ∈ S))

end MetricKMedianRecovery.RationalMetricInput

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CommonL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Rounding
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma edge_pos (u : ℝ) {C : ℕ} (hC : 0 < C) {x y : V} (hxy : x ≠ y) :
    0 < edge u C x y := by
  rw [edge,ite_eq_right hxy]
  exact lt_min hC (lt_of_lt_of_le (by omega : 0 < (1:ℕ)) (le_max_left _ _))

lemma edge_triangle (u : ℝ) (hu : 0 < u) (C : ℕ) (x y z : V) :
    edge u C x z ≤ edge u C x y+edge u C y z := by
  by_cases hxz : x = z
  · subst z; rw [edge_self]; omega
  by_cases hxy : x = y
  · subst y; simp only [edge_self,zero_add,le_refl]
  by_cases hyz : y = z
  · subst z; simp only [edge_self,add_zero,le_refl]
  have hceil : ⌈dist x z/u⌉₊ ≤ ⌈dist x y/u⌉₊+⌈dist y z/u⌉₊ := by
    calc
      _ ≤ ⌈dist x y/u+dist y z/u⌉₊ := Nat.ceil_mono (by
        rw [← add_div]; exact div_le_div_of_nonneg_right (dist_triangle x y z) hu.le)
      _ ≤ _ := Nat.ceil_add_le _ _
  simp only [edge,ite_eq_right hxz,ite_eq_right hxy,ite_eq_right hyz]
  omega

@[instance_reducible]
noncomputable def metric (u : ℝ) (hu : 0 < u) (C : ℕ) (hC : 0 < C) : MetricSpace V where
  dist x y := edge u C x y
  dist_self x := by exact_mod_cast edge_self u C x
  dist_comm x y := by exact_mod_cast edge_symm u C x y
  dist_triangle x y z := by exact_mod_cast edge_triangle u hu C x y z
  eq_of_dist_eq_zero := by
    intro x y he
    by_contra hn
    have hh := edge_pos u hC hn
    have hz : edge u C x y = 0 := by exact_mod_cast he
    omega

end MetricKMedianRecovery.Rounding

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ReferenceBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling
open BitMachine BinarySamplingReference
variable {n l : ℕ}
def fromArrays (T : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) : State n :=
  ⟨T,List.ofFn (fun j=>(v j,r j))⟩
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_VirtualCast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Completion
variable {n : ℕ}
lemma State.real_length (s : State n) : s.real.leaves.length=s.leaves.length := List.length_map _
def State.center (s : State n) (i : Fin s.leaves.length) : Fin n := s.leaves[i.val].1
def State.radius (s : State n) (i : Fin s.leaves.length) : ℝ := (s.leaves[i.val].2:ℝ)
variable [PseudoMetricSpace (Fin n)]
noncomputable def State.assignment (S : Finset (Fin n)) (Δ : ℚ) (s : State n) : Fin n→Virtual (Fin n) s.leaves.length :=
  Virtual.cast s.real_length ∘ Sampling.completionAssignment S (Δ:ℝ) s.real
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open BitMachine RationalHeight
variable {n : ℕ}
def State.Height (s : State n) (H : ℕ) : Prop := ∀ z∈s.leaves,RationalHeight.Height z.2 H
end MetricKMedianRecovery.RationalSampling

end OAI
end


