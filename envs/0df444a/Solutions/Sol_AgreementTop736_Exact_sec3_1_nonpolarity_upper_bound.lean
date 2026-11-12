-- Prove2me | solution 1 for AgreementTop736.Exact.sec3_1_nonpolarity_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:27:07.466586+00:00
-- url     : https://prove2.me/submissions/4f7d9f62-4458-4f58-9db8-80be088754f5

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized
import Theorems.Thm_AgreementTop736_Exact_eq6_local_witness_bound
import Theorems.Thm_AgreementTop736_Exact_eq7_residual_bound

section
set_option autoImplicit false
namespace AgreementTop736.Exact.Dev.Upper
open AgreementTop736.Exact Finset Scheme

variable {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]

lemma muD_nonneg (S : Scheme V) (hS : S.IsValid) (K H : Finset V) : 0 ≤ S.μ K * S.D K H := by
  rcases (hS.μ_nonneg K).eq_or_lt with h | h
  · rw [← h]; simp
  · exact mul_nonneg h.le (hS.D_nonneg K h H)

lemma μH_nn (S : Scheme V) (hS : S.IsValid) (H : Finset V) : 0 ≤ S.μH H :=
  Finset.sum_nonneg fun K _ => muD_nonneg S hS K H

lemma U_nn (S : Scheme V) (hS : S.IsValid) (H K : Finset V) : 0 ≤ S.U H K :=
  div_nonneg (muD_nonneg S hS K H) (μH_nn S hS H)

lemma tw_nn (S : Scheme V) (hS : S.IsValid) (H K K' : Finset V) : 0 ≤ S.testWeight H K K' :=
  mul_nonneg (mul_nonneg (μH_nn S hS H) (U_nn S hS H K)) (U_nn S hS H K')

lemma sum_U (S : Scheme V) (H : Finset V) (h : 0 < S.μH H) : ∑ K, S.U H K = 1 := by
  unfold Scheme.U
  rw [← Finset.sum_div]
  exact div_self h.ne'

/-- `∑_{K'} testWeight H K K' = μK D K H`. -/
lemma sum_tw (S : Scheme V) (hS : S.IsValid) (H K : Finset V) :
    ∑ K', S.testWeight H K K' = S.μ K * S.D K H := by
  rcases (μH_nn S hS H).eq_or_lt with h | h
  · have h0 : S.μ K * S.D K H = 0 := by
      have hle := Finset.single_le_sum (f := fun K => S.μ K * S.D K H)
        (fun K _ => muD_nonneg S hS K H) (Finset.mem_univ K)
      have hH : S.μH H = ∑ K, S.μ K * S.D K H := rfl
      have : S.μ K * S.D K H ≤ 0 := by rw [← hH] at hle; linarith
      exact le_antisymm this (muD_nonneg S hS K H)
    rw [h0]; simp [Scheme.testWeight, ← h]
  · unfold Scheme.testWeight
    rw [← Finset.mul_sum, sum_U S H h, mul_one]
    unfold Scheme.U
    field_simp

/-- cross-term nonnegativity -/
lemma cross_nn (S : Scheme V) (hS : S.IsValid) (H : Finset V) (r : Finset V → ℝ) :
    0 ≤ ∑ K, ∑ K', S.testWeight H K K' * (r K * r K') := by
  have : ∑ K, ∑ K', S.testWeight H K K' * (r K * r K') =
      S.μH H * (∑ K, S.U H K * r K) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun K' _ => ?_
    unfold Scheme.testWeight; ring
  rw [this]; exact mul_nonneg (μH_nn S hS H) (sq_nonneg _)

lemma lemA (S : Scheme V) (hS : S.IsValid) (H : Finset V) (r : Finset V → ℝ) :
    ∑ K, ∑ K', S.testWeight H K K' * (r K - r K') ^ 2 ≤
      2 * ∑ K, ∑ K', S.testWeight H K K' * (r K) ^ 2 := by
  have hsym : ∑ K, ∑ K', S.testWeight H K K' * (r K') ^ 2 =
      ∑ K, ∑ K', S.testWeight H K K' * (r K) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun K' _ => ?_
    unfold Scheme.testWeight; ring
  have hx := cross_nn S hS H r
  have : ∑ K, ∑ K', S.testWeight H K K' * (r K - r K') ^ 2 =
      ∑ K, ∑ K', S.testWeight H K K' * (r K) ^ 2 +
      ∑ K, ∑ K', S.testWeight H K K' * (r K') ^ 2 -
      2 * ∑ K, ∑ K', S.testWeight H K K' * (r K * r K') := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun K' _ => ?_
    ring
  rw [this, hsym]; linarith

lemma swap4 (H : Finset V) (g : V → α) (f : Finset V → Finset V → V → α → ℝ) :
    ∑ K : Finset V, ∑ K' : Finset V, ∑ x ∈ H, ∑ s ∈ offLabels g x, f K K' x s =
      ∑ x ∈ H, ∑ s ∈ offLabels g x, ∑ K : Finset V, ∑ K' : Finset V, f K K' x s := by
  calc ∑ K : Finset V, ∑ K' : Finset V, ∑ x ∈ H, ∑ s ∈ offLabels g x, f K K' x s
      = ∑ K : Finset V, ∑ x ∈ H, ∑ K' : Finset V, ∑ s ∈ offLabels g x, f K K' x s :=
        Finset.sum_congr rfl fun K _ => Finset.sum_comm
    _ = ∑ K : Finset V, ∑ x ∈ H, ∑ s ∈ offLabels g x, ∑ K' : Finset V, f K K' x s :=
        Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x ∈ H, ∑ K : Finset V, ∑ s ∈ offLabels g x, ∑ K' : Finset V, f K K' x s :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun x _ => Finset.sum_comm

lemma lemB (S : Scheme V) (hS : S.IsValid) (F : Finset V → V → α) (g : V → α) (a : ℝ)
    (H : Finset V) :
    ∑ K, ∑ K', S.testWeight H K K' *
        (∑ x ∈ H, ∑ s ∈ offLabels g x,
          ((phi F g a x s K - S.psi F g a x s K H) - (phi F g a x s K' - S.psi F g a x s K' H)) ^ 2)
      ≤ 2 * ∑ K, S.μ K * S.D K H * S.residualSq F g a K H := by
  set R : V → α → Finset V → ℝ := fun x s K => phi F g a x s K - S.psi F g a x s K H with hR
  have h1 : ∑ K, ∑ K', S.testWeight H K K' *
        (∑ x ∈ H, ∑ s ∈ offLabels g x, (R x s K - R x s K') ^ 2)
      = ∑ x ∈ H, ∑ s ∈ offLabels g x, ∑ K, ∑ K', S.testWeight H K K' * (R x s K - R x s K') ^ 2 := by
    rw [← swap4 H g (fun K K' x s => S.testWeight H K K' * (R x s K - R x s K') ^ 2)]
    refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun K' _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
  have h2 : ∑ K, ∑ K', S.testWeight H K K' * S.residualSq F g a K H
      = ∑ x ∈ H, ∑ s ∈ offLabels g x, ∑ K, ∑ K', S.testWeight H K K' * (R x s K) ^ 2 := by
    rw [← swap4 H g (fun K K' x s => S.testWeight H K K' * (R x s K) ^ 2)]
    refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun K' _ => ?_
    unfold Scheme.residualSq
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
  have h3 : ∑ K, ∑ K', S.testWeight H K K' * S.residualSq F g a K H
      = ∑ K, S.μ K * S.D K H * S.residualSq F g a K H := by
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [← Finset.sum_mul, sum_tw S hS]
  change ∑ K, ∑ K', S.testWeight H K K' *
        (∑ x ∈ H, ∑ s ∈ offLabels g x, (R x s K - R x s K') ^ 2) ≤ _
  rw [h1, ← h3, h2, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  exact lemA S hS H (R x s)

lemma pt (A B : ℝ) : (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by nlinarith [sq_nonneg (A - B)]

lemma phiDist_le (S : Scheme V) (F : Finset V → V → α) (g : V → α) (a : ℝ) (H K K' : Finset V) :
    phiDistSq F g a H K K' ≤
      2 * (∑ x ∈ H, ∑ s ∈ offLabels g x,
          ((phi F g a x s K - S.psi F g a x s K H) - (phi F g a x s K' - S.psi F g a x s K' H)) ^ 2)
        + 2 * S.psiDistSq F g a H K K' := by
  unfold phiDistSq Scheme.psiDistSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  have := pt ((phi F g a x s K - S.psi F g a x s K H) - (phi F g a x s K' - S.psi F g a x s K' H))
    (S.psi F g a x s K H - S.psi F g a x s K' H)
  have e : (phi F g a x s K - phi F g a x s K') =
    ((phi F g a x s K - S.psi F g a x s K H) - (phi F g a x s K' - S.psi F g a x s K' H)) +
    (S.psi F g a x s K H - S.psi F g a x s K' H) := by ring
  rw [e]; exact this

end AgreementTop736.Exact.Dev.Upper
namespace AgreementTop736.Exact
open Finset Scheme
open AgreementTop736.Exact.Dev.Upper in
theorem chk_sec3_1_nonpolarity_upper_bound {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (h2 : S.VarianceBound) (F : Finset V → V → α) (g : V → α)
    {a : ℝ} (ha : 0 < a) :
    S.Enp F g a ≤ 4 * (1 - S.ρ) / a * S.Vreg F g a + 4 * S.ρ * S.rejectionProb F := by
  have e6 := AgreementTop736.Exact.eq6_local_witness_bound S hS F g ha
  have e7 := AgreementTop736.Exact.eq7_residual_bound S hS h2 F g ha
  set Rd : Finset V → Finset V → Finset V → ℝ := fun H K K' => ∑ x ∈ H, ∑ s ∈ offLabels g x,
    ((phi F g a x s K - S.psi F g a x s K H) - (phi F g a x s K' - S.psi F g a x s K' H)) ^ 2 with hRd
  have step1 : S.Enp F g a ≤ ∑ H, ∑ K, ∑ K', S.testWeight H K K' *
      (2 * Rd H K K' + 2 * S.psiDistSq F g a H K K') := by
    unfold Scheme.Enp
    refine Finset.sum_le_sum fun H _ => Finset.sum_le_sum fun K _ => Finset.sum_le_sum fun K' _ => ?_
    exact mul_le_mul_of_nonneg_left (phiDist_le S F g a H K K') (tw_nn S hS H K K')
  have step2 : ∑ H, ∑ K, ∑ K', S.testWeight H K K' *
      (2 * Rd H K K' + 2 * S.psiDistSq F g a H K K') =
      2 * ∑ H, ∑ K, ∑ K', S.testWeight H K K' * Rd H K K' +
      2 * ∑ H, ∑ K, ∑ K', S.testWeight H K K' * S.psiDistSq F g a H K K' := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun K' _ => ?_
    ring
  have step3 : ∑ H, ∑ K, ∑ K', S.testWeight H K K' * Rd H K K' ≤
      2 * ∑ K, ∑ H, S.μ K * S.D K H * S.residualSq F g a K H := by
    rw [Finset.sum_comm (f := fun K H => S.μ K * S.D K H * S.residualSq F g a K H), Finset.mul_sum]
    refine Finset.sum_le_sum fun H _ => ?_
    exact lemB S hS F g a H
  have hρτ : S.rejectionProb F = S.rejectionProb F := rfl
  calc S.Enp F g a ≤ _ := step1
    _ = _ := step2
    _ ≤ 2 * (2 * ((1 - S.ρ) / a * S.Vreg F g a)) + 2 * (2 * S.ρ * S.rejectionProb F) := by
        have := mul_le_mul_of_nonneg_left (step3.trans (mul_le_mul_of_nonneg_left e7 (by norm_num : (0:ℝ) ≤ 2))) (by norm_num : (0:ℝ) ≤ 2)
        have h6 := mul_le_mul_of_nonneg_left e6 (by norm_num : (0:ℝ) ≤ 2)
        linarith
    _ = _ := by ring
end AgreementTop736.Exact
end

theorem solution : type_of% @AgreementTop736.Exact.chk_sec3_1_nonpolarity_upper_bound := @AgreementTop736.Exact.chk_sec3_1_nonpolarity_upper_bound
