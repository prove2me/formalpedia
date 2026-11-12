-- Prove2me | solution 1 for AgreementTop736.Exact.eq3_conditioned_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:27:06.60133+00:00
-- url     : https://prove2.me/submissions/da13d04c-5bab-4829-9093-95c99ca23fe9

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized
import Theorems.Thm_AgreementTop736_Exact_sec3_1_cauchy_schwarz_variance

section
set_option autoImplicit false
namespace AgreementTop736.Exact.Dev.Eq3
open Finset AgreementTop736.Exact AgreementTop736.Exact.Scheme

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma rho_pos (S : Scheme V) (hS : S.IsValid) : 0 < S.ρ := by
  unfold Scheme.ρ
  have h1 := hS.n_pos
  have h2 := hS.n_lt_N
  apply div_pos
  · exact_mod_cast h1
  · exact_mod_cast (h1.trans h2)

lemma muD_nonneg (S : Scheme V) (hS : S.IsValid) (K H : Finset V) : 0 ≤ S.μ K * S.D K H := by
  rcases (hS.μ_nonneg K).eq_or_lt with h | h
  · rw [← h]; simp
  · exact mul_nonneg h.le (hS.D_nonneg K h H)

lemma muD_zero_of_muH (S : Scheme V) (hS : S.IsValid) (H : Finset V) (h : S.μH H = 0) (K : Finset V) :
    S.μ K * S.D K H = 0 := by
  unfold Scheme.μH at h
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun K _ => muD_nonneg S hS K H)).1 h K (mem_univ _)

lemma muH_nonneg (S : Scheme V) (hS : S.IsValid) (H : Finset V) : 0 ≤ S.μH H :=
  Finset.sum_nonneg fun K _ => muD_nonneg S hS K H

lemma key (S : Scheme V) (hS : S.IsValid) (H K K' : Finset V) :
    S.testWeight H K K' = S.μ K * S.D K H * S.U H K' := by
  unfold Scheme.testWeight Scheme.U
  rcases (muH_nonneg S hS H).eq_or_lt with h | h
  · rw [← h]
    have := muD_zero_of_muH S hS H h.symm K
    simp [this]
  · field_simp

lemma D_zero_of_not_mem (S : Scheme V) (hS : S.IsValid) (K : Finset V) (hK : 0 < S.μ K) (x : V)
    (hx : x ∉ K) (H : Finset V) : S.D K H * (if x ∈ H then 1 else 0) = 0 := by
  rcases (hS.D_nonneg K hK H).eq_or_lt with h | h
  · rw [← h]; simp
  · have := (hS.D_support K hK H h).1
    have : x ∉ H := fun hh => hx (this hh)
    simp [this]

lemma incl_zero (S : Scheme V) (hS : S.IsValid) (K : Finset V) (hK : 0 < S.μ K) (x : V)
    (hx : x ∉ K) : S.incl K x = 0 := by
  unfold Scheme.incl
  exact Finset.sum_eq_zero fun H _ => D_zero_of_not_mem S hS K hK x hx H

lemma probInH_eq (S : Scheme V) (hS : S.IsValid) (h1 : S.UniformInclusion) (x : V) :
    S.probInH x = S.ρ * S.pointMass x := by
  unfold Scheme.probInH Scheme.pointMass
  have : ∀ H, S.μH H * (if x ∈ H then (1:ℝ) else 0) = ∑ K, S.μ K * (S.D K H * (if x ∈ H then 1 else 0)) := by
    intro H
    unfold Scheme.μH
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro K _; ring
  simp_rw [this]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [← Finset.mul_sum]
  have hi : ∑ H, S.D K H * (if x ∈ H then (1:ℝ) else 0) = S.incl K x := rfl
  rw [hi]
  rcases (hS.μ_nonneg K).eq_or_lt with h | h
  · rw [← h]; simp
  · by_cases hxK : x ∈ K
    · rw [h1 K h x hxK]; simp [hxK]; ring
    · rw [incl_zero S hS K h x hxK]; simp [hxK]

lemma mx_eq (S : Scheme V) (hS : S.IsValid) (h1 : S.UniformInclusion) (x : V) (K K' : Finset V) :
    S.μx x K * S.Mx x K K' =
      (∑ H, S.μ K * S.D K H * (if x ∈ H then 1 else 0) * S.U H K') / (S.ρ * S.pointMass x) := by
  have hρ := rho_pos S hS
  unfold Scheme.μx Scheme.Mx
  rcases (hS.μ_nonneg K).eq_or_lt with h | h
  · rw [← h]; simp
  · by_cases hxK : x ∈ K
    · rw [h1 K h x hxK]
      rw [Finset.mul_sum, Finset.sum_div]
      by_cases hp : S.pointMass x = 0
      · simp [hp]
      · apply Finset.sum_congr rfl
        intro H _
        simp only [hxK, if_true]
        field_simp
    · have : ∀ H, S.μ K * S.D K H * (if x ∈ H then (1:ℝ) else 0) * S.U H K' = 0 := by
        intro H
        have := D_zero_of_not_mem S hS K h x hxK H
        calc S.μ K * S.D K H * (if x ∈ H then (1:ℝ) else 0) * S.U H K'
            = S.μ K * (S.D K H * (if x ∈ H then (1:ℝ) else 0)) * S.U H K' := by ring
          _ = 0 := by rw [this]; simp
      rw [Finset.sum_eq_zero (fun H _ => this H), zero_div]
      simp [hxK]

lemma numer_eq (S : Scheme V) (hS : S.IsValid) (h1 : S.UniformInclusion) (x : V) (f : Finset V → ℝ) :
    (∑ H, ∑ K, ∑ K', S.testWeight H K K' * (if x ∈ H then 1 else 0) * (f K - f K') ^ 2) / S.probInH x
      = 2 * S.dirichlet x f ∨ S.probInH x = 0 := by
  by_cases hp : S.probInH x = 0
  · exact Or.inr hp
  left
  rw [probInH_eq S hS h1] at hp ⊢
  unfold Scheme.dirichlet
  simp_rw [mx_eq S hS h1]
  have e : ∑ H, ∑ K, ∑ K', S.testWeight H K K' * (if x ∈ H then 1 else 0) * (f K - f K') ^ 2
      = ∑ K, ∑ K', (∑ H, S.μ K * S.D K H * (if x ∈ H then 1 else 0) * S.U H K') * (f K - f K') ^ 2 := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro K _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro K' _
    apply Finset.sum_congr rfl
    intro H _
    rw [key S hS]; ring
  rw [e, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [Finset.sum_div, ← mul_assoc, show (2:ℝ) * (1 / 2) = 1 by norm_num, one_mul]
  apply Finset.sum_congr rfl
  intro K' _
  ring

end AgreementTop736.Exact.Dev.Eq3
namespace AgreementTop736.Exact
open Finset Scheme
open AgreementTop736.Exact.Dev.Eq3 in
theorem chk_eq3_conditioned_gap {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (h1 : S.UniformInclusion) {γ : ℝ} (hγ : 0 < γ)
    (h3 : S.HasConditionedGap γ) (F : Finset V → V → α) (g : V → α)
    (hg : S.IsCoordMajority F g) {a : ℝ} (ha : 0 < a) (x : V) (hx : 0 < S.pointMass x)
    (s : α) (hs : s ≠ g x) :
    γ * ∑ K, S.μx x K * phi F g a x s K ^ 2 ≤
      (∑ H, ∑ K, ∑ K', S.testWeight H K K' * (if x ∈ H then 1 else 0) *
          (phi F g a x s K - phi F g a x s K') ^ 2) / S.probInH x := by
  have hρ := rho_pos S hS
  have hpi : 0 < S.probInH x := by rw [probInH_eq S hS h1]; positivity
  rcases numer_eq S hS h1 x (phi F g a x s) with h | h
  · rw [h]
    have hv := (AgreementTop736.Exact.sec3_1_cauchy_schwarz_variance S hS F g hg ha x hx s hs).2.2.2
    have hd := h3 x hx (phi F g a x s)
    nlinarith
  · exact absurd h hpi.ne'

end AgreementTop736.Exact
end

theorem solution : type_of% @AgreementTop736.Exact.chk_eq3_conditioned_gap := @AgreementTop736.Exact.chk_eq3_conditioned_gap
