-- Prove2me | solution 1 for AgreementTop736.Exact.eq6_local_witness_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:27:06.307843+00:00
-- url     : https://prove2.me/submissions/dee781f7-d98e-4e38-bf65-ec72301f2cdb

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized

section
set_option autoImplicit false
namespace AgreementTop736.Exact.Dev.Eq6
open AgreementTop736.Exact Finset Scheme

variable {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]

lemma fReg_nonneg (a u : ℝ) : 0 ≤ fReg a u := by unfold fReg; positivity

lemma psi_nonneg (S : Scheme V) (F : Finset V → V → α) (g : V → α) (a : ℝ) (x : V) (s : α)
    (K H : Finset V) : 0 ≤ S.psi F g a x s K H := by
  unfold Scheme.psi; split_ifs
  · exact fReg_nonneg _ _
  · exact le_rfl

lemma mu_D_nonneg (S : Scheme V) (hS : S.IsValid) (K H : Finset V) : 0 ≤ S.μ K * S.D K H := by
  rcases (hS.μ_nonneg K).eq_or_lt with h | h
  · rw [← h]; simp
  · exact mul_nonneg h.le (hS.D_nonneg K h H)

lemma μH_nonneg (S : Scheme V) (hS : S.IsValid) (H : Finset V) : 0 ≤ S.μH H :=
  Finset.sum_nonneg fun K _ => mu_D_nonneg S hS K H

lemma U_nonneg (S : Scheme V) (hS : S.IsValid) (H K : Finset V) : 0 ≤ S.U H K :=
  div_nonneg (mu_D_nonneg S hS K H) (μH_nonneg S hS H)

lemma tw_nonneg (S : Scheme V) (hS : S.IsValid) (H K K' : Finset V) : 0 ≤ S.testWeight H K K' :=
  mul_nonneg (mul_nonneg (μH_nonneg S hS H) (U_nonneg S hS H K)) (U_nonneg S hS H K')

lemma rho_pos (S : Scheme V) (hS : S.IsValid) : 0 < S.ρ := by
  unfold Scheme.ρ
  have := hS.n_pos
  have := hS.n_lt_N
  have : (0:ℝ) < S.n := by exact_mod_cast hS.n_pos
  have : (0:ℝ) < S.N := by exact_mod_cast (hS.n_pos.trans hS.n_lt_N)
  positivity

lemma psi_sq_inner (S : Scheme V) (F : Finset V → V → α) (g : V → α) (a : ℝ) (ha : 0 < a)
    (hρ : 0 < S.ρ) (x : V) (K H : Finset V) :
    ∑ s ∈ offLabels g x, (S.psi F g a x s K H) ^ 2 =
      if x ∈ H ∧ F K x ≠ g x then 1 / ((localErr F g K H : ℝ) / S.ρ + a) else 0 := by
  have hpos : 0 < (localErr F g K H : ℝ) / S.ρ + a := by positivity
  have hsq : fReg a ((localErr F g K H : ℝ) / S.ρ) ^ 2 = 1 / ((localErr F g K H : ℝ) / S.ρ + a) := by
    unfold fReg; rw [div_pow, Real.sq_sqrt hpos.le]; simp
  unfold Scheme.psi
  by_cases hx : x ∈ H
  · by_cases hF : F K x = g x
    · rw [Finset.sum_eq_zero]
      · simp [hF]
      · intro s hs
        have : s ≠ g x := by simpa [offLabels] using hs
        have : F K x ≠ s := by rw [hF]; exact fun h => this h.symm
        simp [this]
    · have hmem : F K x ∈ offLabels g x := by simp [offLabels, hF]
      rw [Finset.sum_eq_single (F K x)]
      · simp [hx, hF, hsq]
      · intro s _ hs; simp [Ne.symm hs]
      · intro h; exact absurd hmem h
  · simp [hx]

lemma psi_norm_le (S : Scheme V) (F : Finset V → V → α) (g : V → α) (a : ℝ) (ha : 0 < a)
    (hρ : 0 < S.ρ) (K H : Finset V) :
    ∑ x ∈ H, ∑ s ∈ offLabels g x, (S.psi F g a x s K H) ^ 2 ≤ S.ρ := by
  have h1 : ∑ x ∈ H, ∑ s ∈ offLabels g x, (S.psi F g a x s K H) ^ 2 =
      (localErr F g K H : ℝ) * (1 / ((localErr F g K H : ℝ) / S.ρ + a)) := by
    rw [Finset.sum_congr rfl (fun x _ => psi_sq_inner S F g a ha hρ x K H)]
    unfold localErr
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 3
    ext x; simp only [Finset.mem_filter]; tauto
  rw [h1]
  set Z : ℝ := (localErr F g K H : ℝ)
  have hZ : 0 ≤ Z := Nat.cast_nonneg _
  have hpos : 0 < Z / S.ρ + a := by positivity
  rw [mul_one_div, div_le_iff₀ hpos]
  have : Z / S.ρ * S.ρ = Z := by field_simp
  nlinarith [mul_pos hρ ha]

lemma psiDistSq_le (S : Scheme V) (F : Finset V → V → α) (g : V → α) (a : ℝ) (ha : 0 < a)
    (hρ : 0 < S.ρ) (H K K' : Finset V) :
    S.psiDistSq F g a H K K' ≤ 2 * S.ρ * (if ∃ x ∈ H, F K x ≠ F K' x then 1 else 0) := by
  split_ifs with h
  · have : S.psiDistSq F g a H K K' ≤
        ∑ x ∈ H, ∑ s ∈ offLabels g x, ((S.psi F g a x s K H) ^ 2 + (S.psi F g a x s K' H) ^ 2) := by
      unfold Scheme.psiDistSq
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun s _ => ?_
      nlinarith [psi_nonneg S F g a x s K H, psi_nonneg S F g a x s K' H,
        mul_nonneg (psi_nonneg S F g a x s K H) (psi_nonneg S F g a x s K' H)]
    refine this.trans ?_
    simp only [Finset.sum_add_distrib]
    have := psi_norm_le S F g a ha hρ K H
    have := psi_norm_le S F g a ha hρ K' H
    linarith
  · push_neg at h
    have hZ : localErr F g K H = localErr F g K' H := by
      unfold localErr
      congr 1
      apply Finset.filter_congr
      intro x hx; rw [h x hx]
    have : S.psiDistSq F g a H K K' = 0 := by
      unfold Scheme.psiDistSq
      apply Finset.sum_eq_zero; intro x hx
      apply Finset.sum_eq_zero; intro s _
      unfold Scheme.psi
      rw [h x hx, hZ]; simp
    rw [this]; simp

end AgreementTop736.Exact.Dev.Eq6
namespace AgreementTop736.Exact
open Finset Scheme
open AgreementTop736.Exact.Dev.Eq6 in
theorem chk_eq6_local_witness_bound {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (F : Finset V → V → α) (g : V → α) {a : ℝ} (ha : 0 < a) :
    ∑ H, ∑ K, ∑ K', S.testWeight H K K' * S.psiDistSq F g a H K K' ≤
      2 * S.ρ * S.rejectionProb F := by
  have hρ := rho_pos S hS
  unfold Scheme.rejectionProb
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun H _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun K _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun K' _ => ?_
  have := psiDistSq_le S F g a ha hρ H K K'
  have h0 := tw_nonneg S hS H K K'
  calc S.testWeight H K K' * S.psiDistSq F g a H K K'
      ≤ S.testWeight H K K' * (2 * S.ρ * (if ∃ x ∈ H, F K x ≠ F K' x then 1 else 0)) :=
        mul_le_mul_of_nonneg_left this h0
    _ = _ := by ring
end AgreementTop736.Exact
end

theorem solution : type_of% @AgreementTop736.Exact.chk_eq6_local_witness_bound := @AgreementTop736.Exact.chk_eq6_local_witness_bound
