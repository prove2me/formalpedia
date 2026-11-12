-- Prove2me | solution 1 for AgreementTop736.Exact.sec3_1_cauchy_schwarz_variance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:27:06.26358+00:00
-- url     : https://prove2.me/submissions/04c61ad2-a353-446a-950b-9078e08c1c9d

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized

section
set_option autoImplicit false
namespace AgreementTop736.Exact.Dev.CS
open Finset AgreementTop736.Exact AgreementTop736.Exact.Scheme

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma mux_nonneg (S : Scheme V) (hS : S.IsValid) (x : V) (hx : 0 < S.pointMass x) (K : Finset V) :
    0 ≤ S.μx x K := by
  unfold Scheme.μx
  have := hS.μ_nonneg K
  apply div_nonneg _ hx.le
  split_ifs <;> simp [this]

lemma mux_sum (S : Scheme V) (x : V) (hx : 0 < S.pointMass x) : ∑ K, S.μx x K = 1 := by
  unfold Scheme.μx
  rw [← Finset.sum_div]
  exact div_self hx.ne'

end AgreementTop736.Exact.Dev.CS
namespace AgreementTop736.Exact
open Finset Scheme
open AgreementTop736.Exact.Dev.CS in
theorem chk_sec3_1_cauchy_schwarz_variance {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (F : Finset V → V → α) (g : V → α)
    (hg : S.IsCoordMajority F g) {a : ℝ} (ha : 0 < a) (x : V) (hx : 0 < S.pointMass x)
    (s : α) (hs : s ≠ g x) :
    S.labelFreq F x s ≤ 1 / 2 ∧
    (∑ K, S.μx x K * phi F g a x s K) ^ 2 ≤
      S.labelFreq F x s * ∑ K, S.μx x K * phi F g a x s K ^ 2 ∧
    S.labelFreq F x s * ∑ K, S.μx x K * phi F g a x s K ^ 2 ≤
      (1 / 2) * ∑ K, S.μx x K * phi F g a x s K ^ 2 ∧
    (1 / 2) * ∑ K, S.μx x K * phi F g a x s K ^ 2 ≤
      variance (S.μx x) (phi F g a x s) := by
  have hnn := mux_nonneg S hS x hx
  have h1 := mux_sum S x hx
  have hle := hg x hx s
  have hsum : S.labelFreq F x s + S.labelFreq F x (g x) ≤ 1 := by
    unfold Scheme.labelFreq
    rw [← Finset.sum_add_distrib]
    refine le_trans ?_ h1.le
    apply Finset.sum_le_sum
    intro K _
    have := hnn K
    by_cases h : F K x = s
    · have h2 : F K x ≠ g x := by rw [h]; exact hs
      rw [if_pos h, if_neg h2]; simp
    · rw [if_neg h]; split_ifs <;> linarith
  have hhalf : S.labelFreq F x s ≤ 1 / 2 := by linarith
  have hE : 0 ≤ ∑ K, S.μx x K * phi F g a x s K ^ 2 :=
    Finset.sum_nonneg fun K _ => mul_nonneg (hnn K) (sq_nonneg _)
  have hCS : (∑ K, S.μx x K * phi F g a x s K) ^ 2 ≤
      S.labelFreq F x s * ∑ K, S.μx x K * phi F g a x s K ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Finset V))
      (fun K => Real.sqrt (S.μx x K) * (if F K x = s then 1 else 0))
      (fun K => Real.sqrt (S.μx x K) * phi F g a x s K)
    have e1 : ∑ K, (Real.sqrt (S.μx x K) * (if F K x = s then (1:ℝ) else 0)) *
        (Real.sqrt (S.μx x K) * phi F g a x s K) = ∑ K, S.μx x K * phi F g a x s K := by
      apply Finset.sum_congr rfl
      intro K _
      have h2 : Real.sqrt (S.μx x K) * Real.sqrt (S.μx x K) = S.μx x K := Real.mul_self_sqrt (hnn K)
      by_cases h : F K x = s
      · rw [if_pos h, mul_one, ← mul_assoc, h2]
      · have : phi F g a x s K = 0 := by simp [phi, h]
        simp [this]
    have e2 : ∑ K, (Real.sqrt (S.μx x K) * (if F K x = s then (1:ℝ) else 0)) ^ 2
        = S.labelFreq F x s := by
      unfold Scheme.labelFreq
      apply Finset.sum_congr rfl
      intro K _
      rw [mul_pow, Real.sq_sqrt (hnn K)]
      split_ifs <;> simp
    have e3 : ∑ K, (Real.sqrt (S.μx x K) * phi F g a x s K) ^ 2
        = ∑ K, S.μx x K * phi F g a x s K ^ 2 := by
      apply Finset.sum_congr rfl
      intro K _
      rw [mul_pow, Real.sq_sqrt (hnn K)]
    rw [e1, e2, e3] at this
    exact this
  refine ⟨hhalf, hCS, mul_le_mul_of_nonneg_right hhalf hE, ?_⟩
  unfold variance
  have := mul_le_mul_of_nonneg_right hhalf hE
  linarith

end AgreementTop736.Exact
end

theorem solution : type_of% @AgreementTop736.Exact.chk_sec3_1_cauchy_schwarz_variance := @AgreementTop736.Exact.chk_sec3_1_cauchy_schwarz_variance
