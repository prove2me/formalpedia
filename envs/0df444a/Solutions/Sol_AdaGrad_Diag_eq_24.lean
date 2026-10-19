-- Prove2me | solution 1 for AdaGrad.Diag.eq_24
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:21:08.321897+00:00
-- url     : https://prove2.me/submissions/209df80a-5b4c-4b13-bc9a-9856913b478f

import Mathlib
set_option autoImplicit false

lemma eq24_step (S x : ℝ) (hS : 0 ≤ S) :
    x ^ 2 / Real.sqrt (S + x ^ 2) ≤ 2 * (Real.sqrt (S + x ^ 2) - Real.sqrt S) := by
  have hs : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  have hr : 0 ≤ Real.sqrt (S + x ^ 2) := Real.sqrt_nonneg _
  have hS2 : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS
  have hr2 : Real.sqrt (S + x ^ 2) ^ 2 = S + x ^ 2 := Real.sq_sqrt (by positivity)
  have hle : Real.sqrt S ≤ Real.sqrt (S + x ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
  rcases hr.eq_or_lt with h | h
  · rw [← h]; simp; linarith
  · rw [div_le_iff₀ h]
    nlinarith [mul_nonneg (sub_nonneg.2 hle) (sub_nonneg.2 hle), mul_nonneg hs (sub_nonneg.2 hle)]

theorem solution (a : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, a t ^ 2 / Real.sqrt (∑ τ ∈ Finset.Icc 1 t, a τ ^ 2)
      ≤ 2 * Real.sqrt (∑ τ ∈ Finset.Icc 1 T, a τ ^ 2) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have h := eq24_step (∑ τ ∈ Finset.Icc 1 n, a τ ^ 2) (a (n + 1))
      (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    linarith
