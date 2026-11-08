-- Prove2me | solution 1 for AdaGradDHS.Diag.eq_24_root_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:27:43.982343+00:00
-- url     : https://prove2.me/submissions/b341670d-9025-40ac-8983-b584ec5670bb

import Mathlib

theorem solution (a : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, a t ^ 2 / Real.sqrt (∑ τ ∈ Finset.Icc 1 t, a τ ^ 2) ≤
      2 * Real.sqrt (∑ τ ∈ Finset.Icc 1 T, a τ ^ 2) := by
  have key : ∀ S b : ℝ, 0 ≤ b → b ≤ S → b / Real.sqrt S ≤ 2 * (Real.sqrt S - Real.sqrt (S - b)) := by
    intro S b hb hbS
    rcases eq_or_lt_of_le (le_trans hb hbS) with h0 | hpos
    · have hb0 : b = 0 := by linarith
      rw [← h0, hb0]
      simp
    · have hs := Real.sqrt_pos.mpr hpos
      rw [div_le_iff₀ hs]
      have h1 := Real.sq_sqrt hpos.le
      have h2 := Real.sq_sqrt (by linarith : 0 ≤ S - b)
      nlinarith [sq_nonneg (Real.sqrt S - Real.sqrt (S - b)), Real.sqrt_nonneg (S - b)]
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega) (fun τ => a τ ^ 2)]
    have hS : 0 ≤ ∑ τ ∈ Finset.Icc 1 T, a τ ^ 2 := Finset.sum_nonneg (fun τ _ => sq_nonneg _)
    have h := key (∑ τ ∈ Finset.Icc 1 T, a τ ^ 2 + a (T + 1) ^ 2) (a (T + 1) ^ 2) (sq_nonneg _)
      (by linarith)
    rw [add_sub_cancel_right] at h
    linarith
