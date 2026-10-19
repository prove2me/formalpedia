-- Prove2me | solution 1 for AMPUniversality.Universal.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:26:38.21401+00:00
-- url     : https://prove2.me/submissions/ba12d2e0-b5bf-4fcb-9cf9-bfd87599338d

import Mathlib

set_option autoImplicit false

theorem solution (s x : ℝ) (hs : 0 < s) (hx : 0 < x) :
    x ^ s ≤ (s / Real.exp 1) ^ s * Real.exp x := by
  have hse : 0 < s / Real.exp 1 := div_pos hs (Real.exp_pos 1)
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hse, ← Real.exp_add, Real.exp_le_exp]
  have hl : Real.log (x / s) ≤ x / s - 1 := Real.log_le_sub_one_of_pos (div_pos hx hs)
  rw [Real.log_div hx.ne' hs.ne'] at hl
  rw [Real.log_div hs.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have h2 : s * (Real.log x - Real.log s) ≤ s * (x / s - 1) := mul_le_mul_of_nonneg_left hl hs.le
  have h3 : s * (x / s - 1) = x - s := by field_simp
  nlinarith [h2, h3]
