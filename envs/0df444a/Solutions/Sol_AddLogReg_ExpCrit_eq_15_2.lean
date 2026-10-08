-- Prove2me | solution 2 for AddLogReg.ExpCrit.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T07:05:25.425982+00:00
-- url     : https://prove2.me/submissions/13b35c1a-c8a2-4c72-9d8b-83975d38f908

import Mathlib

theorem solution (F : ℝ) :
    Real.exp F / (Real.exp (-F) + Real.exp F) =
      Real.exp (2 * F) / (1 + Real.exp (2 * F)) := by
  have hL : Real.exp (-F) + Real.exp F ≠ 0 :=
    (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
  have hR : 1 + Real.exp (2 * F) ≠ 0 :=
    (add_pos_of_nonneg_of_pos (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_pos _)).ne'
  rw [div_eq_div_iff hL hR]
  have h1 : Real.exp F * 1 = Real.exp (2 * F) * Real.exp (-F) := by
    rw [mul_one, ← Real.exp_add]
    ring_nf
  have h2 : Real.exp F * Real.exp (2 * F) = Real.exp (2 * F) * Real.exp F := by
    ring
  linarith
