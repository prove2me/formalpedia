-- Prove2me | solution 1 for ActuarialAnnuities.fractional_one_instalment
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:37:00.715395+00:00
-- url     : https://prove2.me/submissions/9e4aeae3-5c6f-4b21-902b-ce1f5876f78a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bFractionalExpectedPV
open ActuarialAnnuities

theorem solution(h a n g delta : ℕ) (w : ℝ) (b p : ℕ → ℝ) : bFractionalExpectedPV h a n g delta 1 w b p = bExpectedPV h a n g delta w b p := by
  unfold bFractionalExpectedPV bExpectedPV
  simp only [mul_one, Nat.cast_one, div_one]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  congr 1
  unfold bUDDMicroMass
  split_ifs with h1 h2 <;> simp_all <;> omega
