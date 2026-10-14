-- Prove2me | solution 1 for ActuarialAnnuities.path_after_horizon
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:31:32.099111+00:00
-- url     : https://prove2.me/submissions/a363e4e9-1f25-4e58-8b4c-d1c38c79d388

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bPathPV
open ActuarialAnnuities

theorem solution(h a n g delta k : ℕ) (v : ℝ) (b : ℕ → ℝ) (ha : h ≤ a) : bPathPV h a n g delta v b k = 0 := by
  unfold bPathPV
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  rw [if_neg (by omega)]
