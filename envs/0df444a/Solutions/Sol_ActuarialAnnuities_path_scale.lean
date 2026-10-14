-- Prove2me | solution 1 for ActuarialAnnuities.path_scale
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:01:30.924375+00:00
-- url     : https://prove2.me/submissions/f0835e68-09c4-43bc-9713-46512659c4b0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bPathPV
open ActuarialAnnuities

theorem solution(h a n g delta k : ℕ) (v c : ℝ) (b : ℕ → ℝ) : bPathPV h a n g delta v (fun j => c*b j) k = c*bPathPV h a n g delta v b k := by
  unfold bPathPV
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring
