-- Prove2me | solution 1 for ActuarialAnnuities.expectation_scale
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:35:47.651789+00:00
-- url     : https://prove2.me/submissions/e1cc3c5a-eb5b-42db-9cc1-3ecf4a3bcb8a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bExpectedPV
open ActuarialAnnuities

theorem solution(h a n g delta : ℕ) (v c : ℝ) (b p : ℕ → ℝ) : bExpectedPV h a n g delta v (fun j => c*b j) p = c*bExpectedPV h a n g delta v b p := by
  have hp : ∀ k, bPathPV h a n g delta v (fun j => c*b j) k = c*bPathPV h a n g delta v b k := by
    intro k
    unfold bPathPV
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  unfold bExpectedPV
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [hp]
  ring
