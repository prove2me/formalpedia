-- Prove2me | solution 1 for ActuarialAnnuities.second_scale
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:35:52.609112+00:00
-- url     : https://prove2.me/submissions/4a39293a-d5e8-48bc-b848-04d2455d7227

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSecondMoment
open ActuarialAnnuities

theorem solution(h a n g delta : ℕ) (v c : ℝ) (b p : ℕ → ℝ) : bSecondMoment h a n g delta v (fun j => c*b j) p = c^2*bSecondMoment h a n g delta v b p := by
  have hp : ∀ k, bPathPV h a n g delta v (fun j => c*b j) k = c*bPathPV h a n g delta v b k := by
    intro k
    unfold bPathPV
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  unfold bSecondMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [hp]
  ring
