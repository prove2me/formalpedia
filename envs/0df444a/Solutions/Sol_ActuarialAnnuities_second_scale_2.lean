-- Prove2me | solution 2 for ActuarialAnnuities.second_scale
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:09:10.300237+00:00
-- url     : https://prove2.me/submissions/e90e37ee-1c8a-4b4f-b7ad-a52f12f1407b

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSecondMoment
open ActuarialAnnuities

theorem solution (h a n g delta : ℕ) (v c : ℝ) (b p : ℕ → ℝ) : bSecondMoment h a n g delta v (fun j => c*b j) p = c^2*bSecondMoment h a n g delta v b p := by
  simp only [bSecondMoment]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  have hpath : bPathPV h a n g delta v (fun j => c * b j) k = c * bPathPV h a n g delta v b k := by
    simp only [bPathPV, bEntitlement, bAlive]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    split_ifs <;> simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hpath, mul_pow]
  simp [mul_assoc, mul_left_comm, mul_comm]

