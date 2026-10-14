-- Prove2me | solution 2 for ActuarialAnnuities.expectation_scale
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:04:59.971198+00:00
-- url     : https://prove2.me/submissions/6231587b-cba2-4948-82b4-7c16f5b698db

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bExpectedPV
open ActuarialAnnuities

theorem solution (h a n g delta : ℕ) (v c : ℝ) (b p : ℕ → ℝ) : bExpectedPV h a n g delta v (fun j => c*b j) p = c*bExpectedPV h a n g delta v b p := by
  simp only [bExpectedPV]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  have hpath : bPathPV h a n g delta v (fun j => c * b j) k = c * bPathPV h a n g delta v b k := by
    simp only [bPathPV, bEntitlement, bAlive]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    split_ifs <;> simp [mul_add, mul_assoc, mul_left_comm, mul_comm]
  rw [hpath]
  simp [mul_assoc, mul_left_comm, mul_comm]

