-- Prove2me | solution 2 for ActuarialAnnuities.variance_scale
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:09:11.737537+00:00
-- url     : https://prove2.me/submissions/cc0675e8-16b9-4a97-a7e7-646c4883df57

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bVariance
open ActuarialAnnuities

theorem solution (h a n g delta : ℕ) (v c : ℝ) (b p : ℕ → ℝ) : bVariance h a n g delta v (fun j => c*b j) p = c^2*bVariance h a n g delta v b p := by
  simp only [bVariance]
  have hs : bSecondMoment h a n g delta v (fun j => c * b j) p = c ^ 2 * bSecondMoment h a n g delta v b p := by
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
  have he : bExpectedPV h a n g delta v (fun j => c * b j) p = c * bExpectedPV h a n g delta v b p := by
    simp only [bExpectedPV]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    have hpath : bPathPV h a n g delta v (fun j => c * b j) k = c * bPathPV h a n g delta v b k := by
      simp only [bPathPV, bEntitlement, bAlive]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      split_ifs <;> simp [mul_assoc, mul_left_comm, mul_comm]
    rw [hpath]
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hs, he, mul_pow]
  ring

