-- Prove2me | solution 1 for ActuarialAnnuities.variance_scale
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:45:26.457983+00:00
-- url     : https://prove2.me/submissions/73679ba7-f362-42b0-acc2-92fc75dd8d29

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bVariance
open ActuarialAnnuities

theorem solution(h a n g delta : ℕ) (v c : ℝ) (b p : ℕ → ℝ) : bVariance h a n g delta v (fun j => c*b j) p = c^2*bVariance h a n g delta v b p := by
  have key : ∀ k, bPathPV h a n g delta v (fun j => c*b j) k = c * bPathPV h a n g delta v b k := by
    intro k
    unfold bPathPV
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  unfold bVariance bSecondMoment bExpectedPV
  simp only [key]
  have h1 : ∑ k ∈ Finset.range (h+1), p k * (c * bPathPV h a n g delta v b k)^2 = c^2 * ∑ k ∈ Finset.range (h+1), p k * (bPathPV h a n g delta v b k)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h2 : ∑ k ∈ Finset.range (h+1), p k * (c * bPathPV h a n g delta v b k) = c * ∑ k ∈ Finset.range (h+1), p k * bPathPV h a n g delta v b k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h1, h2]
  ring
