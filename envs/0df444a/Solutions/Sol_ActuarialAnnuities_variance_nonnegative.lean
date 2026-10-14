-- Prove2me | solution 1 for ActuarialAnnuities.variance_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T10:23:55.252615+00:00
-- url     : https://prove2.me/submissions/7930e14b-7db9-4468-92cc-55d8893e327f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bVariance
open ActuarialAnnuities

theorem solution(h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hp : bTotal h p = 1) (hn : ∀ k, 0 ≤ p k) : 0 ≤ bVariance h a n g delta v b p := by
  unfold bVariance bSecondMoment bExpectedPV
  unfold bTotal at hp
  set E := ∑ k ∈ Finset.range (h+1), p k * bPathPV h a n g delta v b k with hE
  have key : 0 ≤ ∑ k ∈ Finset.range (h+1), p k * (bPathPV h a n g delta v b k - E)^2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hn k) (sq_nonneg _))
  have expand : ∑ k ∈ Finset.range (h+1), p k * (bPathPV h a n g delta v b k - E)^2 = ∑ k ∈ Finset.range (h+1), (p k * (bPathPV h a n g delta v b k)^2 - 2*E*(p k * bPathPV h a n g delta v b k) + E^2 * p k) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hE, hp] at expand
  nlinarith [key, expand]
