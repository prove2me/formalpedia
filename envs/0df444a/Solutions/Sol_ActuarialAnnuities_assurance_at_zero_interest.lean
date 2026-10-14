-- Prove2me | solution 1 for ActuarialAnnuities.assurance_at_zero_interest
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:30:54.946311+00:00
-- url     : https://prove2.me/submissions/f79c7935-14a2-4a44-b1c2-71a4c43d8b21

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bAssurancePV
open ActuarialAnnuities

theorem solution(h : ℕ) (p : ℕ → ℝ) : bAssurancePV h 1 p = bTotal h p - p h := by
  unfold bAssurancePV bTotal
  simp only [one_pow, mul_one]
  rw [Finset.sum_range_succ]
  ring
