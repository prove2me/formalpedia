-- Prove2me | solution 1 for ActuarialAnnuities.precommencement_death
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:39:06.029459+00:00
-- url     : https://prove2.me/submissions/bd7c7c6d-14ab-426c-8d30-39a7f32403fc

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bPathPV
open ActuarialAnnuities

theorem solution(h a n g delta k : ℕ) (v : ℝ) (b : ℕ → ℝ) (hk : k < a) : bPathPV h a n g delta v b k = 0 := by
  unfold bPathPV
  apply Finset.sum_eq_zero
  intro j _
  unfold bEntitlement bAlive
  split_ifs <;> simp_all <;> omega
