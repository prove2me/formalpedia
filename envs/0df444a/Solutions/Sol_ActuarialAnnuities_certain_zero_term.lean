-- Prove2me | solution 1 for ActuarialAnnuities.certain_zero_term
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:09:38.824965+00:00
-- url     : https://prove2.me/submissions/32405932-8076-4c82-9333-30d5c08d5f6b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bCertainPV
open ActuarialAnnuities

theorem solution(h a delta : ℕ) (v : ℝ) (b : ℕ → ℝ) : bCertainPV h a 0 delta v b = 0 := by
  unfold bCertainPV
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (by omega)]
