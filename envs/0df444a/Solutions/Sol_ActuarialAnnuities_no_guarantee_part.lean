-- Prove2me | solution 1 for ActuarialAnnuities.no_guarantee_part
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:14:18.334747+00:00
-- url     : https://prove2.me/submissions/cbac1d83-3189-4b85-bc86-ad6ac3f2005b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bGuaranteedPV
open ActuarialAnnuities

theorem solution(h a n delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : bGuaranteedPV h a n 0 delta v b p = 0 := by
  unfold bGuaranteedPV
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (by omega)]
