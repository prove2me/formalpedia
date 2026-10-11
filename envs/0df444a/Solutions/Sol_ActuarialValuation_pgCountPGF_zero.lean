-- Prove2me | solution 1 for ActuarialValuation.pgCountPGF_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:49:15.073951+00:00
-- url     : https://prove2.me/submissions/5dca4c9e-e49b-4bae-84d4-0b7feefa7a7c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgCountPGF
open ActuarialValuation

theorem solution(p : ℕ → ℝ) (z : ℝ) : pgCountPGF p 0 z = p 0 := by
  simp [pgCountPGF]
