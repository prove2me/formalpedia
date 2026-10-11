-- Prove2me | solution 1 for ActuarialValuation.mackDenominator_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:24:11.930309+00:00
-- url     : https://prove2.me/submissions/fd4ad0e6-744f-48c6-bb3e-29ba58f9b858

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackDenominator
open ActuarialValuation

theorem solution(c : ℕ → ℕ → ℝ) (j : ℕ) : mackDenominator c 0 j = 0 := by
  simp [mackDenominator]
