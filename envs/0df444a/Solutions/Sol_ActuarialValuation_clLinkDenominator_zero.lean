-- Prove2me | solution 1 for ActuarialValuation.clLinkDenominator_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:06:21.583856+00:00
-- url     : https://prove2.me/submissions/8c239b9f-f852-4583-a9be-b5a356d3b2d9

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clLinkDenominator
open ActuarialValuation

theorem solution(p : ℕ → ℕ → ℝ) (j : ℕ) : clLinkDenominator p 0 j = 0 := by
  simp [clLinkDenominator]
