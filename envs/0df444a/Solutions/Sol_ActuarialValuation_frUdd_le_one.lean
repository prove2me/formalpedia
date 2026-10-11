-- Prove2me | solution 1 for ActuarialValuation.frUdd_le_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:26:20.795651+00:00
-- url     : https://prove2.me/submissions/32cf2fbe-3c52-4739-b96f-9a83e46b6a68

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frUddSurvival
open ActuarialValuation

theorem solution(q s : ℝ) (hq : 0 ≤ q) (hs : 0 ≤ s) : frUddSurvival q s ≤ 1 := by
  unfold frUddSurvival
  nlinarith [mul_nonneg hs hq]
