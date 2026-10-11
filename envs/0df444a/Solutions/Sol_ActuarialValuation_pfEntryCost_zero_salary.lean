-- Prove2me | solution 1 for ActuarialValuation.pfEntryCost_zero_salary
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:25:33.272993+00:00
-- url     : https://prove2.me/submissions/818e7150-625e-4ddb-b243-728080844c2d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfEntryNormalCost
open ActuarialValuation

theorem solution(rate : ℝ) : pfEntryNormalCost rate 0=0 := by
  simp [pfEntryNormalCost]
