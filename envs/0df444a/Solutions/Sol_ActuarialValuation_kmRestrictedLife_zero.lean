-- Prove2me | solution 1 for ActuarialValuation.kmRestrictedLife_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:45:29.511994+00:00
-- url     : https://prove2.me/submissions/b330758f-184f-4c47-9e4b-a482044cfde4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmRestrictedLife
open ActuarialValuation

theorem solution(r d : ℕ → ℝ) : kmRestrictedLife r d 0 = 0 := by
  simp [kmRestrictedLife]
