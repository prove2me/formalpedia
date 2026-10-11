-- Prove2me | solution 1 for ActuarialValuation.whFitPenalty_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:53:06.0317+00:00
-- url     : https://prove2.me/submissions/e2910862-6847-41a0-9db1-c18f1c434250

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFitPenalty
open ActuarialValuation

theorem solution(w g q : ℕ → ℝ) : whFitPenalty w g q 0 = 0 := by
  simp [whFitPenalty]
