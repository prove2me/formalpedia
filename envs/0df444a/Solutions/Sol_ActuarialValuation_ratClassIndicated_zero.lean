-- Prove2me | solution 1 for ActuarialValuation.ratClassIndicated_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:29:26.496123+00:00
-- url     : https://prove2.me/submissions/3d4c3961-49f7-4ca0-9629-adfa88df154e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratClassIndicated
open ActuarialValuation

theorem solution(severity : ℝ) : ratClassIndicated 0 severity = 0 := by
  simp [ratClassIndicated]
