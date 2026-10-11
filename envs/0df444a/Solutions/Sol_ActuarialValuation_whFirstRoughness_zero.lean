-- Prove2me | solution 1 for ActuarialValuation.whFirstRoughness_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:51:32.932705+00:00
-- url     : https://prove2.me/submissions/2482d31e-2de9-48b2-a8e5-e3b8951e5cd1

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFirstRoughness
open ActuarialValuation

theorem solution(g : ℕ → ℝ) : whFirstRoughness g 0 = 0 := by
  simp [whFirstRoughness]
