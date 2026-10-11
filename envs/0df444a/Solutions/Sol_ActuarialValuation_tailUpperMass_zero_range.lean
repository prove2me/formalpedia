-- Prove2me | solution 1 for ActuarialValuation.tailUpperMass_zero_range
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:17:45.270663+00:00
-- url     : https://prove2.me/submissions/009e157e-2dcf-4a97-95b2-6931aa8acb79

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailUpperMass
open ActuarialValuation

theorem solution(p : ℕ → ℝ) : tailUpperMass p 0 0 = 0 := by
  simp [tailUpperMass]
