-- Prove2me | solution 1 for ActuarialValuation.pen9ExitMass_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:33:44.08007+00:00
-- url     : https://prove2.me/submissions/c9c3b128-4d42-4c6c-800f-5dcb267f8f85

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9ExitMass
open ActuarialValuation

theorem solution(w d i r : ℝ) : pen9ExitMass w d i r = w+d+i+r := by
  simp [pen9ExitMass]
