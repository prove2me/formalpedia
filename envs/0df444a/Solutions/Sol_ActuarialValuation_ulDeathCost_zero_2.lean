-- Prove2me | solution 2 for ActuarialValuation.ulDeathCost_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:42.478561+00:00
-- url     : https://prove2.me/submissions/dc367161-b80f-4682-ae6f-f36f7a0b2dbb

import Mathlib
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulDeathCost

open ActuarialValuation

theorem solution (fund guarantee : ℝ) : ulDeathCost 0 fund guarantee=0 := by simp [ulDeathCost]

