-- Prove2me | solution 1 for ActuarialValuation.pen9AccumFactor_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:56:35.487111+00:00
-- url     : https://prove2.me/submissions/53957e00-6c25-4cf5-a1c7-983bd8204518

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9AccumFactor
open ActuarialValuation

theorem solution(s : ℕ → ℝ) (j : ℝ) : pen9AccumFactor s j 1 = s 0 := by
  simp [pen9AccumFactor]
