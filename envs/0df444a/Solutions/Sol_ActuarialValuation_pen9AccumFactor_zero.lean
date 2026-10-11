-- Prove2me | solution 1 for ActuarialValuation.pen9AccumFactor_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:47:50.107324+00:00
-- url     : https://prove2.me/submissions/97f89234-9445-4e91-9a54-ec59e969866a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9AccumFactor
open ActuarialValuation

theorem solution(s : ℕ → ℝ) (j : ℝ) : pen9AccumFactor s j 0 = 0 := by
  simp [pen9AccumFactor]
