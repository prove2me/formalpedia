-- Prove2me | solution 1 for ActuarialValuation.tailCDF_zero_range
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:00:42.559556+00:00
-- url     : https://prove2.me/submissions/e869f16c-fb25-48bf-a21e-14ba1cd884ac

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailCDF
open ActuarialValuation

theorem solution(p : ℕ → ℝ) (t : ℕ) : tailCDF p 0 t = p 0 := by
  simp [tailCDF]
