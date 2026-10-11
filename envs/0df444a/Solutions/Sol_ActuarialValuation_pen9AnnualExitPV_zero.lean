-- Prove2me | solution 1 for ActuarialValuation.pen9AnnualExitPV_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:45:42.17256+00:00
-- url     : https://prove2.me/submissions/b5da7b25-fbdf-4459-844d-f732835fe032

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9AnnualExitPV
open ActuarialValuation

theorem solution(p v b : ℕ → ℝ) : pen9AnnualExitPV p v b 0 = 0 := by
  simp [pen9AnnualExitPV]
