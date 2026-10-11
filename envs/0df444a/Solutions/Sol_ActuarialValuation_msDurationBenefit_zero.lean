-- Prove2me | solution 1 for ActuarialValuation.msDurationBenefit_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:30:25.543521+00:00
-- url     : https://prove2.me/submissions/b8527c75-df29-4a67-9693-68f60cff28ae

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msDurationBenefit
open ActuarialValuation

theorem solution(b : ℕ → ℝ) : msDurationBenefit b 0 = b 0 := by
  simp [msDurationBenefit]
