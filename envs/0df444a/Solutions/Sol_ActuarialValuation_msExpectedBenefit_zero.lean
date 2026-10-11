-- Prove2me | solution 1 for ActuarialValuation.msExpectedBenefit_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:13:58.028649+00:00
-- url     : https://prove2.me/submissions/902152df-dcbd-4c1e-a5a6-c7c6f562b566

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msExpectedBenefit
open ActuarialValuation

theorem solution(p : Fin 3 → ℝ) : msExpectedBenefit p (fun _ => 0) = 0 := by
  simp [msExpectedBenefit]
