-- Prove2me | solution 1 for ActuarialValuation.scrCovarianceTerm_zero_first
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:28:30.024986+00:00
-- url     : https://prove2.me/submissions/1e457544-52f6-497f-8f73-a4df65023f16

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrCovarianceTerm
open ActuarialValuation

theorem solution(rho b : ℝ) : scrCovarianceTerm rho 0 b = 0 := by
  simp [scrCovarianceTerm]
