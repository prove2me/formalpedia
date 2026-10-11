-- Prove2me | solution 1 for ActuarialValuation.scrPairSquared_first_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:50:19.237355+00:00
-- url     : https://prove2.me/submissions/61451873-fb1a-40cb-8767-22be5d846093

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared
open ActuarialValuation

theorem solution(rho b : ℝ) : scrPairSquared rho 0 b = b^2 := by
  simp [scrPairSquared, scrCovarianceTerm]
