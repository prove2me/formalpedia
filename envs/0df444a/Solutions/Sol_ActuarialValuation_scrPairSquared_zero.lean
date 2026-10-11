-- Prove2me | solution 1 for ActuarialValuation.scrPairSquared_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:35:34.88189+00:00
-- url     : https://prove2.me/submissions/6cc3a7b9-3482-4e8d-b1ff-b2a682dae2aa

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared
open ActuarialValuation

theorem solution(rho : ℝ) : scrPairSquared rho 0 0 = 0 := by
  simp [scrPairSquared, scrCovarianceTerm]
