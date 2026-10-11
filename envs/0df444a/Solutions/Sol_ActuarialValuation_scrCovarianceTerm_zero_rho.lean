-- Prove2me | solution 1 for ActuarialValuation.scrCovarianceTerm_zero_rho
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:03:28.525331+00:00
-- url     : https://prove2.me/submissions/e5fbad50-6494-4043-ad0a-2267971f8476

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrCovarianceTerm
open ActuarialValuation

theorem solution(a b : ℝ) : scrCovarianceTerm 0 a b = 0 := by
  simp [scrCovarianceTerm]
