-- Prove2me | solution 1 for ActuarialValuation.scrDiversificationSquared_zero_first
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:39:02.373449+00:00
-- url     : https://prove2.me/submissions/c9b01c3e-c7f5-4c48-b013-8ee4d6ba75d4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrDiversificationSquared

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rho b : ℝ) : scrDiversificationSquared rho 0 b = 0 := by
  simp [scrDiversificationSquared, scrSumSquared,
    scrPairSquared, scrCovarianceTerm]
