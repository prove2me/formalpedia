-- Prove2me | solution 1 for ActuarialValuation.mackVarianceNumerator_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:35:57.877974+00:00
-- url     : https://prove2.me/submissions/22536ea2-5e46-4198-9e46-e2c7a9683a93

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackScaledResidual
import Definitions.Def_actuarial_mackVarianceNumerator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b e : ℕ → ℝ) (m : ℕ) : mackVarianceNumerator a b e (m+1) = mackVarianceNumerator a b e m + mackScaledResidual (a m) (b m) (e m) := by
  simp [mackVarianceNumerator, Finset.sum_range_succ]
