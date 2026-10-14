-- Prove2me | solution 1 for ActuarialValuation.cxBernAggregatePGF_zero_freq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:52:28.943348+00:00
-- url     : https://prove2.me/submissions/2ba47f23-2302-443c-87b4-4b74e097cb4b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxBernAggregatePGF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p0 : ℝ) (f : ℕ → ℝ) (n : ℕ) (z : ℝ) : cxBernAggregatePGF p0 0 f n z = p0 := by
  simp [cxBernAggregatePGF]
