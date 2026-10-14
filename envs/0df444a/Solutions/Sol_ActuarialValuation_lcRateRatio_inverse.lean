-- Prove2me | solution 1 for ActuarialValuation.lcRateRatio_inverse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:30:41.93893+00:00
-- url     : https://prove2.me/submissions/5f98a422-f4b8-41bc-9edf-f6a9b02454e4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_lcRateRatio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b k1 k2 : ℝ) :
    lcRateRatio b k1 k2 * lcRateRatio b k2 k1 = 1 := by
  simp only [lcRateRatio, lcLogChange]
  rw [← Real.exp_add]
  have hzero : b * (k2 - k1) + b * (k1 - k2) = 0 := by ring
  rw [hzero, Real.exp_zero]
