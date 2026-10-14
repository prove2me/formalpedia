-- Prove2me | solution 1 for ActuarialValuation.erRuinCandidate_capital_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:41:00.131199+00:00
-- url     : https://prove2.me/submissions/15b24c69-579b-49df-a2a2-59baa3a9831e

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erAdjustment
import Definitions.Def_actuarial_erRuinCandidate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda c beta u v : ℝ) :
    erRuinCandidate lambda c beta (u+v) =
      erRuinCandidate lambda c beta u * Real.exp (-(erAdjustment lambda c beta)*v) := by
  unfold erRuinCandidate
  have hexp : -(erAdjustment lambda c beta) * (u + v) =
      (-(erAdjustment lambda c beta) * u) + (-(erAdjustment lambda c beta) * v) := by
    ring
  rw [hexp, Real.exp_add]
  ring
