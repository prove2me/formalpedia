-- Prove2me | solution 1 for ActuarialValuation.erSeverityTail_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:38:42.507008+00:00
-- url     : https://prove2.me/submissions/82c179d0-6d4d-4345-84c9-f929ea297029

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erSeverityTail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (beta x y : ℝ) :
    erSeverityTail beta (x+y) = erSeverityTail beta x * erSeverityTail beta y := by
  unfold erSeverityTail
  rw [show -beta*(x+y) = (-beta*x) + (-beta*y) by ring, Real.exp_add]
