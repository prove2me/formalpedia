-- Prove2me | solution 1 for ActuarialValuation.erLundbergGap_adjustment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:23:28.003298+00:00
-- url     : https://prove2.me/submissions/a8a5f7cf-4919-4388-a7df-c4f0d572dbbc

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erAdjustment
import Definitions.Def_actuarial_erLundbergGap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda premium beta : ℝ) (hl : 0<lambda) (hc : 0<premium) :
    erLundbergGap lambda premium beta (erAdjustment lambda premium beta) = 0 := by
  unfold erLundbergGap erExponentialMGF erAdjustment
  field_simp [hc.ne', hl.ne']
  <;> ring
