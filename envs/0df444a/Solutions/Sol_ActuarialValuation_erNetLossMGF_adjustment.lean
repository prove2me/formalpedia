-- Prove2me | solution 1 for ActuarialValuation.erNetLossMGF_adjustment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:24:47.639504+00:00
-- url     : https://prove2.me/submissions/65cb7f13-7b49-4d47-978d-826c596e50e3

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erAdjustment
import Definitions.Def_actuarial_erNetLossMGF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda premium beta t : ℝ) (hl : 0<lambda) (hc : 0<premium) :
    erNetLossMGF lambda premium beta (erAdjustment lambda premium beta) t = 1 := by
  unfold erNetLossMGF erLundbergGap erExponentialMGF erAdjustment
  field_simp [hc.ne', hl.ne']
  <;> ring_nf
  <;> simp [Real.exp_zero]
