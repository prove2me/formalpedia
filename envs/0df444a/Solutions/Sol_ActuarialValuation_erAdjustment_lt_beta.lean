-- Prove2me | solution 1 for ActuarialValuation.erAdjustment_lt_beta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:22:33.220417+00:00
-- url     : https://prove2.me/submissions/3754eeab-1ef9-4627-8fc7-074b78d8e416

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erAdjustment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda c beta : ℝ)
    (hl : 0<lambda) (hc : 0<c) :
    erAdjustment lambda c beta<beta := by
  unfold erAdjustment
  have hpos : 0 < lambda / c := div_pos hl hc
  linarith
