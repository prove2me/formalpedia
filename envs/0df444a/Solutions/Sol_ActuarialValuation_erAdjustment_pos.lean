-- Prove2me | solution 1 for ActuarialValuation.erAdjustment_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:24:48.524006+00:00
-- url     : https://prove2.me/submissions/d4886dc3-e937-4ba5-8cdd-f17671820e9e

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erAdjustment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda c beta : ℝ) (hc : 0<c) (hb : 0<beta)
    (hn : lambda<c*beta) : 0<erAdjustment lambda c beta := by
  unfold erAdjustment
  apply sub_pos.mpr
  apply (div_lt_iff₀ hc).2
  nlinarith [hn]
