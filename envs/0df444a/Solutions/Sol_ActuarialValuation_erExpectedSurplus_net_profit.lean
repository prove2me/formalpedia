-- Prove2me | solution 1 for ActuarialValuation.erExpectedSurplus_net_profit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:32:05.019656+00:00
-- url     : https://prove2.me/submissions/1526650c-dc68-44a4-a3c8-be1d637dc99a

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c lambda beta t : ℝ) (hc : 0<c) (hb : 0<beta)
    (hn : lambda < c * beta) (ht : 0 ≤ t) :
    u ≤ erExpectedSurplus u c lambda beta t := by
  unfold erExpectedSurplus erExpectedPremium erExpectedAggregate
  have hratio : lambda / beta < c :=
    (div_lt_iff₀ hb).2 (by nlinarith [hn])
  have hrate : 0 ≤ c - lambda / beta := by linarith
  have hprod : 0 ≤ t * (c - lambda / beta) := mul_nonneg ht hrate
  have hsurplus :
      u + c * t - lambda * t / beta = u + t * (c - lambda / beta) := by
    field_simp [ne_of_gt hb]
    ring
  rw [hsurplus]
  exact le_add_of_nonneg_right hprod
