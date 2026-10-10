-- Prove2me | solution 1 for ActuarialValuation.finiteExponentialMoment_zero_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:25:04.765199+00:00
-- url     : https://prove2.me/submissions/c60f5a85-33fc-4514-bb6a-23e6adae9836

import Mathlib
import Definitions.Def_actuarial_finiteExponentialMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (gamma : ℝ)
    (hsum : (∑ ω : Ω, w ω) = 1) :
    finiteExponentialMoment w (fun _ => 0) gamma = 1 := by
  simpa [finiteExponentialMoment] using hsum
