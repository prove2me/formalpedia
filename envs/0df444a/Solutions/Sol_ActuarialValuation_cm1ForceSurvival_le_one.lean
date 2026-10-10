-- Prove2me | solution 1 for ActuarialValuation.cm1ForceSurvival_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:58:20.74829+00:00
-- url     : https://prove2.me/submissions/567d93d0-db20-4113-bc9d-5daaaaecc020

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_actuarial_cm1ForceSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (μ t : ℝ) (hμ : 0 ≤ μ) (ht : 0 ≤ t) :
    cm1ForceSurvival μ t ≤ 1 := by
  have hneg : -μ * t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hμ) ht
  have hexp : Real.exp (-μ * t) ≤ Real.exp (0 : ℝ) :=
    (Real.exp_le_exp).mpr hneg
  simpa only [cm1ForceSurvival, Real.exp_zero] using hexp
