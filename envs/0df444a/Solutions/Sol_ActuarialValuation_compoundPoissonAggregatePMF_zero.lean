-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonAggregatePMF_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:12:33.889867+00:00
-- url     : https://prove2.me/submissions/71e53573-eff6-4f86-ac8f-0b9730ca2a38

import Mathlib
import Definitions.Def_actuarial_compoundPoissonAggregatePMF
import Definitions.Def_actuarial_compoundPoissonCountWeight
import Definitions.Def_actuarial_compoundPoissonSeverityPower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rate : ℝ) (f : ℕ → ℝ)
  (hzero : f 0 = 0) :
  compoundPoissonAggregatePMF rate f 0 = Real.exp (-rate) := by
  simp [compoundPoissonAggregatePMF, compoundPoissonCountWeight,
    compoundPoissonSeverityPower]
