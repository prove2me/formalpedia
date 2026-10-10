-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonSeverityPower_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:08:54.765148+00:00
-- url     : https://prove2.me/submissions/6823d298-b9ad-4673-b565-974a2a9af920

import Mathlib
import Definitions.Def_actuarial_compoundPoissonSeverityPower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (s : ℕ) :
  compoundPoissonSeverityPower f 0 s = (if s = 0 then 1 else 0) := by
  rfl
