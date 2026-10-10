-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonSeverityPower_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:08:57.725634+00:00
-- url     : https://prove2.me/submissions/3880ef71-a14a-46b4-963f-7da42c33de58

import Mathlib
import Definitions.Def_actuarial_compoundPoissonSeverityPower
import Definitions.Def_actuarial_compoundPoissonConvolution

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (m s : ℕ) :
  compoundPoissonSeverityPower f (m + 1) s =
    compoundPoissonConvolution f (compoundPoissonSeverityPower f m) s := by
  rfl
