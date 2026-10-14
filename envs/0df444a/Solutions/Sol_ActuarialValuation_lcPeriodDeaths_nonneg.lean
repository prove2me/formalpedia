-- Prove2me | solution 1 for ActuarialValuation.lcPeriodDeaths_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:35:51.388559+00:00
-- url     : https://prove2.me/submissions/d9606441-a056-465f-a86a-e524443819cd

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcPeriodDeaths

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lives q : ℝ)
    (hl : 0 ≤ lives) (hq : 0 ≤ q) :
    0 ≤ lcPeriodDeaths lives q := by
  unfold lcPeriodDeaths
  exact mul_nonneg hl hq
