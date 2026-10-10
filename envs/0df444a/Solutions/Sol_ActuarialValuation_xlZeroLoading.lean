-- Prove2me | solution 1 for ActuarialValuation.xlZeroLoading
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:19:57.244471+00:00
-- url     : https://prove2.me/submissions/48cdc1d8-4447-40d9-ba28-d7281c57e97f

import Mathlib
import Definitions.Def_actuarial_xlExpectedLoss
import Definitions.Def_actuarial_xlExpectedValuePremiumCost
import Theorems.Thm_ActuarialValuation_xlExpectedSplit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (a : ℝ)
  :
  xlExpectedValuePremiumCost w z a 0 = xlExpectedLoss w z := by
  simpa [xlExpectedValuePremiumCost] using xlExpectedSplit w z a
