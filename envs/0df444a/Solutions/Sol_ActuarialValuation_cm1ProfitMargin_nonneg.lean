-- Prove2me | solution 1 for ActuarialValuation.cm1ProfitMargin_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:17.950363+00:00
-- url     : https://prove2.me/submissions/0c93a021-77d5-48c2-ad09-4321520b01b0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ProfitMargin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P V : ℝ) (hp : 0 ≤ P) (hV : 0 < V) : 0 ≤ cm1ProfitMargin P V := by
  unfold cm1ProfitMargin
  exact div_nonneg hp (le_of_lt hV)
