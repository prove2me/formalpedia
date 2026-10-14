-- Prove2me | solution 1 for ActuarialValuation.ulNonUnitProfit_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:20:26.694872+00:00
-- url     : https://prove2.me/submissions/338c4f17-a5c5-44f6-a937-6880785d2193

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulNonUnitProfit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (income expense comm death guarantee : ℝ) : ulNonUnitProfit income expense comm death guarantee+expense+comm+death+guarantee=income := by
  unfold ulNonUnitProfit
  ring
