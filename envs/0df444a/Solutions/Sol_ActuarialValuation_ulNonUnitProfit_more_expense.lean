-- Prove2me | solution 1 for ActuarialValuation.ulNonUnitProfit_more_expense
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:22:31.915984+00:00
-- url     : https://prove2.me/submissions/9e7d5b72-5ab4-4f2f-8881-92e6826ee69f

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulNonUnitProfit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (income expense comm death guarantee extra : ℝ) : ulNonUnitProfit income (expense+extra) comm death guarantee=ulNonUnitProfit income expense comm death guarantee-extra := by
  unfold ulNonUnitProfit
  ring
