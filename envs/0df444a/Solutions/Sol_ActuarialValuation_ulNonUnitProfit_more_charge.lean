-- Prove2me | solution 1 for ActuarialValuation.ulNonUnitProfit_more_charge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:23:49.864334+00:00
-- url     : https://prove2.me/submissions/dea561db-f290-4ee5-89b3-4587164db63c

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulNonUnitProfit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (income expense comm death guarantee extra : ℝ) : ulNonUnitProfit (income+extra) expense comm death guarantee=ulNonUnitProfit income expense comm death guarantee+extra := by
  unfold ulNonUnitProfit
  ring
