-- Prove2me | solution 1 for ActuarialValuation.pen9UnitNormalCost_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:23:21.920404+00:00
-- url     : https://prove2.me/submissions/8a423fab-a197-4467-a9fb-b83d97d8b863

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9PUCNormalCost
import Definitions.Def_actuarial_pen9TUCNormalCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a current projected f : ℝ) : pen9PUCNormalCost a projected f - pen9TUCNormalCost a current f = a*(projected-current)*f := by
  unfold pen9PUCNormalCost pen9TUCNormalCost
  ring
