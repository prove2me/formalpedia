-- Prove2me | solution 1 for ActuarialValuation.irDevelopmentFactor_equal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:01:05.879658+00:00
-- url     : https://prove2.me/submissions/6de2a80b-86eb-43d0-8f8e-c43528a4b842

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irDevelopmentFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (amount : ℝ) (h : amount≠0) : irDevelopmentFactor amount amount=1 := by
  unfold irDevelopmentFactor
  exact div_self h
