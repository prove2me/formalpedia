-- Prove2me | solution 1 for ActuarialValuation.irProject_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:02:50.674676+00:00
-- url     : https://prove2.me/submissions/64352864-1408-4749-97e5-635f1268d09c

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irProject

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b link : ℝ) : irProject (a+b) link=irProject a link+irProject b link := by
  unfold irProject
  ring
