-- Prove2me | solution 1 for ActuarialValuation.irProject_two_steps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:03:14.244138+00:00
-- url     : https://prove2.me/submissions/9abec8f6-648b-4c7f-9bb1-3e0017fbfd11

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irProject

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (paid f g : ℝ) : irProject (irProject paid f) g=irProject paid (f*g) := by
  unfold irProject
  ring
