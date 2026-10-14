-- Prove2me | solution 1 for ActuarialValuation.mackProjection_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:35:07.770882+00:00
-- url     : https://prove2.me/submissions/98ce121d-a77d-474a-8a10-fb5f6030c550

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackProjection

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c d f : ℝ) : mackProjection (c+d) f = mackProjection c f + mackProjection d f := by
  unfold mackProjection
  ring
