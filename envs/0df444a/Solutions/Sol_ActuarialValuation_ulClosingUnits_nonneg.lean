-- Prove2me | solution 1 for ActuarialValuation.ulClosingUnits_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:23:16.270995+00:00
-- url     : https://prove2.me/submissions/30a56f3f-0663-4a76-8c69-12457d37f21b

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulClosingUnits

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (opening bought cancelled : ℝ) (h0 : 0≤opening) (hb : 0≤bought) (hc : cancelled≤opening+bought) : 0≤ulClosingUnits opening bought cancelled := by
  unfold ulClosingUnits
  linarith
