-- Prove2me | solution 1 for ActuarialValuation.clBFUltimate_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:08:36.174217+00:00
-- url     : https://prove2.me/submissions/95ace49c-067f-4dad-9a11-e95987844686

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clBFReserve
import Definitions.Def_actuarial_clBFUltimate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c e f : ℝ) : clBFUltimate c e f = c + clBFReserve e f := by
  rfl
