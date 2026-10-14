-- Prove2me | solution 1 for ActuarialValuation.clUltimate_reserve_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:20:02.435742+00:00
-- url     : https://prove2.me/submissions/fb2384e2-7453-4a9a-a7b4-6f0e6d158534

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clUltimate
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_clReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p f : ℝ) : p + clReserve p f = clUltimate p f := by
  unfold clReserve
  ring
