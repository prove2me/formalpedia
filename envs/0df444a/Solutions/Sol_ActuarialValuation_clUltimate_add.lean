-- Prove2me | solution 1 for ActuarialValuation.clUltimate_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:21:34.258981+00:00
-- url     : https://prove2.me/submissions/67650465-f29b-45f2-bd67-621bd3af1eff

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clUltimate
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p q f : ℝ) : clUltimate (p+q) f = clUltimate p f + clUltimate q f := by
  unfold clUltimate
  ring
