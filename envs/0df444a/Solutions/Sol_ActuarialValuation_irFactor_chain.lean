-- Prove2me | solution 1 for ActuarialValuation.irFactor_chain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:02:46.969121+00:00
-- url     : https://prove2.me/submissions/8131d18c-a3d1-4ac9-abc1-c55eab6fe9cb

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b c : ℝ) (ha : a≠0) (hb : b≠0) : irFactor c b*irFactor b a=irFactor c a := by
  unfold irFactor
  field_simp [ha, hb]
