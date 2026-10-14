-- Prove2me | solution 1 for ActuarialValuation.pen9RequiredDCRate_funds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:19:29.374206+00:00
-- url     : https://prove2.me/submissions/3d57c390-fabe-4463-98a2-2ae0c6f02552

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9RequiredDCRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (capital factor : ℝ) (hf : factor ≠ 0) : pen9RequiredDCRate capital factor * factor = capital := by
  unfold pen9RequiredDCRate
  field_simp [hf] <;> ring
