-- Prove2me | solution 1 for ActuarialValuation.clBFUltimate_blend
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:10:17.43419+00:00
-- url     : https://prove2.me/submissions/42daa674-7342-446a-90e2-00c920394307

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clUltimate
import Definitions.Def_actuarial_clPaidFraction
import Definitions.Def_actuarial_clUnpaidFraction
import Definitions.Def_actuarial_clBFUltimate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c e f : ℝ) (hf : f ≠ 0) : clBFUltimate c e f = clPaidFraction f * clUltimate c f + clUnpaidFraction f * e := by
  unfold clBFUltimate clBFReserve clUltimate clPaidFraction clUnpaidFraction
  field_simp [hf] <;> ring
