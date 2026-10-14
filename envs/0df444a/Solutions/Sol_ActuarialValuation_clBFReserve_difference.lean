-- Prove2me | solution 1 for ActuarialValuation.clBFReserve_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:05:22.745066+00:00
-- url     : https://prove2.me/submissions/77ea62b8-f3ab-4528-ad8f-f9f451a16a59

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clUltimate
import Definitions.Def_actuarial_clUnpaidFraction
import Definitions.Def_actuarial_clBFUltimate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c e f : ℝ) (hf : f ≠ 0) : clBFUltimate c e f - clUltimate c f = clUnpaidFraction f * (e - clUltimate c f) := by
  unfold clBFUltimate clBFReserve clUltimate clUnpaidFraction clPaidFraction
  field_simp [hf] <;> ring
