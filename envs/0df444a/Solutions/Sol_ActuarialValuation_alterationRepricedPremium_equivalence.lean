-- Prove2me | solution 1 for ActuarialValuation.alterationRepricedPremium_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:05.39652+00:00
-- url     : https://prove2.me/submissions/61d22b9e-64fc-40e0-9e53-2ca7e79589d1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationRepricedPremium

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B A : ℝ) (h : A ≠ 0) : alterationRepricedPremium B A * A = B := by
  unfold alterationRepricedPremium
  field_simp [h] <;> ring
