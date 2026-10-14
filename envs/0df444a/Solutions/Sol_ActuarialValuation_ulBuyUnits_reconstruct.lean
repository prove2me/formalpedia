-- Prove2me | solution 1 for ActuarialValuation.ulBuyUnits_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:22:54.959442+00:00
-- url     : https://prove2.me/submissions/2cf0b9e7-b9fd-417c-9499-ec2c6596480d

import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulBuyUnits

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (amount offer : ℝ) (h : offer≠0) : ulBuyUnits amount offer*offer=amount := by
  unfold ulBuyUnits
  field_simp [h]
