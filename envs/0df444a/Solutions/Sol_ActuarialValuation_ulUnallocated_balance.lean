-- Prove2me | solution 1 for ActuarialValuation.ulUnallocated_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:23:05.468498+00:00
-- url     : https://prove2.me/submissions/74b17fee-fff6-43c4-b6f6-d3b25ccb732b

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulPremiumAlloc
import Definitions.Def_actuarial_ulUnallocated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (premium rate : ℝ) : ulUnallocated premium rate+ulPremiumAlloc premium rate=premium := by
  unfold ulUnallocated
  ring
