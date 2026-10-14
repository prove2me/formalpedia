-- Prove2me | solution 1 for ActuarialValuation.ulEarned_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:14:22.056881+00:00
-- url     : https://prove2.me/submissions/ec328894-8d9c-4d4d-bf60-353f30679225

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulEarned
import Definitions.Def_actuarial_ulAfterPremium
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account prem expense flat interest : ℝ) (hbase : 0≤ulAfterPremium account prem expense flat) (hi : -1≤interest) : 0≤ulEarned account prem expense flat interest := by
  change 0 ≤ ulAfterPremium account prem expense flat * (1 + interest)
  exact mul_nonneg hbase (by linarith)
