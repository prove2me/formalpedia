-- Prove2me | solution 1 for ActuarialValuation.ulAllocated_le_gross
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:07:11.514545+00:00
-- url     : https://prove2.me/submissions/bfa6c8bb-ad86-4257-be6c-6df169abffb5

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAllocatedPremium
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (prem expense : ℝ) (hp : 0≤prem) (he : 0≤expense) : ulAllocatedPremium prem expense ≤ prem := by
  change prem * (1 - expense) ≤ prem
  nlinarith [mul_nonneg hp he]
