-- Prove2me | solution 1 for ActuarialValuation.lcExpectedDeathCost_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:34:57.858091+00:00
-- url     : https://prove2.me/submissions/c9d67602-2880-42a5-a770-b9ff42b14db1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcExpectedDeathCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lives q b : ℝ)
    (hl : 0 ≤ lives) (hq : 0 ≤ q) (hb : 0 ≤ b) :
    0 ≤ lcExpectedDeathCost lives q b := by
  unfold lcExpectedDeathCost
  exact mul_nonneg (mul_nonneg hl hq) hb
