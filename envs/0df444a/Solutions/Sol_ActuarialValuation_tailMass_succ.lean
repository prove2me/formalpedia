-- Prove2me | solution 1 for ActuarialValuation.tailMass_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:08:02.480093+00:00
-- url     : https://prove2.me/submissions/3a623240-b707-4953-8252-7e3344a46ab3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n : ℕ) :
    tailMass p (n+1) = tailMass p n + p (n+1) := by
  unfold tailMass
  exact Finset.sum_range_succ _ _
