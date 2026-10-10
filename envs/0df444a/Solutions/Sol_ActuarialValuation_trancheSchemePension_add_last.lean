-- Prove2me | solution 1 for ActuarialValuation.trancheSchemePension_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:59.977765+00:00
-- url     : https://prove2.me/submissions/e72a0176-4edf-4d23-82aa-1a7714642f24

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_trancheAdjustedPension
import Definitions.Def_actuarial_trancheSchemePension
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P A D : ℕ → ℝ) (n : ℕ) :
  trancheSchemePension P A D (n+1) =
    trancheSchemePension P A D n + trancheAdjustedPension P A D n := by
  simp [trancheSchemePension, Finset.sum_range_succ]
