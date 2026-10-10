-- Prove2me | solution 1 for ActuarialValuation.trancheSchemeComparatorPV_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:05:06.880486+00:00
-- url     : https://prove2.me/submissions/3d861e47-5fef-4d2e-8876-8e8997e82afa

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_trancheSchemeComparatorPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P D : ℕ → ℝ) (n : ℕ) :
  trancheSchemeComparatorPV P D (n+1) =
    trancheSchemeComparatorPV P D n + P n * D n := by
  simp [trancheSchemeComparatorPV, Finset.sum_range_succ]
