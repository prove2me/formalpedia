-- Prove2me | solution 1 for ActuarialValuation.pgPanjerRHS_zero_k
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:36:43.846739+00:00
-- url     : https://prove2.me/submissions/5df586a4-eb3a-46c2-89ab-f29562768440

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPanjerRHS

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b : ℝ) (f g : ℕ → ℝ) : pgPanjerRHS a b f g 0=0 := by
  simp [pgPanjerRHS]
