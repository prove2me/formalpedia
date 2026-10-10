-- Prove2me | solution 1 for ActuarialValuation.trancheAdjustedPension_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:19.501988+00:00
-- url     : https://prove2.me/submissions/83071f5a-8ebb-4978-8785-62497dbfeb24

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_trancheAdjustedPension
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P A D : ℕ → ℝ) (i : ℕ)
  (h : P i = 0) : trancheAdjustedPension P A D i = 0 := by
  simp [trancheAdjustedPension, h]
