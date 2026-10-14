-- Prove2me | solution 1 for ActuarialValuation.msMass_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:10:58.483919+00:00
-- url     : https://prove2.me/submissions/931950fa-de33-4836-95df-60735751a2ad

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p q : Fin 3 → ℝ) : msMass (fun i => p i+q i) = msMass p+msMass q := by
  unfold msMass
  simp only [Finset.sum_add_distrib]
