-- Prove2me | solution 1 for ActuarialValuation.msMass_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:11:09.703278+00:00
-- url     : https://prove2.me/submissions/226e8258-fd8a-4066-9bc1-a2a400b1b4e6

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msMass

import Mathlib.Algebra.BigOperators.Ring.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : Fin 3 → ℝ) (c : ℝ) : msMass (fun i => c*p i) = c*msMass p := by
  unfold msMass
  simp only [Finset.mul_sum]
