-- Prove2me | solution 1 for ActuarialValuation.msTransitionBenefit_zero_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:12:50.675114+00:00
-- url     : https://prove2.me/submissions/4226dd06-f875-4651-b633-2e72692d344e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msTransitionBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) : msTransitionBenefit p T B 0 = 0 := by
  simp [msTransitionBenefit]
