-- Prove2me | solution 1 for ActuarialValuation.msTransitionBenefit_zero_payment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:13:02.38903+00:00
-- url     : https://prove2.me/submissions/4e7bee81-da9c-4c2c-81e3-2ebc33e784ea

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msTransitionBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (v : ℝ) : msTransitionBenefit p T (fun _ _ => 0) v = 0 := by
  simp [msTransitionBenefit]
