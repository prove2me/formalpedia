-- Prove2me | solution 1 for ActuarialValuation.msEndStateBenefit_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:13:16.812729+00:00
-- url     : https://prove2.me/submissions/be9f4927-6bac-40de-9cc4-c0c23094d465

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msEndStateBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (v : ℝ) : msEndStateBenefit p T (fun _ => 0) v = 0 := by
  simp [msEndStateBenefit, msExpectedBenefit]
