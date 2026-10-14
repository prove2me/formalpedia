-- Prove2me | solution 1 for ActuarialValuation.msTransitionCost_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:14:10.38028+00:00
-- url     : https://prove2.me/submissions/f2cc405a-7b56-4dd9-9d1b-35e126baa254

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msTransitionCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (T : Fin 3 → Fin 3 → ℝ) (v : ℝ) (i : Fin 3) : msTransitionCost T (fun _ => 0) v i = 0 := by
  simp [msTransitionCost]
