-- Prove2me | solution 1 for ActuarialValuation.msReserveOne_cost
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:13:57.392596+00:00
-- url     : https://prove2.me/submissions/d1f115d2-0db6-4beb-be2e-ee00041933c1

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msReserveOne
import Definitions.Def_actuarial_msTransitionCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b V : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (v : ℝ) (i : Fin 3) : msReserveOne b T V v i = b i+msTransitionCost T V v i := by
  rfl
