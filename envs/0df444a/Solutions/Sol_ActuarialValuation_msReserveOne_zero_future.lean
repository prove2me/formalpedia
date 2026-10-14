-- Prove2me | solution 1 for ActuarialValuation.msReserveOne_zero_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:13:44.681983+00:00
-- url     : https://prove2.me/submissions/a4c07416-4888-4ddd-aac2-3729909ea9f5

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msReserveOne

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (v : ℝ) (i : Fin 3) : msReserveOne b T (fun _ => 0) v i = b i := by
  simp [msReserveOne]
