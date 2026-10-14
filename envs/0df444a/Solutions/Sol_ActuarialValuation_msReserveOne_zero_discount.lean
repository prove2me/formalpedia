-- Prove2me | solution 1 for ActuarialValuation.msReserveOne_zero_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:13:29.923549+00:00
-- url     : https://prove2.me/submissions/b1688363-bd0c-459d-93da-03e6f8f2c6cf

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msReserveOne

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b V : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : msReserveOne b T V 0 i = b i := by
  simp [msReserveOne]
