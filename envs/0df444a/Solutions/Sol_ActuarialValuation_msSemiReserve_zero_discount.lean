-- Prove2me | solution 1 for ActuarialValuation.msSemiReserve_zero_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:14:35.185985+00:00
-- url     : https://prove2.me/submissions/71fdfff9-d390-424d-b349-df2e35348b1b

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msSemiReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b V : Fin 3 → ℝ) (T : ℕ → Fin 3 → Fin 3 → ℝ) (duration : ℕ) (i : Fin 3) : msSemiReserve b T V 0 duration i = b i := by
  simp [msSemiReserve]
