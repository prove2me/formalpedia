-- Prove2me | solution 1 for ActuarialValuation.msResetReserve_zero_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:15:12.276744+00:00
-- url     : https://prove2.me/submissions/cb603128-b985-400d-9d56-aff713bc2a8c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msResetReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b : Fin 3 → ℝ) (T : ℕ → Fin 3 → Fin 3 → ℝ) (V : Fin 3 → ℕ → ℝ) (duration : ℕ) (i : Fin 3) : msResetReserve b T V 0 duration i = b i := by
  simp [msResetReserve]
