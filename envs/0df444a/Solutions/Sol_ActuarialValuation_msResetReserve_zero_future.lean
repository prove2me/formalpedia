-- Prove2me | solution 1 for ActuarialValuation.msResetReserve_zero_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:15:23.706678+00:00
-- url     : https://prove2.me/submissions/d191ec0c-5aa7-42e9-af51-0b0297602456

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msResetReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b : Fin 3 → ℝ) (T : ℕ → Fin 3 → Fin 3 → ℝ) (duration : ℕ) (v : ℝ) (i : Fin 3) : msResetReserve b T (fun _ _ => 0) v duration i = b i := by
  simp [msResetReserve]
