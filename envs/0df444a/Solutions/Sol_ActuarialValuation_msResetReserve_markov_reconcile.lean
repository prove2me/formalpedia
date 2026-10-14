-- Prove2me | solution 1 for ActuarialValuation.msResetReserve_markov_reconcile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:15:35.877832+00:00
-- url     : https://prove2.me/submissions/08832d3f-3fb2-4b86-8100-33a79a76baaf

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msReserveOne
import Definitions.Def_actuarial_msResetReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b V : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (v : ℝ) (duration : ℕ) (i : Fin 3) : msResetReserve b (fun _ => T) (fun j _ => V j) v duration i = msReserveOne b T V v i := by
  rfl
