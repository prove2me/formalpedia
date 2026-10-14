-- Prove2me | solution 1 for ActuarialValuation.msSemiReserve_Markov_case
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:14:46.086001+00:00
-- url     : https://prove2.me/submissions/f5d4a462-8614-4c8f-bc09-5f1071255107

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msReserveOne
import Definitions.Def_actuarial_msSemiReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b V : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (v : ℝ) (duration : ℕ) (i : Fin 3) : msSemiReserve b (fun _ => T) V v duration i = msReserveOne b T V v i := by
  rfl
