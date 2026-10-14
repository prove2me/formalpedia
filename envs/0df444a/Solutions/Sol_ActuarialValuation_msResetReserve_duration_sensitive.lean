-- Prove2me | solution 1 for ActuarialValuation.msResetReserve_duration_sensitive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:16:39.418276+00:00
-- url     : https://prove2.me/submissions/ca2e90cd-d843-4b64-9161-4afa0cbae4c4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msDurationNext
import Definitions.Def_actuarial_msResetReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b : Fin 3 → ℝ) (T : ℕ → Fin 3 → Fin 3 → ℝ) (V : Fin 3 → ℕ → ℝ) (v : ℝ) (duration : ℕ) (i : Fin 3) : msResetReserve b T V v duration i = b i+v*(∑ j : Fin 3, T duration i j*V j (msDurationNext i j duration)) := by
  rfl
