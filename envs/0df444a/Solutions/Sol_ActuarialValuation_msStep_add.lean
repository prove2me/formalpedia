-- Prove2me | solution 1 for ActuarialValuation.msStep_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:11:48.963087+00:00
-- url     : https://prove2.me/submissions/3cfc1646-a66d-46a5-996b-ca671d57d9a8

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msStep

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p q : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (j : Fin 3) : msStep (fun i => p i+q i) T j = msStep p T j+msStep q T j := by
  unfold msStep
  simp only [add_mul, Finset.sum_add_distrib]
