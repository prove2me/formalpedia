-- Prove2me | solution 1 for ActuarialValuation.msSemiReserve_same_duration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:14:58.036446+00:00
-- url     : https://prove2.me/submissions/63986532-c483-4c44-a868-97e93387ae70

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msSemiReserve

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b V : Fin 3 → ℝ) (T : ℕ → Fin 3 → Fin 3 → ℝ) (v : ℝ) (d : ℕ) (i : Fin 3) : msSemiReserve b T V v d i - msSemiReserve b T V v d i = 0 := by
  ring
