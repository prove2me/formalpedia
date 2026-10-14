-- Prove2me | solution 1 for ActuarialValuation.ctBackward_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:19:12.294512+00:00
-- url     : https://prove2.me/submissions/2c576f94-4613-4298-b551-92c5faab0e35

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctBackward

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q : Fin 3 → Fin 3 → ℝ) (v w : Fin 3 → ℝ) (i : Fin 3) : ctBackward q (fun j => v j+w j) i = ctBackward q v i+ctBackward q w i := by
  unfold ctBackward
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring
