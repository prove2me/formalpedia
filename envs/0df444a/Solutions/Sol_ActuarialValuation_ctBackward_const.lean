-- Prove2me | solution 1 for ActuarialValuation.ctBackward_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:24:26.219687+00:00
-- url     : https://prove2.me/submissions/bce820f8-4e44-44ba-9dc1-e11a54f1e3c9

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctBackward

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q : Fin 3 → Fin 3 → ℝ) (v : ℝ) (i : Fin 3) (h : (∑ j : Fin 3, q i j) = 0) : ctBackward q (fun _ => v) i = 0 := by
  unfold ctBackward
  rw [← Finset.sum_mul, h, zero_mul]
