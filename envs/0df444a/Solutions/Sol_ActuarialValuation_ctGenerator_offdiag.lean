-- Prove2me | solution 1 for ActuarialValuation.ctGenerator_offdiag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:12:22.054578+00:00
-- url     : https://prove2.me/submissions/f873489b-90ae-4d39-938c-c2bea68d738b

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctGenerator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) (h : i ≠ j) : ctGenerator r i j = r i j := by
  simp [ctGenerator, h]
