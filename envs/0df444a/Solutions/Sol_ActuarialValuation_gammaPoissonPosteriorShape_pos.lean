-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonPosteriorShape_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:40:14.745451+00:00
-- url     : https://prove2.me/submissions/b7266419-f29e-4d28-8222-c76d7699c1ab

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorShape

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a : ℝ) (c : ℕ)
  (ha : 0 < a) : 0 < gammaPoissonPosteriorShape a c := by
  change 0 < a + (c : ℝ)
  exact add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)
