-- Prove2me | solution 1 for ActuarialValuation.svTail_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:56:51.940981+00:00
-- url     : https://prove2.me/submissions/e98743aa-54c3-4bbd-88f7-3bb518ee80c7

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svFiniteTailMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n k : ℕ) (hp : ∀ j ∈ Finset.Icc (k+1) n, 0 ≤ p j) : 0 ≤ svFiniteTailMass p n k := by
  unfold svFiniteTailMass
  apply Finset.sum_nonneg
  intro j hj
  exact hp j hj
