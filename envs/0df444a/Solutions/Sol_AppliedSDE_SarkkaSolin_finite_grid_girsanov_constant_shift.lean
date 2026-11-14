-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.finite_grid_girsanov_constant_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:36:10.263819+00:00
-- url     : https://prove2.me/submissions/444508ed-4349-4770-a2d1-661e40de00ad

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped BigOperators

/-- The finite-grid Gaussian likelihood tilt telescopes in the exponent to
the total path increment and accumulated time. -/
theorem solution
    (n : ℕ) (θ : ℝ) (dx dt : Fin n → ℝ)
    (hdt : ∀ k : Fin n, 0 < dt k) :
    (∏ k : Fin n, Real.exp (θ * dx k - θ ^ 2 / 2 * dt k)) =
      Real.exp (θ * (∑ k : Fin n, dx k) -
        θ ^ 2 / 2 * (∑ k : Fin n, dt k)) := by
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]
