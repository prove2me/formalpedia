-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.doob_endpoint_conditioned_bridge_kernel_normalised
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:43:50.492652+00:00
-- url     : https://prove2.me/submissions/dc7da284-b753-4e21-b7c2-0217be2ee6d6

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem solution
    (p : ℝ → ℝ → ℝ → ℝ → ℝ)
    (s x t T z : ℝ) (hst : s < t) (htT : t < T)
    (hpositive : 0 < p s x T z)
    (hIntegrable : Integrable
      (fun y : ℝ => p s x t y * p t y T z))
    (hCK : ∫ y : ℝ, p s x t y * p t y T z =
      p s x T z) :
    ∫ y : ℝ, p s x t y * p t y T z / p s x T z = 1 := by
  simp only [div_eq_mul_inv, integral_mul_const, hCK]
  exact mul_inv_cancel₀ (ne_of_gt hpositive)
