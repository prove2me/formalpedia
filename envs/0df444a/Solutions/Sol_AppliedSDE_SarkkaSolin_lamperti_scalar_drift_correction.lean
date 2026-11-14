-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.lamperti_scalar_drift_correction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:30:25.809168+00:00
-- url     : https://prove2.me/submissions/cbcfa4fa-be51-410f-998b-83500187e613

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory
open scoped BigOperators Topology

theorem solution
    (b σ g : ℝ → ℝ)
    (hσ : ContDiff ℝ 2 σ) (hg : ContDiff ℝ 2 g)
    (hσpos : ∀ x : ℝ, 0 < σ x)
    (hgderiv : ∀ x : ℝ, deriv g x = (σ x)⁻¹) :
    ∀ x : ℝ,
      (deriv g x) * σ x = 1 ∧
      (deriv g x) * b x +
        σ x ^ 2 / 2 * deriv (fun y : ℝ => deriv g y) x =
          b x / σ x - (1 / 2 : ℝ) * deriv σ x := by
  intro x
  have hne : σ x ≠ 0 := ne_of_gt (hσpos x)
  have hdiff : DifferentiableAt ℝ σ x :=
    (hσ.differentiable (by norm_num)) x
  have hderiv :
      deriv (fun y : ℝ => deriv g y) x = -deriv σ x / σ x ^ 2 := by
    have heq : (fun y : ℝ => deriv g y) = (fun y : ℝ => (σ y)⁻¹) := by
      funext y
      exact hgderiv y
    rw [heq]
    exact deriv_fun_inv'' hdiff hne
  constructor
  · rw [hgderiv x]
    exact inv_mul_cancel₀ hne
  · rw [hgderiv x, hderiv]
    field_simp [hne]
    ring
