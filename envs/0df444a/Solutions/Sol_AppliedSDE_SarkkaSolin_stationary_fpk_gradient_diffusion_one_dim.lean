-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.stationary_fpk_gradient_diffusion_one_dim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:22:35.999413+00:00
-- url     : https://prove2.me/submissions/6918d540-f153-47d5-955c-47ce62d17d7b

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_stationary_boltzmann_density_deriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology
set_option autoImplicit false
theorem solution
    (q : ℝ) (hq : 0 < q) (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hInt : Integrable (fun x : ℝ => Real.exp (-(v x / q))))
    (hZ : 0 < ∫ x : ℝ, Real.exp (-(v x / q))) :
    let Z : ℝ := ∫ x : ℝ, Real.exp (-(v x / q))
    let p : ℝ → ℝ := fun x => Z⁻¹ * Real.exp (-(v x / q))
    (∀ x : ℝ, 0 ≤ p x) ∧
    (∫ x : ℝ, p x = 1) ∧
    (∀ x : ℝ,
      deriv (fun y : ℝ => (-(1 : ℝ) / 2 * deriv v y) * p y) x =
        q / 2 * deriv (fun y : ℝ => deriv p y) x) := by
  let Z : ℝ := ∫ x : ℝ, Real.exp (-(v x / q))
  let p : ℝ -> ℝ := fun x => Z⁻¹ * Real.exp (-(v x / q))
  have hpder : ∀ x : ℝ, deriv p x = -(deriv v x / q) * p x := by
    exact AppliedSDE.SarkkaSolin.stationary_boltzmann_density_deriv
      q hq v hv Z
  have hcd : ContDiff ℝ 2 p := by
    have hg : ContDiff ℝ 2 (fun x : ℝ => -(v x / q)) :=
      (hv.div_const q).neg
    have he : ContDiff ℝ 2 (fun x : ℝ => Real.exp (-(v x / q))) :=
      hg.exp
    exact contDiff_const.mul he
  change (∀ x : ℝ, 0 <= p x) ∧
    (∫ x : ℝ, p x = 1) ∧
    (∀ x : ℝ,
      deriv (fun y : ℝ => (-(1 : ℝ) / 2 * deriv v y) * p y) x =
        q / 2 * deriv (fun y : ℝ => deriv p y) x)
  constructor
  · intro x
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hZ))
      (Real.exp_nonneg _)
  constructor
  · change (∫ x : ℝ, Z⁻¹ * Real.exp (-(v x / q))) = 1
    rw [integral_const_mul]
    change Z⁻¹ * Z = 1
    exact inv_mul_cancel₀ (ne_of_gt hZ)
  · intro x
    have hflux : (fun y : ℝ =>
        (-(1 : ℝ) / 2 * deriv v y) * p y) =
        (fun y : ℝ => (q / 2) * deriv p y) := by
      funext y
      rw [hpder y]
      field_simp [ne_of_gt hq]
    calc
      deriv (fun y : ℝ => (-(1 : ℝ) / 2 * deriv v y) * p y) x =
          deriv (fun y : ℝ => (q / 2) * deriv p y) x := by
            exact congrArg (fun f : ℝ -> ℝ => deriv f x) hflux
      _ = q / 2 * deriv (fun y : ℝ => deriv p y) x := by
        exact deriv_const_mul (q / 2) (hcd.differentiable_deriv_two x)
