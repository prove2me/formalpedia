-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.doob_h_transform_generator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:31:11.910178+00:00
-- url     : https://prove2.me/submissions/d7d15f90-a51e-482a-b339-a7a9ec09fdd0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Topology
set_option autoImplicit false
theorem solution
    (b a h φ : ℝ → ℝ)
    (hb : ContDiff ℝ 2 b)
    (ha : ContDiff ℝ 2 a)
    (hh : ContDiff ℝ 2 h)
    (hφ : ContDiff ℝ 2 φ)
    (hpos : ∀ x : ℝ, 0 < h x) :
    ∀ x : ℝ,
      let A : (ℝ → ℝ) → ℝ := fun g =>
        b x * deriv g x +
          a x / 2 * deriv (fun y : ℝ => deriv g y) x
      (A (fun y : ℝ => h y * φ y) - φ x * A h) / h x =
        (b x + a x * (deriv h x / h x)) * deriv φ x +
          a x / 2 * deriv (fun y : ℝ => deriv φ y) x := by
  have hhd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hpd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hhd2 : Differentiable ℝ (deriv h) := hh.differentiable_deriv_two
  have hpd2 : Differentiable ℝ (deriv φ) := hφ.differentiable_deriv_two
  have hprod (y : ℝ) :
      deriv (fun z : ℝ => h z * φ z) y =
        deriv h y * φ y + h y * deriv φ y :=
    deriv_fun_mul (hhd y) (hpd y)
  have hprod2 (x : ℝ) :
      deriv (fun y : ℝ => deriv (fun z : ℝ => h z * φ z) y) x =
        deriv (fun y : ℝ => deriv h y) x * φ x +
        2 * deriv h x * deriv φ x +
        h x * deriv (fun y : ℝ => deriv φ y) x := by
    calc
      deriv (fun y : ℝ => deriv (fun z : ℝ => h z * φ z) y) x =
          deriv (fun y : ℝ => deriv h y * φ y + h y * deriv φ y) x := by
            exact congrArg (fun f : ℝ -> ℝ => deriv f x) (funext hprod)
      _ = deriv (fun y : ℝ => deriv h y * φ y) x +
          deriv (fun y : ℝ => h y * deriv φ y) x :=
            deriv_fun_add ((hhd2 x).mul (hpd x)) ((hhd x).mul (hpd2 x))
      _ = deriv (fun y : ℝ => deriv h y) x * φ x +
          2 * deriv h x * deriv φ x +
          h x * deriv (fun y : ℝ => deriv φ y) x := by
            rw [deriv_fun_mul (hhd2 x) (hpd x),
              deriv_fun_mul (hhd x) (hpd2 x)]
            ring
  intro x
  have hne : h x ≠ 0 := ne_of_gt (hpos x)
  dsimp only
  rw [hprod x, hprod2 x]
  field_simp [hne]
  ring
