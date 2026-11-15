-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.transition_density_fpk_of_dynkin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:43:45.072402+00:00
-- url     : https://prove2.me/submissions/80048cc2-2dee-4cf3-a364-eb843b01c65f

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_fpk_generator_formal_adjoint_unrestricted
import Theorems.Thm_AppliedSDE_SarkkaSolin_fpk_fixed_time_weak_to_pointwise
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Topology
set_option autoImplicit false
theorem solution
    (b a : ℝ → ℝ) (p : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hb : ContDiff ℝ 2 b) (ha : ContDiff ℝ 2 a)
    (hreg : ∀ (s y t : ℝ), s < t → ContDiff ℝ 2 (p s y t))
    (htime : ∀ (s y t : ℝ), s < t →
      Continuous (fun x : ℝ => deriv (fun τ : ℝ => p s y τ x) t))
    (hpos : ∀ (s y t x : ℝ), s < t → 0 ≤ p s y t x)
    (hnorm : ∀ (s y t : ℝ), s < t →
      ∫ x : ℝ, p s y t x = 1)
    (hderiv : ∀ (s y t : ℝ), s < t →
      ∀ (φ : ℝ → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
        deriv (fun τ : ℝ => ∫ x : ℝ, φ x * p s y τ x) t =
          ∫ x : ℝ, φ x * deriv (fun τ : ℝ => p s y τ x) t)
    (hDynkin : ∀ (s y t : ℝ), s < t →
      ∀ (φ : ℝ → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
        deriv (fun τ : ℝ => ∫ x : ℝ, φ x * p s y τ x) t =
          ∫ x : ℝ,
            (b x * deriv φ x +
              a x / 2 * deriv (fun z : ℝ => deriv φ z) x) *
              p s y t x) :
    ∀ (s y t x : ℝ), s < t →
      deriv (fun τ : ℝ => p s y τ x) t =
        -deriv (fun z : ℝ => b z * p s y t z) x +
          (1 / 2 : ℝ) *
            deriv (fun z : ℝ =>
              deriv (fun w : ℝ => a w * p s y t w) z) x := by
  intro s y t x hst
  let u : ℝ -> ℝ := p s y t
  let D : ℝ -> ℝ := fun z => deriv (fun q => p s y q z) t
  have hu : ContDiff ℝ 2 u := hreg s y t hst
  have hD : Continuous D := htime s y t hst
  have hBu : ContDiff ℝ 2 (fun z => b z * u z) := hb.mul hu
  have hAu : ContDiff ℝ 2 (fun z => a z * u z) := ha.mul hu
  have hBder : Continuous (deriv (fun z => b z * u z)) :=
    hBu.continuous_deriv (by norm_num)
  have hAder2 : Continuous
      (deriv (fun z => deriv (fun w => a w * u w) z)) :=
    (hAu.deriv' : ContDiff ℝ 1 (deriv (fun w => a w * u w)))
      |>.continuous_deriv_one
  have hweak (φ : ℝ -> ℝ)
      (hφ : ContDiff ℝ 2 φ)
      (hc : HasCompactSupport φ) :
      (∫ z : ℝ, φ z *
        (D z + deriv (fun w => b w * u w) z -
          (1 / 2 : ℝ) *
            deriv (fun w => deriv (fun r => a r * u r) w) z)) = 0 := by
    have hDk := hDynkin s y t hst φ hφ hc
    have hDv := hderiv s y t hst φ hφ hc
    have hAdj := AppliedSDE.SarkkaSolin.fpk_generator_formal_adjoint_unrestricted
      b a u φ hb ha hu hφ hc
    have hEq :
        (∫ z : ℝ, φ z * D z) =
        (∫ z : ℝ, φ z *
          (-deriv (fun w => b w * u w) z +
            (1 / 2 : ℝ) * deriv (fun w => deriv (fun r => a r * u r) w) z)) := by
      calc
        _ = deriv (fun q => ∫ z : ℝ, φ z * p s y q z) t := hDv.symm
        _ = (∫ z : ℝ,
            (b z * deriv φ z +
              a z / 2 * deriv (fun w => deriv φ w) z) * u z) := hDk
        _ = _ := hAdj.symm
    have hI1 : Integrable (fun z : ℝ => φ z * D z) :=
      (hφ.continuous.mul hD).integrable_of_hasCompactSupport hc.mul_right
    have hI2 : Integrable (fun z : ℝ => φ z *
        (-deriv (fun w => b w * u w) z +
          (1 / 2 : ℝ) * deriv (fun w => deriv (fun r => a r * u r) w) z)) :=
      (hφ.continuous.mul
        (hBder.neg.add (continuous_const.mul hAder2)))
          |>.integrable_of_hasCompactSupport hc.mul_right
    have heq : (fun z : ℝ => φ z *
        (D z + deriv (fun w => b w * u w) z -
          (1 / 2 : ℝ) * deriv (fun w => deriv (fun r => a r * u r) w) z)) =
        (fun z => φ z * D z -
          φ z * (-deriv (fun w => b w * u w) z +
            (1 / 2 : ℝ) * deriv (fun w => deriv (fun r => a r * u r) w) z)) := by
      funext z
      ring
    rw [heq, integral_sub hI1 hI2, hEq, sub_self]
  have hpoint := AppliedSDE.SarkkaSolin.fpk_fixed_time_weak_to_pointwise
    b a u D hb ha hu hD hweak x
  exact hpoint
