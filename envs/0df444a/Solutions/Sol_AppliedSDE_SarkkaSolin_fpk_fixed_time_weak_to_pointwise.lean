-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.fpk_fixed_time_weak_to_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T11:22:15.863201+00:00
-- url     : https://prove2.me/submissions/94cea8a5-b7e9-4743-9add-a1986e860016

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_continuous_zero_of_compact_smooth_tests
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Topology
set_option autoImplicit false
theorem solution
    (b a u D : ℝ -> ℝ)
    (hb : ContDiff ℝ 2 b) (ha : ContDiff ℝ 2 a)
    (hu : ContDiff ℝ 2 u) (hD : Continuous D)
    (hweak : ∀ (φ : ℝ -> ℝ),
      ContDiff ℝ 2 φ -> HasCompactSupport φ ->
      (∫ x : ℝ, φ x *
        (D x + deriv (fun z => b z * u z) x -
          (1 / 2 : ℝ) *
            deriv (fun z => deriv (fun w => a w * u w) z) x)) = 0) :
    ∀ x : ℝ, D x =
      -deriv (fun z => b z * u z) x +
        (1 / 2 : ℝ) * deriv (fun z => deriv (fun w => a w * u w) z) x := by
  let F : ℝ -> ℝ := fun z => b z * u z
  let A : ℝ -> ℝ := fun z => a z * u z
  have hF : ContDiff ℝ 2 F := by simpa [F] using hb.mul hu
  have hA : ContDiff ℝ 2 A := by simpa [A] using ha.mul hu
  have hFder : Continuous (deriv F) :=
    hF.continuous_deriv (by norm_num)
  have hAder : ContDiff ℝ 1 (deriv A) := hA.deriv'
  have hAder2 : Continuous (deriv (deriv A)) :=
    hAder.continuous_deriv_one
  have hC : Continuous (fun x : ℝ =>
      D x + deriv F x - (1 / 2 : ℝ) * deriv (deriv A) x) :=
    (hD.add hFder).sub (continuous_const.mul hAder2)
  have hz : ∀ x : ℝ,
      D x + deriv F x - (1 / 2 : ℝ) * deriv (deriv A) x = 0 := by
    apply AppliedSDE.SarkkaSolin.continuous_zero_of_compact_smooth_tests
      (g := fun x : ℝ => D x + deriv F x -
        (1 / 2 : ℝ) * deriv (deriv A) x) hC
    intro φ hφ hcomp
    exact hweak φ hφ hcomp
  intro x
  specialize hz x
  dsimp [F, A] at hz
  linarith
