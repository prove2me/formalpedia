-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.stationary_boltzmann_density_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:27:00.074259+00:00
-- url     : https://prove2.me/submissions/06061d86-fbe3-4a2e-8fb1-289009d72d66

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Topology
set_option autoImplicit false
theorem solution
    (q : ℝ) (hq : 0 < q) (v : ℝ -> ℝ)
    (hv : ContDiff ℝ 2 v) (Z : ℝ) :
    let p : ℝ -> ℝ := fun x => Z⁻¹ * Real.exp (-(v x / q))
    ∀ x : ℝ, deriv p x = -(deriv v x / q) * p x := by
  intro p x
  have hvx : HasDerivAt v (deriv v x) x :=
    (hv.differentiable (by norm_num) x).hasDerivAt
  have hinner : HasDerivAt
      (fun z : ℝ => -(v z / q)) (-(deriv v x / q)) x := by
    simpa only [neg_one_mul] using (hvx.div_const q).const_mul (-1 : ℝ)
  have hpder : HasDerivAt
      (fun z : ℝ => Z⁻¹ * Real.exp (-(v z / q)))
      (Z⁻¹ * (Real.exp (-(v x / q)) * (-(deriv v x / q)))) x := by
    simpa using (hinner.exp.const_mul (Z⁻¹))
  change deriv (fun z : ℝ => Z⁻¹ * Real.exp (-(v z / q))) x =
    -(deriv v x / q) * (Z⁻¹ * Real.exp (-(v x / q)))
  rw [hpder.deriv]
  ring
