-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussian_constant_drift_time_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:10:36.005001+00:00
-- url     : https://prove2.me/submissions/c5ea0046-6b9c-4f03-af80-f8f71c5d1f39

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_time_density_quotient_algebra
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Topology
set_option autoImplicit false
theorem solution
    (b q y s t x : ℝ) (hq : 0 < q) (hst : s < t) :
    let p : ℝ -> ℝ := fun tau =>
      Real.exp (-((x - y - b * (tau - s)) ^ 2 / (2 * q * (tau - s)))) /
        Real.sqrt (2 * Real.pi * q * (tau - s))
    deriv p t =
      (b * (x - y - b * (t - s)) / (q * (t - s)) +
        (x - y - b * (t - s)) ^ 2 / (2 * q * (t - s) ^ 2) -
          1 / (2 * (t - s))) * p t := by
  let d : ℝ -> ℝ := fun u => u - s
  let g : ℝ -> ℝ := fun u => x - y - b * d u
  let A : ℝ -> ℝ := fun u => 2 * q * d u
  let N : ℝ -> ℝ := fun u => 2 * Real.pi * q * d u
  let h : ℝ -> ℝ := fun u => -(g u ^ 2 / A u)
  let p : ℝ -> ℝ := fun u => Real.exp (h u) / Real.sqrt (N u)
  change deriv p t = (b * g t / (q * d t) +
      g t ^ 2 / (2 * q * (d t) ^ 2) - 1 / (2 * d t)) * p t
  have hdpos : 0 < d t := sub_pos.mpr hst
  have hqne : q ≠ 0 := ne_of_gt hq
  have hdne : d t ≠ 0 := ne_of_gt hdpos
  have hAne : A t ≠ 0 := by
    dsimp [A]; positivity
  have hNpos : 0 < N t := by
    dsimp [N]; positivity
  have hNne : N t ≠ 0 := ne_of_gt hNpos
  have hSne : Real.sqrt (N t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hNpos)
  have hd : HasDerivAt d 1 t := (hasDerivAt_id t).sub_const s
  have hg := (hd.const_mul b).const_sub (x - y)
  have hA := hd.const_mul (2 * q)
  have hN := hd.const_mul (2 * Real.pi * q)
  have hh := ((hg.pow 2).div hA hAne).neg
  have hs := hN.sqrt hNne
  have hder := hh.exp.div hs hSne
  change HasDerivAt p _ t at hder
  rw [hder.deriv]
  convert AppliedSDE.SarkkaSolin.gaussian_time_density_quotient_algebra
    b q (d t) (g t) (Real.sqrt (N t)) (Real.exp (h t))
    hqne hdne hSne (Real.sq_sqrt hNpos.le)
    using 1 <;>
    simp [p, h, A, N, g, d, div_eq_mul_inv, mul_assoc]
