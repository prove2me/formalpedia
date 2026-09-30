-- Prove2me | solution 1 for AKR2008.osc_HJ_solution
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:53:25.487984+00:00
-- url     : https://prove2.me/submissions/f2470738-00cb-479d-8820-8f91a5524f0e

import Definitions.Def_AKR2008_HybridDefs
set_option autoImplicit false
open AKR2008

theorem solution (ω x t : ℝ) (hcos : Real.cos (ω * t) ≠ 0) :
    deriv (fun s => oscS ω x s) t + (1 / 2) * (deriv (fun y => oscS ω y t) x) ^ 2
      + (1 / 2) * ω ^ 2 * x ^ 2 = 0 := by
  have ht : HasDerivAt (fun s => oscS ω x s)
      (-(ω*x^2/2) * ((Real.cos (ω*t)^2)⁻¹ * ω)) t := by
    simpa [oscS, Function.comp_def, one_div] using
      ((Real.hasDerivAt_tan hcos).comp t ((hasDerivAt_id t).const_mul ω)).const_mul (-(ω*x^2/2))
  have hx : HasDerivAt (fun y => oscS ω y t)
      (-(ω*(2*x)/2)*Real.tan (ω*t)) x := by
    simpa [oscS] using (((((hasDerivAt_id x).pow 2).const_mul ω).div_const 2).neg).mul_const
      (Real.tan (ω*t))
  rw [ht.deriv, hx.deriv, Real.tan_eq_sin_div_cos]
  field_simp
  linear_combination ω^2*x^2*(Real.sin_sq_add_cos_sq (ω*t))
