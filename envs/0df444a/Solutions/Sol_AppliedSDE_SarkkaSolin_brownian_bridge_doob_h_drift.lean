-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.brownian_bridge_doob_h_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:03:05.607293+00:00
-- url     : https://prove2.me/submissions/ebfa62ae-9e41-41bd-806c-6c6fd55d82ec

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped BigOperators

/-- The logarithmic derivative of the endpoint Brownian transition
density gives the Doob h-transform drift of a Brownian bridge. -/
theorem solution
    (q T t x z : ℝ) (hq : 0 < q) (ht : t < T) :
    let h : ℝ → ℝ := fun u =>
      Real.exp (-((z - u) ^ 2 / (2 * q * (T - t)))) /
        Real.sqrt (2 * Real.pi * q * (T - t))
    q * deriv (fun u => Real.log (h u)) x = (z - x) / (T - t) := by
  let h : ℝ → ℝ := fun u =>
    Real.exp (-((z - u) ^ 2 / (2 * q * (T - t)))) /
      Real.sqrt (2 * Real.pi * q * (T - t))
  change q * deriv (fun u => Real.log (h u)) x = (z - x) / (T - t)
  have hd : 0 < T - t := sub_pos.mpr ht
  have hqne : q ≠ 0 := ne_of_gt hq
  have hdne : T - t ≠ 0 := ne_of_gt hd
  have hden : 0 < 2 * Real.pi * q * (T - t) := by positivity
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * q * (T - t)) :=
    Real.sqrt_pos.2 hden
  have hlog : (fun u : ℝ => Real.log (h u)) =
      (fun u : ℝ => -((z - u) ^ 2 / (2 * q * (T - t))) -
        Real.log (Real.sqrt (2 * Real.pi * q * (T - t)))) := by
    funext u
    dsimp [h]
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hsqrt),
      Real.log_exp]
  rw [hlog]
  have hsub : HasDerivAt (fun u : ℝ => z - u) (-1) x := by
    exact (hasDerivAt_id x).const_sub z
  have hpow := (hsub.pow 2)
  have hcalc := (hpow.div_const (2 * q * (T - t))).neg
  have hder : deriv (fun u : ℝ =>
      -((z - u) ^ 2 / (2 * q * (T - t)))) x =
      (z - x) / (q * (T - t)) := by
    convert hcalc.deriv using 1
    · simp [Pi.neg_apply, Pi.pow_apply, Pi.div_apply]
    · field_simp [hqne, hdne]
      ring
  rw [deriv_sub_const, hder]
  field_simp [hqne, hdne]
