-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.scalar_linear_ode_variation_constants
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:51:45.629236+00:00
-- url     : https://prove2.me/submissions/960dc7ac-feaa-41c1-9a6b-b62b62c83f7d

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology

theorem solution
    (a x₀ : ℝ) (b x : ℝ → ℝ)
    (hb : Continuous b)
    (hxcont : Continuous x)
    (hxdiff : ∀ t : ℝ, 0 ≤ t → DifferentiableAt ℝ x t)
    (hx0 : x 0 = x₀)
    (hode : ∀ t : ℝ, 0 ≤ t → deriv x t = a * x t + b t) :
    ∀ t : ℝ, 0 ≤ t →
      x t = Real.exp (a * t) * x₀ +
        ∫ s in (0 : ℝ)..t, Real.exp (a * (t - s)) * b s := by
  intro t ht
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun u : ℝ => Real.exp (a * (t - u)) * x u)
        (Real.exp (a * (t - s)) * b s) s := by
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    have hs0 : 0 ≤ s := hs.1
    have hsub : HasDerivAt (fun u : ℝ => t - u) (-1) s := by
      exact (hasDerivAt_id s).const_sub t
    have hinner : HasDerivAt (fun u : ℝ => a * (t - u)) (-a) s := by
      simpa only [mul_neg, mul_one] using (hsub.const_mul a)
    have hexp : HasDerivAt (fun u : ℝ => Real.exp (a * (t - u)))
        (-a * Real.exp (a * (t - s))) s := by
      have hd : HasDerivAt
          (fun u : ℝ => Real.exp (a * (t - u)))
          (Real.exp (a * (t - s)) * (-a)) s :=
        hinner.exp
      have hcoeff :
          Real.exp (a * (t - s)) * (-a) =
            -a * Real.exp (a * (t - s)) := by ring
      rw [hcoeff] at hd
      exact hd
    have hprod := hexp.mul ((hxdiff s hs0).hasDerivAt)
    have hcoeff :
        (-a * Real.exp (a * (t - s))) * x s +
          Real.exp (a * (t - s)) * deriv x s =
          Real.exp (a * (t - s)) * b s := by
      calc
        (-a * Real.exp (a * (t - s))) * x s +
              Real.exp (a * (t - s)) * deriv x s =
            (-a * Real.exp (a * (t - s))) * x s +
              Real.exp (a * (t - s)) * (a * x s + b s) := by
                  rw [hode s hs0]
        _ = Real.exp (a * (t - s)) * b s := by ring
    exact hcoeff ▸ hprod
  have hcont : Continuous (fun s : ℝ => Real.exp (a * (t - s)) * b s) := by
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (hcont.intervalIntegrable (0 : ℝ) t)
  simp only [sub_self, mul_zero, Real.exp_zero, one_mul, sub_zero, hx0] at hFTC
  calc
    x t = Real.exp (a * t) * x₀ +
      (x t - Real.exp (a * t) * x₀) := by ring
    _ = Real.exp (a * t) * x₀ +
      ∫ s in (0 : ℝ)..t, Real.exp (a * (t - s)) * b s := by rw [hFTC]
