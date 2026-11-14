-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ou_deterministic_integrand_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:42:08.502218+00:00
-- url     : https://prove2.me/submissions/71ae9f0f-ae38-49fa-9b31-5e9be995a672

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory

private theorem ou_exp_interval
    (rate q T : ℝ) (hrate : 0 < rate) :
    (∫ s in (0 : ℝ)..T, q * Real.exp (-2 * rate * (T - s))) =
      q / (2 * rate) * (1 - Real.exp (-2 * rate * T)) := by
  have hrne : (2 * rate) ≠ 0 := by positivity
  let F : ℝ → ℝ :=
    fun s => q / (2 * rate) * Real.exp (-2 * rate * (T - s))
  have hF (s : ℝ) :
      HasDerivAt F (q * Real.exp (-2 * rate * (T - s))) s := by
    have hsub : HasDerivAt (fun u : ℝ => T - u) (-1) s := by
      exact (hasDerivAt_id s).const_sub T
    have hinner :
        HasDerivAt (fun u : ℝ => -2 * rate * (T - u))
          (2 * rate) s := by
      have hd : (-2 * rate) * (-1) = 2 * rate := by ring
      exact hd ▸ (hsub.const_mul (-2 * rate))
    have hexp : HasDerivAt F
        ((q / (2 * rate)) *
          ((2 * rate) * Real.exp (-2 * rate * (T - s)))) s := by
      dsimp [F]
      have hd :
          (q / (2 * rate)) *
              (Real.exp (-2 * rate * (T - s)) * (2 * rate)) =
            (q / (2 * rate)) *
              ((2 * rate) * Real.exp (-2 * rate * (T - s))) := by ring
      exact hd ▸ (((Real.hasDerivAt_exp _).comp s hinner).const_mul
        (q / (2 * rate)))
    have hcoeff :
        (q / (2 * rate)) *
          ((2 * rate) * Real.exp (-2 * rate * (T - s))) =
        q * Real.exp (-2 * rate * (T - s)) := by
      field_simp [hrne]
    exact hcoeff ▸ hexp
  have hcont : Continuous
      (fun s : ℝ => q * Real.exp (-2 * rate * (T - s))) := by
    fun_prop
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := T) (fun s _ => hF s)
      (hcont.intervalIntegrable (0 : ℝ) T)
  have hfinal :
      F T - F 0 =
        q / (2 * rate) * (1 - Real.exp (-2 * rate * T)) := by
    dsimp [F]
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one, sub_zero]
    ring
  exact hFTC.trans hfinal

private theorem ou_integrand_sq
    (rate q T s : ℝ) (hq : 0 ≤ q) :
    (Real.sqrt q * Real.exp (-rate * (T - s))) ^ 2 =
      q * Real.exp (-2 * rate * (T - s)) := by
  calc
    (Real.sqrt q * Real.exp (-rate * (T - s))) ^ 2 =
        (Real.sqrt q) ^ 2 * (Real.exp (-rate * (T - s))) ^ 2 := by ring
    _ = q * Real.exp ((-rate * (T - s)) + (-rate * (T - s))) := by
        rw [Real.sq_sqrt hq, pow_two, ← Real.exp_add]
    _ = q * Real.exp (-2 * rate * (T - s)) := by
        congr 1
        ring

theorem solution
    (rate q T : ℝ) (hrate : 0 < rate) (hq : 0 ≤ q) (hT : 0 ≤ T) :
    (∫ s in (0 : ℝ)..T,
      (Real.sqrt q * Real.exp (-rate * (T - s))) ^ 2) =
      q / (2 * rate) * (1 - Real.exp (-2 * rate * T)) := by
  calc
    (∫ s in (0 : ℝ)..T,
      (Real.sqrt q * Real.exp (-rate * (T - s))) ^ 2) =
        ∫ s in (0 : ℝ)..T,
          q * Real.exp (-2 * rate * (T - s)) := by
            apply intervalIntegral.integral_congr
            intro s hs
            exact ou_integrand_sq rate q T s hq
    _ = q / (2 * rate) * (1 - Real.exp (-2 * rate * T)) :=
          ou_exp_interval rate q T hrate
