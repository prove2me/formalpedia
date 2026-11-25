-- Prove2me | solution 1 for Arxiv2009_12420.layered_seafloor_integral_equation
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T20:48:22.766278+00:00
-- url     : https://prove2.me/submissions/63cba77f-c2af-4bbf-88ad-eae022c5b29d

import Mathlib
import Definitions.Def_Arxiv2009_12420_Basic

open Complex MeasureTheory

open Arxiv2009_12420

lemma singleLayer_const_mul_aux (k c : ℂ) (gl gm : ℝ → ℝ) (φ : ℝ → ℂ) (x : ℝ) :
    singleLayer k gl gm (fun t => c * φ t) x = c * singleLayer k gl gm φ x := by
  unfold singleLayer
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

theorem solution (ω : ℝ) (hω : 0 < ω) (m0 m1 m2 : Medium)
    (hm0 : m0.IsPhysical) (hm1 : m1.IsPhysical) (hm2 : m2.IsPhysical)
    (g1 g2 : ℝ → ℝ) (hsep : ∀ x, g2 x < g1 x)
    (pinc p0 dp0 p1t dp1t p1b dp1b p2 dp2 : ℝ → ℂ)
    (hΩ0 : ∀ x, (alphaAbove g1 x : ℂ) * p0 x =
      singleLayer (m0.wavenumber ω) g1 g1 dp0 x
        - doubleLayer (m0.wavenumber ω) g1 g1 (normalTop g1) p0 x + pinc x)
    (hΩ1t : ∀ x, (1 - (alphaAbove g1 x : ℂ)) * p1t x =
      -singleLayer (m1.wavenumber ω) g1 g1 dp1t x
        + doubleLayer (m1.wavenumber ω) g1 g1 (normalTop g1) p1t x
        - singleLayer (m1.wavenumber ω) g1 g2 dp1b x
        + doubleLayer (m1.wavenumber ω) g1 g2 (normalBottom g2) p1b x)
    (hΩ1b : ∀ x, (1 - (alphaBelow g2 x : ℂ)) * p1b x =
      -singleLayer (m1.wavenumber ω) g2 g2 dp1b x
        + doubleLayer (m1.wavenumber ω) g2 g2 (normalBottom g2) p1b x
        - singleLayer (m1.wavenumber ω) g2 g1 dp1t x
        + doubleLayer (m1.wavenumber ω) g2 g1 (normalTop g1) p1t x)
    (hΩ2 : ∀ x, (alphaBelow g2 x : ℂ) * p2 x =
      singleLayer (m2.wavenumber ω) g2 g2 dp2 x
        - doubleLayer (m2.wavenumber ω) g2 g2 (normalBottom g2) p2 x)
    (hp1 : ∀ x, p1t x = p0 x) (hv1 : ∀ x, dp1t x / (m1.rho : ℂ) = dp0 x / (m0.rho : ℂ))
    (hp2 : ∀ x, p2 x = p1b x) (hv2 : ∀ x, dp2 x / (m2.rho : ℂ) = dp1b x / (m1.rho : ℂ)) :
    (∀ x, (alphaAbove g1 x : ℂ) * p0 x + doubleLayer (m0.wavenumber ω) g1 g1 (normalTop g1) p0 x
        - singleLayer (m0.wavenumber ω) g1 g1 dp0 x = pinc x) ∧
    (∀ x, (1 - (alphaAbove g1 x : ℂ)) * p0 x - doubleLayer (m1.wavenumber ω) g1 g1 (normalTop g1) p0 x
        + (densityRatio m1 m0 : ℂ) * singleLayer (m1.wavenumber ω) g1 g1 dp0 x
        - doubleLayer (m1.wavenumber ω) g1 g2 (normalBottom g2) p1b x
        + (densityRatio m1 m0 : ℂ) * singleLayer (m1.wavenumber ω) g1 g2
            (fun t => (densityRatio m1 m0 : ℂ)⁻¹ * dp1b t) x = 0) ∧
    (∀ x, -doubleLayer (m1.wavenumber ω) g2 g1 (normalTop g1) p0 x
        + (densityRatio m1 m0 : ℂ) * singleLayer (m1.wavenumber ω) g2 g1 dp0 x
        + (1 - (alphaBelow g2 x : ℂ)) * p1b x
        - doubleLayer (m1.wavenumber ω) g2 g2 (normalBottom g2) p1b x
        + (densityRatio m1 m0 : ℂ) * singleLayer (m1.wavenumber ω) g2 g2
            (fun t => (densityRatio m1 m0 : ℂ)⁻¹ * dp1b t) x = 0) ∧
    (∀ x, (alphaBelow g2 x : ℂ) * p1b x + doubleLayer (m2.wavenumber ω) g2 g2 (normalBottom g2) p1b x
        - (densityRatio m2 m0 : ℂ) * singleLayer (m2.wavenumber ω) g2 g2
            (fun t => (densityRatio m1 m0 : ℂ)⁻¹ * dp1b t) x = 0) := by
  have h0 : (m0.rho : ℂ) ≠ 0 := by exact_mod_cast hm0.2.1.ne'
  have h1 : (m1.rho : ℂ) ≠ 0 := by exact_mod_cast hm1.2.1.ne'
  have h2 : (m2.rho : ℂ) ≠ 0 := by exact_mod_cast hm2.2.1.ne'
  have hρ : (densityRatio m1 m0 : ℂ) ≠ 0 := by
    unfold densityRatio; push_cast; exact div_ne_zero h1 h0
  have hp1' : p1t = p0 := funext hp1
  have hp2' : p2 = p1b := funext hp2
  have hdp1t : dp1t = fun t => (densityRatio m1 m0 : ℂ) * dp0 t := by
    funext t
    have := hv1 t
    rw [div_eq_div_iff h1 h0] at this
    unfold densityRatio
    push_cast
    field_simp
    linear_combination this
  have hdp2 : dp2 = fun t => ((m2.rho : ℂ) / (m1.rho : ℂ)) * dp1b t := by
    funext t
    have := hv2 t
    rw [div_eq_div_iff h2 h1] at this
    field_simp
    linear_combination this
  have hr : (densityRatio m2 m0 : ℂ) * (densityRatio m1 m0 : ℂ)⁻¹
      = (m2.rho : ℂ) / (m1.rho : ℂ) := by
    unfold densityRatio
    push_cast
    field_simp
  rw [hp1', hdp1t] at hΩ1t hΩ1b
  rw [hp2', hdp2] at hΩ2
  simp only [singleLayer_const_mul_aux] at hΩ1t hΩ1b hΩ2 ⊢
  simp only [mul_inv_cancel_left₀ hρ]
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · linear_combination hΩ0 x
  · linear_combination hΩ1t x
  · linear_combination hΩ1b x
  · linear_combination hΩ2 x - singleLayer (m2.wavenumber ω) g2 g2 dp1b x * hr
