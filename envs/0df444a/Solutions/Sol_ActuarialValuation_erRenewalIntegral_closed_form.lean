-- Prove2me | solution 1 for ActuarialValuation.erRenewalIntegral_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:18:16.920927+00:00
-- url     : https://prove2.me/submissions/109e7ed7-7e96-4040-84ee-54cd4c0b17b5

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_actuarial_erTrafficIntensity
import Definitions.Def_actuarial_erAdjustment
import Definitions.Def_actuarial_erRenewalIntegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

open MeasureTheory

theorem solution (lambda c beta u : ℝ) (hl : 0<lambda) (hc : 0<c) (hb : 0<beta) :
    erRenewalIntegral lambda c beta u =
      erTrafficIntensity lambda c beta * beta / (beta-erAdjustment lambda c beta) *
        (Real.exp (-(erAdjustment lambda c beta)*u)-Real.exp (-beta*u)) := by
  let r : ℝ := erAdjustment lambda c beta
  have hden : beta-r = lambda/c := by dsimp [r, erAdjustment]; ring
  have hden0 : beta-r ≠ 0 := by rw [hden]; exact (div_pos hl hc).ne'
  unfold erRenewalIntegral
  let q : ℝ := r-beta
  let a : ℝ := erTrafficIntensity lambda c beta * beta * Real.exp (-r*u) / q
  have hqeq : q = -(beta-r) := by dsimp [q]; ring
  have hq0 : q ≠ 0 := by rw [hqeq]; exact neg_ne_zero.mpr hden0
  have hexp_point (x : ℝ) :
      Real.exp (-r*(u-x))*Real.exp (-beta*x) = Real.exp (-r*u+q*x) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [q]
    ring
  have hpoint (x : ℝ) :
      erRuinCandidate lambda c beta (u-x) * beta * Real.exp (-beta*x) =
        a * (q * Real.exp (q*x)) := by
    simp only [erRuinCandidate]
    calc
      _ = erTrafficIntensity lambda c beta * beta *
          (Real.exp (-r*(u-x))*Real.exp (-beta*x)) := by ring
      _ = erTrafficIntensity lambda c beta * beta * Real.exp (-r*u+q*x) := by
        rw [hexp_point]
      _ = erTrafficIntensity lambda c beta * beta *
          (Real.exp (-r*u)*Real.exp (q*x)) := by rw [Real.exp_add]
      _ = a * (q * Real.exp (q*x)) := by
        dsimp [a]
        field_simp [hq0]
        <;> ring
  have hderiv (x : ℝ) :
      HasDerivAt (fun y : ℝ => a*Real.exp (q*y))
        (a*(q*Real.exp (q*x))) x := by
    have hlinear := (hasDerivAt_id x).const_mul q
    have hexp := (Real.hasDerivAt_exp (q*x)).comp x hlinear
    have hscaled := hexp.const_mul a
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hcontinuous : Continuous (fun x : ℝ => a*(q*Real.exp (q*x))) := by
    continuity
  have hintegrable : IntervalIntegrable
      (fun x : ℝ => a*(q*Real.exp (q*x))) volume 0 u :=
    hcontinuous.intervalIntegrable 0 u
  have hftc :
      (∫ x in (0 : ℝ)..u, a*(q*Real.exp (q*x))) =
        a*Real.exp (q*u)-a*Real.exp (q*0) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      exact hderiv x
    · exact hintegrable
  calc
    (∫ x in (0 : ℝ)..u,
        erRuinCandidate lambda c beta (u-x)*beta*Real.exp (-beta*x)) =
      ∫ x in (0 : ℝ)..u, a*(q*Real.exp (q*x)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hpoint x
    _ = a*Real.exp (q*u)-a*Real.exp (q*0) := hftc
    _ = erTrafficIntensity lambda c beta * beta / (beta-r) *
        (Real.exp (-r*u)-Real.exp (-beta*u)) := by
          dsimp [a]
          simp only [mul_zero, Real.exp_zero, mul_one]
          rw [hqeq]
          have hend : Real.exp (-(beta-r)*u) = Real.exp (-beta*u) / Real.exp (-r*u) := by
            rw [← Real.exp_sub]
            congr 1
            ring
          rw [hend]
          field_simp [hden0, Real.exp_ne_zero]
          <;> ring
