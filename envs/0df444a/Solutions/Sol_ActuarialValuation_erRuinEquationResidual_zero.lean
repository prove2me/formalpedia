-- Prove2me | solution 1 for ActuarialValuation.erRuinEquationResidual_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:51:22.685134+00:00
-- url     : https://prove2.me/submissions/27798825-ea3a-4280-b83c-162a6e6c1ceb

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_actuarial_erAdjustment
import Definitions.Def_actuarial_erRuinCandidate
import Definitions.Def_actuarial_erRuinDerivativeRHS
import Definitions.Def_actuarial_erRuinEquationResidual
import Definitions.Def_actuarial_erRenewalIntegral
import Definitions.Def_actuarial_erSeverityTail
import Definitions.Def_actuarial_erTrafficIntensity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation MeasureTheory

theorem solution (lambda c beta u : ℝ) (hl : 0<lambda) (hc : 0<c) (hb : 0<beta)
    (hn : lambda<c*beta) (hu : 0≤u) : erRuinEquationResidual lambda c beta u=0 := by
  let r : ℝ := erAdjustment lambda c beta
  have hden : beta-r = lambda/c := by dsimp [r, erAdjustment]; ring
  have hden0 : beta-r ≠ 0 := by rw [hden]; exact (div_pos hl hc).ne'
  have hroot : c*(beta-r)=lambda := by rw [hden]; field_simp [hc.ne']
  have hrenewal : erRenewalIntegral lambda c beta u =
      erTrafficIntensity lambda c beta * beta / (beta-r) *
        (Real.exp (-r*u)-Real.exp (-beta*u)) := by
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
          have hend : Real.exp (-(beta-r)*u) =
              Real.exp (-beta*u) / Real.exp (-r*u) := by
            rw [← Real.exp_sub]
            congr 1
            ring
          rw [hend]
          field_simp [hden0, Real.exp_ne_zero]
          <;> ring
  have hratio : (lambda / (c * beta)) * beta / (beta-r) = 1 := by
    rw [hden]
    field_simp [hl.ne', hc.ne', hb.ne']
    <;> ring
  have hrenewal' : erRenewalIntegral lambda c beta u =
      Real.exp (-r*u) - Real.exp (-beta*u) := by
    rw [hrenewal]
    unfold erTrafficIntensity
    rw [hratio]
    ring
  have hcoef :
      c * (-r) * (lambda / (c * beta)) -
        lambda * (lambda / (c * beta)) + lambda = 0 := by
    rw [hroot.symm]
    field_simp [hc.ne', hb.ne']
    <;> ring
  unfold erRuinEquationResidual erRuinDerivativeRHS erRuinCandidate
  rw [show erAdjustment lambda c beta = r by rfl]
  rw [hrenewal']
  unfold erTrafficIntensity erSeverityTail
  calc
    _ = (c * (-r) * (lambda / (c * beta)) -
          lambda * (lambda / (c * beta)) + lambda) *
          Real.exp (-r*u) := by ring
    _ = 0 := by rw [hcoef]; ring
