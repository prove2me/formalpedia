-- Prove2me | solution 1 for ActuarialValuation.erRuin_candidate_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T21:46:01.578534+00:00
-- url     : https://prove2.me/submissions/7cb20ebf-9010-4719-8be6-76206599831d

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Group.Ext
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_actuarial_erExponentialMGF
import Definitions.Def_actuarial_erAdjustment
import Definitions.Def_actuarial_erLundbergGap
import Definitions.Def_actuarial_erNetLossMGF
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
    (hn : lambda<c*beta) (hu : 0≤u) :
    (0<erAdjustment lambda c beta) ∧
      (erLundbergGap lambda c beta (erAdjustment lambda c beta)=0) ∧
      (erNetLossMGF lambda c beta (erAdjustment lambda c beta) u=1) ∧
      (HasDerivAt (erRuinCandidate lambda c beta)
        (erRuinDerivativeRHS lambda c beta u) u) ∧
      (erRuinEquationResidual lambda c beta u=0) := by
  have h_adj : 0 < erAdjustment lambda c beta := by unfold erAdjustment; have hratio : lambda / c < beta := (div_lt_iff₀ hc).2 (by nlinarith [hn]); linarith
  let r : ℝ := erAdjustment lambda c beta
  have hden : beta - r = lambda / c := by dsimp [r, erAdjustment]; ring
  have hden0 : beta - r ≠ 0 := by rw [hden]; exact (div_pos hl hc).ne'
  have hcr : c * r = c * beta - lambda := by have h := hden; field_simp [hc.ne'] at h; nlinarith
  have h_gap : erLundbergGap lambda c beta (erAdjustment lambda c beta) = 0 := by
    change lambda * (erExponentialMGF beta r - 1) - c * r = 0
    unfold erExponentialMGF
    rw [hden]
    field_simp [hl.ne', hc.ne']
    nlinarith [hcr]
  have h_mgf : erNetLossMGF lambda c beta (erAdjustment lambda c beta) u = 1 := by
    unfold erNetLossMGF
    rw [h_gap]
    simp
  have h_deriv : HasDerivAt (erRuinCandidate lambda c beta)
      (erRuinDerivativeRHS lambda c beta u) u := by
    letI : AddCommGroup ℝ := Real.instAddCommGroup
    letI : Module ℝ ℝ := @Semiring.toModule ℝ Real.semiring
    have hlinear := (hasDerivAt_id u).const_mul (-(erAdjustment lambda c beta))
    have hexp := (Real.hasDerivAt_exp (-(erAdjustment lambda c beta) * u)).comp u hlinear
    have hscaled := hexp.const_mul (erTrafficIntensity lambda c beta)
    unfold erRuinCandidate erRuinDerivativeRHS
    have hadd : @Ring.toAddCommGroup ℝ (@NormedRing.toRing ℝ (@NormedCommRing.toNormedRing ℝ Real.normedCommRing)) = Real.instAddCommGroup := by apply AddCommGroup.ext; funext x y; rfl
    have hmod : @NormedSpace.toModule ℝ ℝ inferInstance inferInstance inferInstance = @Semiring.toModule ℝ inferInstance := by apply Module.ext; funext a x; rfl
    convert hscaled using 1
    simp only [HasDerivAt, hadd, hmod, mul_assoc, mul_left_comm, mul_comm]
    · apply Module.ext
      funext a x
      rfl
    · funext y
      rfl
    · simp only [erRuinCandidate]
      ring
  have hrenewal : erRenewalIntegral lambda c beta u =
      erTrafficIntensity lambda c beta * beta / (beta - r) *
        (Real.exp (-r * u) - Real.exp (-beta * u)) := by
    unfold erRenewalIntegral
    let q : ℝ := r - beta
    let a : ℝ := erTrafficIntensity lambda c beta * beta * Real.exp (-r * u) / q
    have hqeq : q = -(beta - r) := by dsimp [q]; ring
    have hq0 : q ≠ 0 := by rw [hqeq]; exact neg_ne_zero.mpr hden0
    have hexp_point (x : ℝ) :
        Real.exp (-r * (u - x)) * Real.exp (-beta * x) =
          Real.exp (-r * u + q * x) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [q]
      ring
    have hpoint (x : ℝ) :
        erRuinCandidate lambda c beta (u - x) * beta * Real.exp (-beta * x) =
          a * (q * Real.exp (q * x)) := by
      simp only [erRuinCandidate]
      calc
        _ = erTrafficIntensity lambda c beta * beta *
            (Real.exp (-r * (u - x)) * Real.exp (-beta * x)) := by ring
        _ = erTrafficIntensity lambda c beta * beta *
            Real.exp (-r * u + q * x) := by rw [hexp_point]
        _ = erTrafficIntensity lambda c beta * beta *
            (Real.exp (-r * u) * Real.exp (q * x)) := by rw [Real.exp_add]
        _ = a * (q * Real.exp (q * x)) := by
          dsimp [a]
          field_simp [hq0]
          <;> ring
    have hderiv (x : ℝ) :
        HasDerivAt (fun y : ℝ => a * Real.exp (q * y))
          (a * (q * Real.exp (q * x))) x := by
      have hlinear := (hasDerivAt_id x).const_mul q
      have hexp := (Real.hasDerivAt_exp (q * x)).comp x hlinear
      have hscaled := hexp.const_mul a
      simpa [mul_comm] using hscaled
    have hcontinuous : Continuous
        (fun x : ℝ => a * (q * Real.exp (q * x))) := by
      continuity
    have hintegrable : IntervalIntegrable
        (fun x : ℝ => a * (q * Real.exp (q * x))) volume 0 u :=
      hcontinuous.intervalIntegrable 0 u
    have hftc :
        (∫ x in (0 : ℝ)..u, a * (q * Real.exp (q * x))) =
          a * Real.exp (q * u) - a * Real.exp (q * 0) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        exact hderiv x
      · exact hintegrable
    calc
      (∫ x in (0 : ℝ)..u,
          erRuinCandidate lambda c beta (u - x) * beta * Real.exp (-beta * x)) =
          ∫ x in (0 : ℝ)..u, a * (q * Real.exp (q * x)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hpoint x
      _ = a * Real.exp (q * u) - a * Real.exp (q * 0) := hftc
      _ = erTrafficIntensity lambda c beta * beta / (beta - r) *
          (Real.exp (-r * u) - Real.exp (-beta * u)) := by
        dsimp [a]
        simp only [mul_zero, Real.exp_zero, mul_one]
        rw [hqeq]
        have hend : Real.exp (-(beta - r) * u) =
            Real.exp (-beta * u) / Real.exp (-r * u) := by
          rw [← Real.exp_sub]
          congr 1
          ring
        rw [hend]
        field_simp [hden0, Real.exp_ne_zero]
        <;> ring
  have htraffic : erTrafficIntensity lambda c beta = lambda / (c * beta) := by unfold erTrafficIntensity; ring
  have hrenewal_coeff : erTrafficIntensity lambda c beta * beta / (beta - r) = 1 := by
    rw [hden]; unfold erTrafficIntensity
    field_simp [hl.ne', hc.ne', hb.ne'] <;> ring
  refine ⟨h_adj, h_gap, h_mgf, h_deriv, ?_⟩
  unfold erRuinEquationResidual erRuinDerivativeRHS erRuinCandidate erSeverityTail
  rw [show erAdjustment lambda c beta = r by rfl]
  rw [hrenewal]
  rw [hrenewal_coeff, htraffic]
  have hroot : -c * r - lambda + c * beta = 0 := by nlinarith [hcr]
  calc
    _ = (lambda / (c * beta)) * (-c * r - lambda + c * beta) *
        Real.exp (-r * u) := by
      field_simp [hc.ne', hb.ne']
      <;> ring
    _ = 0 := by rw [hroot]; ring
