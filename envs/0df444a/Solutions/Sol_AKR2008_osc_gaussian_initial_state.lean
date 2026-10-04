-- Prove2me | solution 1 for AKR2008.osc_gaussian_initial_state
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:02:08.444989+00:00
-- url     : https://prove2.me/submissions/6cf3b6ea-5ac6-4466-87e2-ad64dbb17761

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
lemma akr3e4c_oscP_eq (ω τ w : ℝ) (hτ : 0 < τ) (v : NNReal) (hvv : (v : ℝ) = τ⁻¹) (x : ℝ) :
    AKR2008.oscP ω τ w x 0 = gaussianPDFReal w v x := by
  simp only [AKR2008.oscP, gaussianPDFReal, mul_zero, Real.cos_zero, one_pow, div_one, mul_one]
  rw [hvv]
  congr 1
  · rw [← Real.sqrt_inv]
    congr 1
    field_simp
  · congr 1
    field_simp

open MeasureTheory ProbabilityTheory in
lemma akr3e4c_derivS (ω x : ℝ) : deriv (fun y => AKR2008.oscS ω y 0) x = 0 := by
  simp [AKR2008.oscS]

open MeasureTheory ProbabilityTheory in
theorem solution (ω τ w : ℝ) (hτ : 0 < τ) :
    ∫ x, AKR2008.oscP ω τ w x 0 = 1 ∧
    ∫ x, x * AKR2008.oscP ω τ w x 0 = w ∧
    Real.sqrt (∫ x, (x - w) ^ 2 * AKR2008.oscP ω τ w x 0) = τ ^ (-(1 / 2 : ℝ)) ∧
    ∫ x, AKR2008.oscP ω τ w x 0 * deriv (fun y => AKR2008.oscS ω y 0) x = 0 ∧
    ∫ x, AKR2008.oscP ω τ w x 0 * (deriv (fun y => AKR2008.oscS ω y 0) x) ^ 2 = 0 := by
  set v : NNReal := ⟨τ⁻¹, by positivity⟩ with hvdef
  have hv : v ≠ 0 := by
    intro h
    have : (v : ℝ) = 0 := by rw [h]; rfl
    have h2 : τ⁻¹ = 0 := this
    exact hτ.ne' (inv_eq_zero.mp h2)
  have hP : ∀ x, AKR2008.oscP ω τ w x 0 = gaussianPDFReal w v x :=
    akr3e4c_oscP_eq ω τ w hτ v rfl
  simp only [hP, akr3e4c_derivS]
  refine ⟨integral_gaussianPDFReal_eq_one w hv, ?_, ?_, by simp, by simp⟩
  · have h := integral_gaussianReal_eq_integral_smul (μ := w) (f := fun x : ℝ => x) hv
    rw [integral_id_gaussianReal] at h
    refine Eq.trans ?_ h.symm
    congr 1
    ext x
    simp [smul_eq_mul, mul_comm]
  · have h := integral_gaussianReal_eq_integral_smul (μ := w) (f := fun x : ℝ => (x - w) ^ 2) hv
    have hvar := variance_eq_integral (X := (id : ℝ → ℝ)) (μ := gaussianReal w v)
      measurable_id.aemeasurable
    rw [variance_id_gaussianReal] at hvar
    simp only [id, integral_id_gaussianReal] at hvar
    have hI : ∫ x, (x - w) ^ 2 * gaussianPDFReal w v x = τ⁻¹ := by
      have : ∫ x, (x - w) ^ 2 * gaussianPDFReal w v x = ∫ x, (x - w) ^ 2 ∂gaussianReal w v := by
        rw [h]; congr 1; ext x; simp [smul_eq_mul, mul_comm]
      rw [this, ← hvar]
      rfl
    rw [hI, Real.sqrt_eq_rpow, Real.rpow_neg hτ.le, Real.inv_rpow hτ.le]
