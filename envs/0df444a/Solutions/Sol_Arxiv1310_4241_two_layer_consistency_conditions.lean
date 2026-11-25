-- Prove2me | solution 1 for Arxiv1310_4241.two_layer_consistency_conditions
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T19:26:40.387128+00:00
-- url     : https://prove2.me/submissions/8e5c52b0-8aef-4b01-9993-7e6bca041e1e

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology Arxiv1310_4241

private lemma hasFDerivAt_mode (ξ η : ℝ) (p : Space) :
    HasFDerivAt (mode ξ η)
      (mode ξ η p •
        (Complex.I • ((ξ : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
          (η : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)))))) p := by
  have h0 : HasFDerivAt (fun q : Space => ((q 0 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt
  have h1 : HasFDerivAt (fun q : Space => ((q 1 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).hasFDerivAt
  have harg := ((h0.const_mul (ξ : ℂ)).add (h1.const_mul (η : ℂ))).const_mul Complex.I
  have hexp := ((Complex.hasDerivAt_exp _).hasFDerivAt.restrictScalars ℝ).comp p harg
  have hexp' : HasFDerivAt (mode ξ η) _ p :=
    hexp.congr_of_eventuallyEq (Eventually.of_forall fun q => by
      simp [Function.comp, mode, planeWave])
  refine hexp'.congr_fderiv ?_
  ext v
  simp [mode, planeWave, smul_eq_mul, mul_comm]

private lemma pd_const_mode (i : Fin 3) (c : ℂ) (ξ η : ℝ) (p : Space) :
    pd i (fun q => c * mode ξ η q) p =
      c * (match i with | 0 => Complex.I * ξ | 1 => Complex.I * η | 2 => 0) * mode ξ η p := by
  have h := (hasFDerivAt_mode ξ η p).const_mul c
  have hproj : ∀ (k j : Fin 3),
      EuclideanSpace.proj (𝕜 := ℝ) k (EuclideanSpace.single j (1 : ℝ)) = if k = j then 1 else 0 := by
    intro k j
    change (EuclideanSpace.single j (1 : ℝ)).ofLp k = _
    simp [PiLp.single_apply]
  rw [pd, h.fderiv]
  fin_cases i <;> simp [hproj] <;> ring

private lemma tangentialDivergence_modeField (v : Fin 3 → ℂ) (ξ η : ℝ) (p : Space) :
    tangentialDivergence (modeField v ξ η) p =
      (Complex.I * ξ * v 0 + Complex.I * η * v 1) * mode ξ η p := by
  simp only [tangentialDivergence, modeField]
  rw [pd_const_mode 0, pd_const_mode 1]
  ring

private lemma wavenumber_of_pos (ω a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    wavenumber ω (a : ℂ) (b : ℂ) = (ω : ℂ) * (Real.sqrt (a * b) : ℂ) := by
  rw [wavenumber]
  congr 1
  have hab : 0 ≤ a * b := mul_nonneg ha.le hb.le
  rw [← Complex.ofReal_mul, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hab]
  norm_cast
  rw [Real.sqrt_eq_rpow]

theorem solution (ω ε0 μ0 ε1 μ1 : ℝ) (hω : 0 < ω) (hε0 : 0 < ε0)
    (hμ0 : 0 < μ0) (hε1 : 0 < ε1) (hμ1 : 0 < μ1) (ξ η : ℝ) (hξη : (ξ, η) ≠ (0, 0))
    (r0 r1 q0 q1 : ℂ) (p : Space) :
    tangentialDivergence (modeField (twoLayerJ0 ω ε0 μ0 ε1 μ1 ξ η r0 r1) ξ η) p =
        Complex.I * wavenumber ω ε0 μ0 * (r0 * mode ξ η p) ∧
    tangentialDivergence (modeField (twoLayerJ1 ω ε0 μ0 ε1 μ1 ξ η r0 r1) ξ η) p =
        Complex.I * wavenumber ω ε1 μ1 * (r1 * mode ξ η p) ∧
    tangentialDivergence (modeField (twoLayerM0 ω ε0 μ0 ε1 μ1 ξ η q0 q1) ξ η) p =
        Complex.I * wavenumber ω ε0 μ0 * (q0 * mode ξ η p) ∧
    tangentialDivergence (modeField (twoLayerM1 ω ε0 μ0 ε1 μ1 ξ η q0 q1) ξ η) p =
        Complex.I * wavenumber ω ε1 μ1 * (q1 * mode ξ η p) := by
  have hρ2_real : (0 : ℝ) < ξ ^ 2 + η ^ 2 := by
    by_contra h
    push Not at h
    exact hξη (Prod.ext (by nlinarith [sq_nonneg ξ, sq_nonneg η]) (by nlinarith [sq_nonneg ξ, sq_nonneg η]))
  have hρ2 : (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 ≠ 0 := by
    have : ((ξ ^ 2 + η ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ2_real.ne'
    simpa using this
  have hsq_e : (Real.sqrt (ε0 / ε1) : ℂ) * ((ε1 * Real.sqrt (μ1 / ε0) : ℝ) : ℂ) = (Real.sqrt (ε1 * μ1) : ℂ) := by
    exact_mod_cast (show Real.sqrt (ε0 / ε1) * (ε1 * Real.sqrt (μ1 / ε0)) = Real.sqrt (ε1 * μ1) by
      rw [Real.sqrt_div hε0.le, Real.sqrt_div hμ1.le, Real.sqrt_mul hε1.le]
      have h1 : 0 < Real.sqrt ε0 := Real.sqrt_pos.mpr hε0
      have h2 : 0 < Real.sqrt ε1 := Real.sqrt_pos.mpr hε1
      have hsq : Real.sqrt ε1 * Real.sqrt ε1 = ε1 := Real.mul_self_sqrt hε1.le
      field_simp [h1.ne', h2.ne']; nlinarith [hsq])
  have hsq_m : (Real.sqrt (μ0 / μ1) : ℂ) * ((μ1 * Real.sqrt (ε1 / μ0) : ℝ) : ℂ) = (Real.sqrt (ε1 * μ1) : ℂ) := by
    exact_mod_cast (show Real.sqrt (μ0 / μ1) * (μ1 * Real.sqrt (ε1 / μ0)) = Real.sqrt (ε1 * μ1) by
      rw [Real.sqrt_div hμ0.le, Real.sqrt_div hε1.le, Real.sqrt_mul hε1.le]
      have h1 : 0 < Real.sqrt μ0 := Real.sqrt_pos.mpr hμ0
      have h2 : 0 < Real.sqrt μ1 := Real.sqrt_pos.mpr hμ1
      have hsq : Real.sqrt μ1 * Real.sqrt μ1 = μ1 := Real.mul_self_sqrt hμ1.le
      field_simp [h1.ne', h2.ne']; nlinarith [hsq])
  have hcomm : Real.sqrt (μ0 * ε0) = Real.sqrt (ε0 * μ0) := by rw [mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tangentialDivergence_modeField, wavenumber_of_pos ω ε0 μ0 hε0 hμ0]
    simp only [twoLayerJ0, gradInvLap, nCross, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, hcomm]
    field_simp [hρ2]
    ring_nf; simp [Complex.I_sq]
  · rw [tangentialDivergence_modeField, wavenumber_of_pos ω ε1 μ1 hε1 hμ1]
    simp only [twoLayerJ1, twoLayerJ0, gradInvLap, nCross, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hcoeff :
        Complex.I * (ξ : ℂ) * -((Real.sqrt (ε0 / ε1) : ℂ) * (Complex.I * (ω : ℂ) *
            ((Real.sqrt (μ0 * ε0) : ℂ) * (Complex.I * (η : ℂ) * (-r0 / ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2))) -
              ((ε1 * Real.sqrt (μ1 / ε0) : ℝ) : ℂ) * (Complex.I * (ξ : ℂ) * (-r1 / ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2)))))) +
        Complex.I * (η : ℂ) * ((Real.sqrt (ε0 / ε1) : ℂ) * (Complex.I * (ω : ℂ) *
            ((Real.sqrt (μ0 * ε0) : ℂ) * (Complex.I * (ξ : ℂ) * (-r0 / ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2))) -
              ((ε1 * Real.sqrt (μ1 / ε0) : ℝ) : ℂ) * -(Complex.I * (η : ℂ) * (-r1 / ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2)))))) =
        Complex.I * (ω : ℂ) * ((Real.sqrt (ε0 / ε1) : ℂ) * ((ε1 * Real.sqrt (μ1 / ε0) : ℝ) : ℂ)) * r1 := by
      field_simp [hρ2]
      ring_nf; simp [Complex.I_sq]
    rw [hcoeff, hsq_e]; ring
  · rw [tangentialDivergence_modeField, wavenumber_of_pos ω ε0 μ0 hε0 hμ0]
    simp only [twoLayerM0, gradInvLap, nCross, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, hcomm]
    field_simp [hρ2]
    ring_nf; simp [Complex.I_sq]
  · rw [tangentialDivergence_modeField, wavenumber_of_pos ω ε1 μ1 hε1 hμ1]
    simp only [twoLayerM1, twoLayerM0, gradInvLap, nCross, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hcoeff :
        Complex.I * (ξ : ℂ) * -((Real.sqrt (μ0 / μ1) : ℂ) * (Complex.I * (ω : ℂ) *
            ((Real.sqrt (μ0 * ε0) : ℂ) * (Complex.I * (η : ℂ) * (-q0 / ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2))) -
              ((μ1 * Real.sqrt (ε1 / μ0) : ℝ) : ℂ) * (Complex.I * (ξ : ℂ) * (-q1 / ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2)))))) +
        Complex.I * (η : ℂ) * ((Real.sqrt (μ0 / μ1) : ℂ) * (Complex.I * (ω : ℂ) *
            ((Real.sqrt (μ0 * ε0) : ℂ) * (Complex.I * (ξ : ℂ) * (-q0 / ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2))) -
              ((μ1 * Real.sqrt (ε1 / μ0) : ℝ) : ℂ) * -(Complex.I * (η : ℂ) * (-q1 / ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2)))))) =
        Complex.I * (ω : ℂ) * ((Real.sqrt (μ0 / μ1) : ℂ) * ((μ1 * Real.sqrt (ε1 / μ0) : ℝ) : ℂ)) * q1 := by
      field_simp [hρ2]
      ring_nf; simp [Complex.I_sq]
    rw [hcoeff, hsq_m]; ring
