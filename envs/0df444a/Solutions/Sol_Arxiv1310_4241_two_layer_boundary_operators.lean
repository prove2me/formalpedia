-- Prove2me | solution 1 for Arxiv1310_4241.two_layer_boundary_operators
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T19:21:50.027857+00:00
-- url     : https://prove2.me/submissions/db827ca7-f95b-41b6-97f0-4f1dbe55fd1b

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology Arxiv1310_4241

private lemma hasFDerivAt_expMode (α : ℂ) (ξ η : ℝ) (p : Space) :
    HasFDerivAt (fun q : Space => Complex.exp (α * (q 2 : ℂ)) * mode ξ η q)
      (Complex.exp (α * (p 2 : ℂ) + Complex.I * ((ξ : ℂ) * (p 0 : ℂ) + (η : ℂ) * (p 1 : ℂ))) •
        (α • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) +
          Complex.I • ((ξ : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) +
            (η : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)))))) p := by
  have h0 : HasFDerivAt (fun q : Space => ((q 0 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt
  have h1 : HasFDerivAt (fun q : Space => ((q 1 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).hasFDerivAt
  have h2 : HasFDerivAt (fun q : Space => ((q 2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt
  have harg := (h2.const_mul α).add (((h0.const_mul (ξ : ℂ)).add (h1.const_mul (η : ℂ))).const_mul Complex.I)
  have hexp := ((Complex.hasDerivAt_exp _).hasFDerivAt.restrictScalars ℝ).comp p harg
  have hexp' : HasFDerivAt (fun q : Space => Complex.exp (α * (q 2 : ℂ)) * mode ξ η q) _ p :=
    hexp.congr_of_eventuallyEq (Eventually.of_forall fun q => by
      simp [Function.comp, Complex.exp_add, mode, planeWave])
  refine hexp'.congr_fderiv ?_
  ext v
  simp [smul_eq_mul, mul_comm]

private lemma pd_const_expMode (i : Fin 3) (c α : ℂ) (ξ η : ℝ) (p : Space) :
    pd i (fun q => c * (Complex.exp (α * (q 2 : ℂ)) * mode ξ η q)) p =
      c * (match i with | 0 => Complex.I * ξ | 1 => Complex.I * η | 2 => α) *
        (Complex.exp (α * (p 2 : ℂ)) * mode ξ η p) := by
  have h := (hasFDerivAt_expMode α ξ η p).const_mul c
  have hproj : ∀ (k j : Fin 3),
      EuclideanSpace.proj (𝕜 := ℝ) k (EuclideanSpace.single j (1 : ℝ)) = if k = j then 1 else 0 := by
    intro k j
    change (EuclideanSpace.single j (1 : ℝ)).ofLp k = _
    simp [PiLp.single_apply]
  rw [pd, h.fderiv]
  fin_cases i <;>
    simp [Complex.exp_add, mode, planeWave, hproj] <;> ring

private lemma slpUp_eq (k : ℂ) (ξ η : ℝ) (c : ℂ) :
    slpUp k ξ η c =
      fun q => (c * ghat k ξ η 0) *
        (Complex.exp (-(sommerfeldRoot k ξ η) * (q 2 : ℂ)) * mode ξ η q) := by
  ext q
  simp only [slpUp, ghatUp, ghat, abs_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  ring

private lemma slpDown_eq (k : ℂ) (ξ η : ℝ) (c : ℂ) :
    slpDown k ξ η c =
      fun q => (c * ghat k ξ η 0) *
        (Complex.exp (sommerfeldRoot k ξ η * (q 2 : ℂ)) * mode ξ η q) := by
  ext q
  simp only [slpDown, ghatDown, ghat, abs_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  ring

private lemma debyeE_expMode (sqrtμ k g0 α : ℂ) (ξ η : ℝ) (j m : Fin 3 → ℂ) (r : ℂ)
    (hj2 : j 2 = 0) (hm2 : m 2 = 0) :
    debyeE sqrtμ k (fun c q => (c * g0) * (Complex.exp (α * (q 2 : ℂ)) * mode ξ η q)) j m r =
      fun p =>
        ![sqrtμ * g0 * (Complex.I * k * j 0 - Complex.I * ξ * r + α * m 1) *
            (Complex.exp (α * (p 2 : ℂ)) * mode ξ η p),
          sqrtμ * g0 * (Complex.I * k * j 1 - Complex.I * η * r - α * m 0) *
            (Complex.exp (α * (p 2 : ℂ)) * mode ξ η p),
          sqrtμ * g0 * (-α * r - (Complex.I * ξ * m 1 - Complex.I * η * m 0)) *
            (Complex.exp (α * (p 2 : ℂ)) * mode ξ η p)] := by
  ext p i
  simp only [debyeE, grad, curl, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [pd_const_expMode 0, pd_const_expMode 1, pd_const_expMode 2, hm2]
    ring
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [pd_const_expMode 1, pd_const_expMode 2, pd_const_expMode 0, hm2]
    ring
  · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [pd_const_expMode 2, pd_const_expMode 0, pd_const_expMode 1, hj2]
    ring

private lemma debyeH_expMode (sqrtε k g0 α : ℂ) (ξ η : ℝ) (j m : Fin 3 → ℂ) (q : ℂ)
    (hj2 : j 2 = 0) (hm2 : m 2 = 0) :
    debyeH sqrtε k (fun c p => (c * g0) * (Complex.exp (α * (p 2 : ℂ)) * mode ξ η p)) j m q =
      fun p =>
        ![sqrtε * g0 * (Complex.I * k * m 0 - Complex.I * ξ * q - α * j 1) *
            (Complex.exp (α * (p 2 : ℂ)) * mode ξ η p),
          sqrtε * g0 * (Complex.I * k * m 1 - Complex.I * η * q + α * j 0) *
            (Complex.exp (α * (p 2 : ℂ)) * mode ξ η p),
          sqrtε * g0 * (-α * q + (Complex.I * ξ * j 1 - Complex.I * η * j 0)) *
            (Complex.exp (α * (p 2 : ℂ)) * mode ξ η p)] := by
  ext p i
  simp only [debyeH, grad, curl, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [pd_const_expMode 0, pd_const_expMode 1, pd_const_expMode 2, hj2]
    ring
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [pd_const_expMode 1, pd_const_expMode 2, pd_const_expMode 0, hj2]
    ring
  · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [pd_const_expMode 2, pd_const_expMode 0, pd_const_expMode 1, hm2]
    ring

private lemma div_debyeE_expMode (sqrtμ k g0 α : ℂ) (ξ η : ℝ) (j m : Fin 3 → ℂ) (r : ℂ)
    (hj2 : j 2 = 0) (hm2 : m 2 = 0) (x y : ℝ) :
    tangentialDivergence
      (debyeE sqrtμ k (fun c q => (c * g0) * (Complex.exp (α * (q 2 : ℂ)) * mode ξ η q)) j m r)
      (pt x y 0) =
      sqrtμ * g0 *
        (Complex.I * k * (Complex.I * ξ * j 0 + Complex.I * η * j 1) +
          ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2) * r +
          α * (Complex.I * ξ * m 1 - Complex.I * η * m 0)) *
        planeWave ξ η x y := by
  rw [debyeE_expMode sqrtμ k g0 α ξ η j m r hj2 hm2]
  simp only [tangentialDivergence, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [pd_const_expMode 0, pd_const_expMode 1]
  have hpt : mode ξ η (pt x y 0) = planeWave ξ η x y := by simp [mode, pt]
  have hpt2 : (pt x y 0) 2 = 0 := by simp [pt]
  rw [hpt, hpt2]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  ring_nf; simp [Complex.I_sq]

private lemma div_debyeH_expMode (sqrtε k g0 α : ℂ) (ξ η : ℝ) (j m : Fin 3 → ℂ) (q : ℂ)
    (hj2 : j 2 = 0) (hm2 : m 2 = 0) (x y : ℝ) :
    tangentialDivergence
      (debyeH sqrtε k (fun c p => (c * g0) * (Complex.exp (α * (p 2 : ℂ)) * mode ξ η p)) j m q)
      (pt x y 0) =
      sqrtε * g0 *
        (Complex.I * k * (Complex.I * ξ * m 0 + Complex.I * η * m 1) +
          ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2) * q -
          α * (Complex.I * ξ * j 1 - Complex.I * η * j 0)) *
        planeWave ξ η x y := by
  rw [debyeH_expMode sqrtε k g0 α ξ η j m q hj2 hm2]
  simp only [tangentialDivergence, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [pd_const_expMode 0, pd_const_expMode 1]
  have hpt : mode ξ η (pt x y 0) = planeWave ξ η x y := by simp [mode, pt]
  have hpt2 : (pt x y 0) 2 = 0 := by simp [pt]
  rw [hpt, hpt2]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  ring_nf; simp [Complex.I_sq]

private lemma wavenumber_of_pos (ω a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    wavenumber ω (a : ℂ) (b : ℂ) = (ω : ℂ) * (Real.sqrt (a * b) : ℂ) := by
  rw [wavenumber]
  congr 1
  have hab : 0 ≤ a * b := mul_nonneg ha.le hb.le
  rw [← Complex.ofReal_mul, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hab]
  norm_cast
  rw [Real.sqrt_eq_rpow]

theorem solution (ω ε0 μ0 ε1 μ1 : ℝ) (hω : 0 < ω) (hε0 : 0 < ε0)
    (hμ0 : 0 < μ0) (hε1 : 0 < ε1) (hμ1 : 0 < μ1) (k0 k1 β0 β1 : ℂ)
    (hk0 : k0 = wavenumber ω ε0 μ0) (hk1 : k1 = wavenumber ω ε1 μ1) (ξ η : ℝ)
    (hξη : (ξ, η) ≠ (0, 0)) (hβ0def : β0 = sommerfeldRoot k0 ξ η)
    (hβ1def : β1 = sommerfeldRoot k1 ξ η) (hβ0 : β0 ≠ 0) (hβ1 : β1 ≠ 0)
    (r0 r1 q0 q1 : ℂ) (x y : ℝ) :
    laplaceSingleLayerOnMode ξ η
        (tangentialDivergence (twoLayerE0 ω ε0 μ0 ε1 μ1 ξ η r0 r1 q0 q1)) (pt x y 0) =
      (Real.sqrt μ0 : ℂ) * ghat 0 ξ η 0 * ghat k0 ξ η 0 *
        (((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k0 ^ 2) * r0 +
          Complex.I * ω * μ1 * (Real.sqrt (ε1 / μ0) : ℂ) * β0 * q1) * planeWave ξ η x y ∧
    laplaceSingleLayerOnMode ξ η
        (tangentialDivergence (twoLayerE1 ω ε0 μ0 ε1 μ1 ξ η r0 r1 q0 q1)) (pt x y 0) =
      (Real.sqrt μ1 : ℂ) * ghat 0 ξ η 0 * ghat k1 ξ η 0 *
        (((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k1 ^ 2) * r1 +
          Complex.I * ω * μ0 * (Real.sqrt (ε0 / μ1) : ℂ) * β1 * q0) * planeWave ξ η x y ∧
    laplaceSingleLayerOnMode ξ η
        (tangentialDivergence (twoLayerH0 ω ε0 μ0 ε1 μ1 ξ η r0 r1 q0 q1)) (pt x y 0) =
      (Real.sqrt ε0 : ℂ) * ghat 0 ξ η 0 * ghat k0 ξ η 0 *
        (((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k0 ^ 2) * q0 -
          Complex.I * ω * ε1 * (Real.sqrt (μ1 / ε0) : ℂ) * β0 * r1) * planeWave ξ η x y ∧
    laplaceSingleLayerOnMode ξ η
        (tangentialDivergence (twoLayerH1 ω ε0 μ0 ε1 μ1 ξ η r0 r1 q0 q1)) (pt x y 0) =
      (Real.sqrt ε1 : ℂ) * ghat 0 ξ η 0 * ghat k1 ξ η 0 *
        (((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k1 ^ 2) * q1 -
          Complex.I * ω * ε0 * (Real.sqrt (μ0 / ε1) : ℂ) * β1 * r0) * planeWave ξ η x y ∧
    (ε0 : ℂ) * twoLayerE0 ω ε0 μ0 ε1 μ1 ξ η r0 r1 q0 q1 (pt x y 0) 2 =
      ε0 * (Real.sqrt μ0 : ℂ) * ghat k0 ξ η 0 *
        (β0 * r0 + Complex.I * ω * μ1 * (Real.sqrt (ε1 / μ0) : ℂ) * q1) * planeWave ξ η x y ∧
    (ε1 : ℂ) * twoLayerE1 ω ε0 μ0 ε1 μ1 ξ η r0 r1 q0 q1 (pt x y 0) 2 =
      -(ε1 * (Real.sqrt μ1 : ℂ) * ghat k1 ξ η 0 *
        (β1 * r1 + Complex.I * ω * μ0 * (Real.sqrt (ε0 / μ1) : ℂ) * q0)) * planeWave ξ η x y ∧
    (μ0 : ℂ) * twoLayerH0 ω ε0 μ0 ε1 μ1 ξ η r0 r1 q0 q1 (pt x y 0) 2 =
      μ0 * (Real.sqrt ε0 : ℂ) * ghat k0 ξ η 0 *
        (β0 * q0 - Complex.I * ω * ε1 * (Real.sqrt (μ1 / ε0) : ℂ) * r1) * planeWave ξ η x y ∧
    (μ1 : ℂ) * twoLayerH1 ω ε0 μ0 ε1 μ1 ξ η r0 r1 q0 q1 (pt x y 0) 2 =
      -(μ1 * (Real.sqrt ε1 : ℂ) * ghat k1 ξ η 0 *
        (β1 * q1 - Complex.I * ω * ε0 * (Real.sqrt (μ0 / ε1) : ℂ) * r0)) * planeWave ξ η x y := by
  have hρ2_real : (0 : ℝ) < ξ ^ 2 + η ^ 2 := by
    by_contra h
    push Not at h
    exact hξη (Prod.ext (by nlinarith [sq_nonneg ξ, sq_nonneg η]) (by nlinarith [sq_nonneg ξ, sq_nonneg η]))
  have hρ2 : (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 ≠ 0 := by
    have : ((ξ ^ 2 + η ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ2_real.ne'
    simpa using this
  have hk0_val : k0 = (ω : ℂ) * (Real.sqrt (ε0 * μ0) : ℂ) := by
    rw [hk0, wavenumber_of_pos ω ε0 μ0 hε0 hμ0]
  have hk1_val : k1 = (ω : ℂ) * (Real.sqrt (ε1 * μ1) : ℂ) := by
    rw [hk1, wavenumber_of_pos ω ε1 μ1 hε1 hμ1]
  have hsq_e1 : (Real.sqrt (ε0 / ε1) : ℂ) * ((ε1 : ℂ) * (Real.sqrt (μ1 / ε0) : ℂ)) = (Real.sqrt (ε1 * μ1) : ℂ) := by
    exact_mod_cast (show Real.sqrt (ε0 / ε1) * (ε1 * Real.sqrt (μ1 / ε0)) = Real.sqrt (ε1 * μ1) by
      rw [Real.sqrt_div hε0.le, Real.sqrt_div hμ1.le, Real.sqrt_mul hε1.le]
      have h1 : 0 < Real.sqrt ε0 := Real.sqrt_pos.mpr hε0
      have h2 : 0 < Real.sqrt ε1 := Real.sqrt_pos.mpr hε1
      have hsq : Real.sqrt ε1 * Real.sqrt ε1 = ε1 := Real.mul_self_sqrt hε1.le
      field_simp [h1.ne', h2.ne']; nlinarith [hsq])
  have hsq_m1 : (Real.sqrt (μ0 / μ1) : ℂ) * ((μ1 : ℂ) * (Real.sqrt (ε1 / μ0) : ℂ)) = (Real.sqrt (ε1 * μ1) : ℂ) := by
    exact_mod_cast (show Real.sqrt (μ0 / μ1) * (μ1 * Real.sqrt (ε1 / μ0)) = Real.sqrt (ε1 * μ1) by
      rw [Real.sqrt_div hμ0.le, Real.sqrt_div hε1.le, Real.sqrt_mul hε1.le]
      have h1 : 0 < Real.sqrt μ0 := Real.sqrt_pos.mpr hμ0
      have h2 : 0 < Real.sqrt μ1 := Real.sqrt_pos.mpr hμ1
      have hsq : Real.sqrt μ1 * Real.sqrt μ1 = μ1 := Real.mul_self_sqrt hμ1.le
      field_simp [h1.ne', h2.ne']; nlinarith [hsq])
  have hsq_e0 : (Real.sqrt (ε0 / ε1) : ℂ) * (Real.sqrt (μ0 * ε0) : ℂ) = (ε0 : ℂ) * (Real.sqrt (μ0 / ε1) : ℂ) := by
    exact_mod_cast (show Real.sqrt (ε0 / ε1) * Real.sqrt (μ0 * ε0) = ε0 * Real.sqrt (μ0 / ε1) by
      rw [Real.sqrt_div hε0.le, Real.sqrt_mul hμ0.le, Real.sqrt_div hμ0.le]
      have h2 : 0 < Real.sqrt ε1 := Real.sqrt_pos.mpr hε1
      have hsq : Real.sqrt ε0 * Real.sqrt ε0 = ε0 := Real.mul_self_sqrt hε0.le
      field_simp [h2.ne']; nlinarith [hsq])
  have hsq_m0 : (Real.sqrt (μ0 / μ1) : ℂ) * (Real.sqrt (μ0 * ε0) : ℂ) = (μ0 : ℂ) * (Real.sqrt (ε0 / μ1) : ℂ) := by
    exact_mod_cast (show Real.sqrt (μ0 / μ1) * Real.sqrt (μ0 * ε0) = μ0 * Real.sqrt (ε0 / μ1) by
      rw [Real.sqrt_div hμ0.le, Real.sqrt_mul hμ0.le, Real.sqrt_div hε0.le]
      have h2 : 0 < Real.sqrt μ1 := Real.sqrt_pos.mpr hμ1
      have hsq : Real.sqrt μ0 * Real.sqrt μ0 = μ0 := Real.mul_self_sqrt hμ0.le
      field_simp [h2.ne']; nlinarith [hsq])
  have hcomm0 : (Real.sqrt (μ0 * ε0) : ℂ) = (Real.sqrt (ε0 * μ0) : ℂ) := by rw [mul_comm]
  set J0 := twoLayerJ0 ω ε0 μ0 ε1 μ1 ξ η r0 r1
  set J1 := twoLayerJ1 ω ε0 μ0 ε1 μ1 ξ η r0 r1
  set M0 := twoLayerM0 ω ε0 μ0 ε1 μ1 ξ η q0 q1
  set M1 := twoLayerM1 ω ε0 μ0 ε1 μ1 ξ η q0 q1
  have hJ0_2 : J0 2 = 0 := by simp [J0, twoLayerJ0, gradInvLap, nCross]
  have hJ1_2 : J1 2 = 0 := by simp [J1, twoLayerJ1, nCross]
  have hM0_2 : M0 2 = 0 := by simp [M0, twoLayerM0, gradInvLap, nCross]
  have hM1_2 : M1 2 = 0 := by simp [M1, twoLayerM1, nCross]
  have hdivJ0 : Complex.I * ξ * J0 0 + Complex.I * η * J0 1 = Complex.I * k0 * r0 := by
    rw [hk0_val]
    simp only [J0, twoLayerJ0, gradInvLap, nCross, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, hcomm0]
    field_simp [hρ2]; ring_nf; simp [Complex.I_sq]
  have hcurlJ0 : Complex.I * ξ * J0 1 - Complex.I * η * J0 0 =
      -(Complex.I * ω * ε1 * (Real.sqrt (μ1 / ε0) : ℂ) * r1) := by
    simp only [J0, twoLayerJ0, gradInvLap, nCross, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast; field_simp [hρ2]; ring_nf; simp [Complex.I_sq]; ring
  have hdivM0 : Complex.I * ξ * M0 0 + Complex.I * η * M0 1 = Complex.I * k0 * q0 := by
    rw [hk0_val]
    simp only [M0, twoLayerM0, gradInvLap, nCross, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, hcomm0]
    field_simp [hρ2]; ring_nf; simp [Complex.I_sq]
  have hcurlM0 : Complex.I * ξ * M0 1 - Complex.I * η * M0 0 =
      -(Complex.I * ω * μ1 * (Real.sqrt (ε1 / μ0) : ℂ) * q1) := by
    simp only [M0, twoLayerM0, gradInvLap, nCross, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast; field_simp [hρ2]; ring_nf; simp [Complex.I_sq]; ring
  have hdivJ1 : Complex.I * ξ * J1 0 + Complex.I * η * J1 1 = Complex.I * k1 * r1 := by
    rw [hk1_val]
    simp only [J1, twoLayerJ1, nCross, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    have : Complex.I * (ξ : ℂ) * -((Real.sqrt (ε0 / ε1) : ℂ) * J0 1) +
        Complex.I * (η : ℂ) * ((Real.sqrt (ε0 / ε1) : ℂ) * J0 0) =
        -(Real.sqrt (ε0 / ε1) : ℂ) * (Complex.I * ξ * J0 1 - Complex.I * η * J0 0) := by ring
    rw [this, hcurlJ0]
    calc -(Real.sqrt (ε0 / ε1) : ℂ) * -(Complex.I * (ω : ℂ) * (ε1 : ℂ) * (Real.sqrt (μ1 / ε0) : ℂ) * r1)
        = Complex.I * (ω : ℂ) * ((Real.sqrt (ε0 / ε1) : ℂ) * ((ε1 : ℂ) * (Real.sqrt (μ1 / ε0) : ℂ))) * r1 := by ring
      _ = Complex.I * ((ω : ℂ) * (Real.sqrt (ε1 * μ1) : ℂ)) * r1 := by rw [hsq_e1]; ring
  have hcurlJ1 : Complex.I * ξ * J1 1 - Complex.I * η * J1 0 =
      Complex.I * ω * ε0 * (Real.sqrt (μ0 / ε1) : ℂ) * r0 := by
    simp only [J1, twoLayerJ1, nCross, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    have : Complex.I * (ξ : ℂ) * ((Real.sqrt (ε0 / ε1) : ℂ) * J0 0) -
        Complex.I * (η : ℂ) * -((Real.sqrt (ε0 / ε1) : ℂ) * J0 1) =
        (Real.sqrt (ε0 / ε1) : ℂ) * (Complex.I * ξ * J0 0 + Complex.I * η * J0 1) := by ring
    rw [this, hdivJ0, hk0_val, ← hcomm0]
    calc (Real.sqrt (ε0 / ε1) : ℂ) * (Complex.I * ((ω : ℂ) * (Real.sqrt (μ0 * ε0) : ℂ)) * r0)
        = Complex.I * (ω : ℂ) * ((Real.sqrt (ε0 / ε1) : ℂ) * (Real.sqrt (μ0 * ε0) : ℂ)) * r0 := by ring
      _ = Complex.I * (ω : ℂ) * (ε0 : ℂ) * (Real.sqrt (μ0 / ε1) : ℂ) * r0 := by rw [hsq_e0]; ring
  have hdivM1 : Complex.I * ξ * M1 0 + Complex.I * η * M1 1 = Complex.I * k1 * q1 := by
    rw [hk1_val]
    simp only [M1, twoLayerM1, nCross, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    have : Complex.I * (ξ : ℂ) * -((Real.sqrt (μ0 / μ1) : ℂ) * M0 1) +
        Complex.I * (η : ℂ) * ((Real.sqrt (μ0 / μ1) : ℂ) * M0 0) =
        -(Real.sqrt (μ0 / μ1) : ℂ) * (Complex.I * ξ * M0 1 - Complex.I * η * M0 0) := by ring
    rw [this, hcurlM0]
    calc -(Real.sqrt (μ0 / μ1) : ℂ) * -(Complex.I * (ω : ℂ) * (μ1 : ℂ) * (Real.sqrt (ε1 / μ0) : ℂ) * q1)
        = Complex.I * (ω : ℂ) * ((Real.sqrt (μ0 / μ1) : ℂ) * ((μ1 : ℂ) * (Real.sqrt (ε1 / μ0) : ℂ))) * q1 := by ring
      _ = Complex.I * ((ω : ℂ) * (Real.sqrt (ε1 * μ1) : ℂ)) * q1 := by rw [hsq_m1]; ring
  have hcurlM1 : Complex.I * ξ * M1 1 - Complex.I * η * M1 0 =
      Complex.I * ω * μ0 * (Real.sqrt (ε0 / μ1) : ℂ) * q0 := by
    simp only [M1, twoLayerM1, nCross, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    have : Complex.I * (ξ : ℂ) * ((Real.sqrt (μ0 / μ1) : ℂ) * M0 0) -
        Complex.I * (η : ℂ) * -((Real.sqrt (μ0 / μ1) : ℂ) * M0 1) =
        (Real.sqrt (μ0 / μ1) : ℂ) * (Complex.I * ξ * M0 0 + Complex.I * η * M0 1) := by ring
    rw [this, hdivM0, hk0_val, ← hcomm0]
    calc (Real.sqrt (μ0 / μ1) : ℂ) * (Complex.I * ((ω : ℂ) * (Real.sqrt (μ0 * ε0) : ℂ)) * q0)
        = Complex.I * (ω : ℂ) * ((Real.sqrt (μ0 / μ1) : ℂ) * (Real.sqrt (μ0 * ε0) : ℂ)) * q0 := by ring
      _ = Complex.I * (ω : ℂ) * (μ0 : ℂ) * (Real.sqrt (ε0 / μ1) : ℂ) * q0 := by rw [hsq_m0]; ring
  have hpt : mode ξ η (pt x y 0) = planeWave ξ η x y := by simp [mode, pt]
  have hpt2 : (pt x y 0) 2 = 0 := by simp [pt]
  have hslpUp0 : slpUp k0 ξ η = fun c q => (c * ghat k0 ξ η 0) * (Complex.exp (-β0 * (q 2 : ℂ)) * mode ξ η q) := by
    ext c q; rw [slpUp_eq, hβ0def]
  have hslpDown1 : slpDown k1 ξ η = fun c q => (c * ghat k1 ξ η 0) * (Complex.exp (β1 * (q 2 : ℂ)) * mode ξ η q) := by
    ext c q; rw [slpDown_eq, hβ1def]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [laplaceSingleLayerOnMode, twoLayerE0, ← hk0]
    rw [hslpUp0, div_debyeE_expMode _ _ _ _ _ _ J0 M0 r0 hJ0_2 hM0_2, hdivJ0, hcurlM0]
    ring_nf; simp [Complex.I_sq]; ring
  · simp only [laplaceSingleLayerOnMode, twoLayerE1, ← hk1]
    rw [hslpDown1, div_debyeE_expMode _ _ _ _ _ _ J1 M1 r1 hJ1_2 hM1_2, hdivJ1, hcurlM1]
    ring_nf; simp [Complex.I_sq]; ring
  · simp only [laplaceSingleLayerOnMode, twoLayerH0, ← hk0]
    rw [hslpUp0, div_debyeH_expMode _ _ _ _ _ _ J0 M0 q0 hJ0_2 hM0_2, hdivM0, hcurlJ0]
    ring_nf; simp [Complex.I_sq]; ring
  · simp only [laplaceSingleLayerOnMode, twoLayerH1, ← hk1]
    rw [hslpDown1, div_debyeH_expMode _ _ _ _ _ _ J1 M1 q1 hJ1_2 hM1_2, hdivM1, hcurlJ1]
    ring_nf; simp [Complex.I_sq]; ring
  · simp only [twoLayerE0, ← hk0]
    rw [hslpUp0, debyeE_expMode _ _ _ _ _ _ J0 M0 r0 hJ0_2 hM0_2]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hpt, hpt2,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, hcurlM0]
    ring
  · simp only [twoLayerE1, ← hk1]
    rw [hslpDown1, debyeE_expMode _ _ _ _ _ _ J1 M1 r1 hJ1_2 hM1_2]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hpt, hpt2,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, hcurlM1]
    ring
  · simp only [twoLayerH0, ← hk0]
    rw [hslpUp0, debyeH_expMode _ _ _ _ _ _ J0 M0 q0 hJ0_2 hM0_2]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hpt, hpt2,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, hcurlJ0]
    ring
  · simp only [twoLayerH1, ← hk1]
    rw [hslpDown1, debyeH_expMode _ _ _ _ _ _ J1 M1 q1 hJ1_2 hM1_2]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hpt, hpt2,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, hcurlJ1]
    ring
