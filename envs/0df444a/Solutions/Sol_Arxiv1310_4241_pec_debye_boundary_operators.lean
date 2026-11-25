-- Prove2me | solution 1 for Arxiv1310_4241.pec_debye_boundary_operators
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T19:21:31.306488+00:00
-- url     : https://prove2.me/submissions/77d23aeb-a6f8-4d1c-9be3-a78de46cd896

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

private lemma debyeE_slpUp (sqrtμ k : ℂ) (ξ η : ℝ) (j m : Fin 3 → ℂ) (r : ℂ)
    (hj2 : j 2 = 0) (hm2 : m 2 = 0) :
    debyeE sqrtμ k (slpUp k ξ η) j m r =
      fun p =>
        ![sqrtμ * ghat k ξ η 0 * (Complex.I * k * j 0 - Complex.I * ξ * r - sommerfeldRoot k ξ η * m 1) *
            (Complex.exp (-(sommerfeldRoot k ξ η) * (p 2 : ℂ)) * mode ξ η p),
          sqrtμ * ghat k ξ η 0 * (Complex.I * k * j 1 - Complex.I * η * r + sommerfeldRoot k ξ η * m 0) *
            (Complex.exp (-(sommerfeldRoot k ξ η) * (p 2 : ℂ)) * mode ξ η p),
          sqrtμ * ghat k ξ η 0 * (sommerfeldRoot k ξ η * r - (Complex.I * ξ * m 1 - Complex.I * η * m 0)) *
            (Complex.exp (-(sommerfeldRoot k ξ η) * (p 2 : ℂ)) * mode ξ η p)] := by
  ext p i
  simp only [debyeE, grad, curl, slpUp_eq, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
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

private lemma debyeH_slpUp_2 (sqrtε k : ℂ) (ξ η : ℝ) (j m : Fin 3 → ℂ) (q : ℂ)
    (hm2 : m 2 = 0) (p : Space) :
    debyeH sqrtε k (slpUp k ξ η) j m q p 2 =
      sqrtε * ghat k ξ η 0 * (sommerfeldRoot k ξ η * q + (Complex.I * ξ * j 1 - Complex.I * η * j 0)) *
        (Complex.exp (-(sommerfeldRoot k ξ η) * (p 2 : ℂ)) * mode ξ η p) := by
  simp only [debyeH, grad, curl, slpUp_eq, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [pd_const_expMode 2, pd_const_expMode 0, pd_const_expMode 1, hm2]
  ring

theorem solution (ω : ℝ) (ε μ k : ℂ) (hkdef : k = wavenumber ω ε μ)
    (hk : IsCausalWavenumber k) (ξ η : ℝ) (hξη : (ξ, η) ≠ (0, 0))
    (hβ : sommerfeldRoot k ξ η ≠ 0) (r q : ℂ) (x y : ℝ) :
    laplaceSingleLayerOnMode ξ η (tangentialDivergence (pecE ω ε μ ξ η r q)) (pt x y 0) =
      csqrt μ * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2 - Complex.I * k * sommerfeldRoot k ξ η) *
        ghat 0 ξ η 0 * ghat k ξ η 0 * r * planeWave ξ η x y ∧
    pecH ω ε μ ξ η r q (pt x y 0) 2 =
      csqrt ε * (sommerfeldRoot k ξ η - Complex.I * k) * ghat k ξ η 0 * q * planeWave ξ η x y := by
  have hρ2_real : (0 : ℝ) < ξ ^ 2 + η ^ 2 := by
    by_contra h
    push Not at h
    exact hξη (Prod.ext (by nlinarith [sq_nonneg ξ, sq_nonneg η]) (by nlinarith [sq_nonneg ξ, sq_nonneg η]))
  have hρ2 : (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 ≠ 0 := by
    have : ((ξ ^ 2 + η ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ2_real.ne'
    simpa using this
  have hj2 : pecJ k ξ η r q 2 = 0 := by simp [pecJ, gradInvLap, nCross]
  have hm2 : nCross (pecJ k ξ η r q) 2 = 0 := by simp [nCross]
  have hpt : mode ξ η (pt x y 0) = planeWave ξ η x y := by simp [mode, pt]
  have hpt2 : (pt x y 0) 2 = 0 := by simp [pt]
  subst hkdef
  set k := wavenumber ω ε μ
  set β := sommerfeldRoot k ξ η
  constructor
  · simp only [laplaceSingleLayerOnMode, tangentialDivergence, pecE]
    rw [debyeE_slpUp (csqrt μ) k ξ η _ _ r hj2 hm2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [pd_const_expMode 0, pd_const_expMode 1, hpt, hpt2]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    simp only [pecJ, gradInvLap, nCross, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hρ2]
    ring_nf
    simp [Complex.I_sq, pow_succ]
    ring
  · simp only [pecH]
    rw [debyeH_slpUp_2 (csqrt ε) k ξ η _ _ q hm2, hpt, hpt2]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    simp only [pecJ, gradInvLap, nCross, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hρ2]
    ring_nf
    simp [Complex.I_sq, pow_succ]
    ring
