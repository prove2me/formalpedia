-- Prove2me | Definitions.Def_SpherePacking
-- name    : SpherePacking
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-19T10:54:31.198+00:00
-- url     : https://prove2.me/theorems/6a34e2a4-2ef7-42fb-b76b-d71963956379
-- title:
--   SpherePacking
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
set_option autoImplicit true
namespace CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory
open scoped FourierTransform SchwartzMap Topology
abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev TestFunction (d : ℕ) := 𝓢(Euclidean d, ℂ)
def IsRealValued {d : ℕ} (f : TestFunction d) : Prop :=
  ∀ x : Euclidean d, (f x).im = 0
def IsRadial {d : ℕ} (f : TestFunction d) : Prop :=
  ∀ x y : Euclidean d, ‖x‖ = ‖y‖ → f x = f y
structure Admissible (d : ℕ) where
  function : TestFunction d
  real : IsRealValued function
  radial : IsRadial function
  fourier_real : IsRealValued (𝓕 function)
  fourier_nonneg : ∀ ξ : Euclidean d, 0 ≤ ((𝓕 function) ξ).re
  fourier_zero_pos : 0 < ((𝓕 function) (0 : Euclidean d)).re
  outside_nonpos :
    ∀ x : Euclidean d, 1 ≤ ‖x‖ → (function x).re ≤ 0
def unitBallVolume (d : ℕ) : ℝ :=
  Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)
theorem unitBallVolume_pos (d : ℕ) : 0 < unitBallVolume d := by
  unfold unitBallVolume
  exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by positivity))
def quotient {d : ℕ} (f : Admissible d) : ℝ :=
  (f.function (0 : Euclidean d)).re /
    ((𝓕 f.function) (0 : Euclidean d)).re
def quotientSet (d : ℕ) : Set ℝ :=
  Set.range (quotient (d := d))
def linearProgram (d : ℕ) : ℝ :=
  unitBallVolume d / (2 : ℝ) ^ d * sInf (quotientSet d)
def normalizedCost {d : ℕ} (f : Admissible d) : ℝ :=
  quotient f ^ ((d : ℝ)⁻¹) / Real.sqrt (d : ℝ)
def normalizedProgram (d : ℕ) : ℝ :=
  sInf (Set.range (normalizedCost (d := d)))
def criticalRadius : ℝ := (Real.pi)⁻¹
def criticalPackingBase : ℝ :=
  Real.sqrt (Real.exp 1 / (2 * Real.pi))
def criticalBinaryExponent : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1)
def SharpQuotientAsymptotic : Prop :=
  Tendsto normalizedProgram atTop (nhds criticalRadius)
def SharpLogAsymptotic : Prop :=
  Tendsto (fun d : ℕ => Real.log (linearProgram d) / (d : ℝ))
    atTop (nhds ((1 / 2 : ℝ) * Real.log (Real.exp 1 / (2 * Real.pi))))
def SharpPackingRootAsymptotic : Prop :=
  Tendsto (fun d : ℕ => (linearProgram d) ^ ((d : ℝ)⁻¹))
    atTop (nhds criticalPackingBase)
end
noncomputable section
def shortCutoff (ε : ℝ) : ℝ := ε ^ 3
def shortEndpoint (ε : ℝ) : ℝ := 10 * Real.log (1 / ε)
def shellLocation (ε : ℝ) : ℝ := ε⁻¹ ^ 3
def shellWeight (ε : ℝ) : ℝ :=
  Real.exp (-(3 : ℝ) * ε * shellLocation ε / 8)
def shortMargin (ε a : ℝ) : ℝ := 1 - 10 * ε * (1 + a)
def beta (ε : ℝ) : ℝ := ε / 4
def plusPolynomial (ε : ℝ) (z : ℂ) : ℂ :=
  1 + z ^ 2 + (beta ε : ℂ) + Complex.I * z * (1 + z ^ 2)
def minusPolynomial (ε : ℝ) (z : ℂ) : ℂ :=
  1 + z ^ 2 + (beta ε : ℂ) - Complex.I * z * (1 + z ^ 2)
theorem shellWeight_pos (ε : ℝ) : 0 < shellWeight ε := by
  exact Real.exp_pos _
theorem beta_pos {ε : ℝ} (hε : 0 < ε) : 0 < beta ε := by
  exact div_pos hε (by norm_num)
theorem plusPolynomial_imaginary (ε u : ℝ) :
    plusPolynomial ε (Complex.I * (u : ℂ)) =
      ((beta ε + (1 - u) ^ 2 * (1 + u) : ℝ) : ℂ) := by
  push_cast
  try dsimp [plusPolynomial]
  ring_nf
  simp [Complex.I_sq]; ring
theorem minusPolynomial_imaginary (ε u : ℝ) :
    minusPolynomial ε (Complex.I * (u : ℂ)) =
      ((beta ε + (1 - u) * (1 + u) ^ 2 : ℝ) : ℂ) := by
  push_cast
  try dsimp [minusPolynomial]
  ring_nf
  simp [Complex.I_sq]; ring
end
noncomputable section
open MeasureTheory
open scoped FourierTransform
def mellinFrequency (ℓ : ℝ) (profile : ℝ → ℂ) (t : ℝ) : ℂ :=
  mellin profile ((ℓ : ℂ) - Complex.I * (t : ℂ))
theorem mellinFrequency_eq_fourier
    (ℓ : ℝ) (profile : ℝ → ℂ) (t : ℝ) :
    mellinFrequency ℓ profile t =
      (𝓕 (fun u : ℝ =>
        Real.exp (-ℓ * u) • profile (Real.exp (-u))))
          (-t / (2 * Real.pi)) := by
  unfold mellinFrequency
  simpa using!
    (mellin_eq_fourier profile
      (s := (ℓ : ℂ) - Complex.I * (t : ℂ)))
def mellinMultiplier (ℓ t : ℝ) : ℂ :=
  Complex.exp
      (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ)) *
    Complex.Gamma (((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2) /
    Complex.Gamma (((ℓ : ℂ) + Complex.I * (t : ℂ)) / 2)
theorem mellinDenominator_re_pos {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    0 < (((ℓ : ℂ) + Complex.I * (t : ℂ)) / 2).re := by
  simpa using! (half_pos hℓ)
theorem mellinMultiplier_denominator_ne_zero
    {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    Complex.Gamma (((ℓ : ℂ) + Complex.I * (t : ℂ)) / 2) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (mellinDenominator_re_pos hℓ t)
theorem gamma_add_nat_eq_product (z : ℂ)
    (hz : ∀ j : ℕ, z + (j : ℂ) ≠ 0) (k : ℕ) :
    Complex.Gamma (z + (k : ℂ)) =
      Complex.Gamma z * ∏ j ∈ Finset.range k, (z + (j : ℂ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc,
      Complex.Gamma_add_one (z + (k : ℂ)) (hz k), ih,
      Finset.prod_range_succ]
    ring
end
noncomputable section
open Filter MeasureTheory
open scoped FourierTransform SchwartzMap
def IsEven {d : ℕ} (f : TestFunction d) : Prop :=
  ∀ x : Euclidean d, f (-x) = f x
theorem IsRadial.even {d : ℕ} {f : TestFunction d}
    (hf : IsRadial f) : IsEven f := by
  intro x
  exact hf (-x) x (by simp)
theorem fourierInv_apply_zero {d : ℕ} (f : TestFunction d) :
    (𝓕⁻ f : TestFunction d) (0 : Euclidean d) =
      ∫ x : Euclidean d, f x := by
  calc
    (𝓕⁻ f : TestFunction d) (0 : Euclidean d) =
        (𝓕⁻ (f : Euclidean d → ℂ)) (0 : Euclidean d) :=
      congrFun (SchwartzMap.fourierInv_coe f) 0
    _ = ∫ x : Euclidean d, f x := by
      rw [Real.fourierInv_eq]
      simp
theorem admissible_zero_pos {d : ℕ} (f : Admissible d) :
    0 < (f.function (0 : Euclidean d)).re := by
  have hpositive : 0 < ∫ x : Euclidean d, ((𝓕 f.function) x).re := by
    exact integral_pos_of_integrable_nonneg_nonzero
      (Complex.continuous_re.comp (𝓕 f.function).continuous)
      (𝓕 f.function).integrable.re
      f.fourier_nonneg f.fourier_zero_pos.ne'
  have hinversion :
      (∫ x : Euclidean d, (𝓕 f.function) x) =
        f.function (0 : Euclidean d) := by
    have h := congrArg (fun g : TestFunction d => g (0 : Euclidean d))
      (show (𝓕⁻ (𝓕 f.function) : TestFunction d) = f.function from
        FourierTransform.fourierInv_fourier_eq f.function)
    simpa only [fourierInv_apply_zero] using! h
  calc
    (0 : ℝ) < (∫ x : Euclidean d, ((𝓕 f.function) x).re) := hpositive
    _ = (∫ x : Euclidean d, (𝓕 f.function) x).re :=
      integral_re (𝓕 f.function).integrable
    _ = (f.function (0 : Euclidean d)).re :=
      congrArg Complex.re hinversion
theorem fourier_sq_apply {d : ℕ} (f : TestFunction d) (x : Euclidean d) :
    ((𝓕 (𝓕 f) : TestFunction d) x) = f (-x) := by
  have hinv := congrArg (fun g : TestFunction d => g (-x))
    (show (𝓕⁻ (𝓕 f) : TestFunction d) = f from
      FourierTransform.fourierInv_fourier_eq f)
  have hchange :
      ((𝓕⁻ (𝓕 f) : TestFunction d) (-x)) =
        ((𝓕 (𝓕 f) : TestFunction d) x) := by
    calc
      ((𝓕⁻ (𝓕 f) : TestFunction d) (-x)) =
          (𝓕⁻ ((𝓕 f : TestFunction d) : Euclidean d → ℂ)) (-x) :=
        congrFun (SchwartzMap.fourierInv_coe (𝓕 f)) (-x)
      _ = (𝓕 ((𝓕 f : TestFunction d) : Euclidean d → ℂ)) x := by
        rw [Real.fourierInv_eq_fourier_neg]
        simp
      _ = ((𝓕 (𝓕 f) : TestFunction d) x) :=
        (congrFun (SchwartzMap.fourier_coe (𝓕 f)) x).symm
  exact hchange ▸ hinv
theorem fourier_sq_of_radial {d : ℕ} (f : TestFunction d)
    (hf : IsRadial f) : (𝓕 (𝓕 f) : TestFunction d) = f := by
  ext x
  rw [fourier_sq_apply]
  exact hf.even x
def antiFourierPart {d : ℕ} (f : TestFunction d) : TestFunction d :=
  𝓕 f - f
theorem fourier_antiFourierPart {d : ℕ} (f : TestFunction d)
    (hf : IsRadial f) :
    (𝓕 (antiFourierPart f) : TestFunction d) = -antiFourierPart f := by
  rw [antiFourierPart, sub_eq_add_neg, FourierTransform.fourier_add,
    FourierTransform.fourier_neg, fourier_sq_of_radial f hf]
  simp
theorem antiFourierPart_zero {d : ℕ} (f : TestFunction d)
    (hbalance : (𝓕 f : TestFunction d) (0 : Euclidean d) = f 0) :
    antiFourierPart f (0 : Euclidean d) = 0 := by
  change (𝓕 f : TestFunction d) 0 - f 0 = 0
  exact sub_eq_zero.mpr hbalance
theorem antiFourierPart_nonneg_of_signs {d : ℕ}
    (f : TestFunction d) (R : ℝ)
    (hfourier : ∀ x : Euclidean d, 0 ≤ ((𝓕 f) x).re)
    (houtside : ∀ x : Euclidean d, R ≤ ‖x‖ → (f x).re ≤ 0)
    (x : Euclidean d) (hx : R ≤ ‖x‖) :
    0 ≤ (antiFourierPart f x).re := by
  change 0 ≤ ((𝓕 f) x).re - (f x).re
  linarith [hfourier x, houtside x hx]
structure AntiFourierWitness (d : ℕ) (R : ℝ) where
  function : TestFunction d
  real : IsRealValued function
  radial : IsRadial function
  nonzero : function ≠ 0
  anti_fourier : (𝓕 function : TestFunction d) = -function
  zero_value : function (0 : Euclidean d) = 0
  eventually_nonneg :
    ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ (function x).re
def UniformAntiFourierSignRadius : Prop :=
  ∀ c : ℝ, 0 < c → c < criticalRadius →
    ∀ᶠ d : ℕ in atTop,
      IsEmpty (AntiFourierWitness d (c * Real.sqrt (d : ℝ)))
end
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace ENNReal NNReal
def dilationEquiv (d : ℕ) (a : ℝ) (ha : a ≠ 0) :
    Euclidean d ≃L[ℝ] Euclidean d :=
  (LinearEquiv.smulOfNeZero ℝ (Euclidean d) a ha).toContinuousLinearEquiv
@[simp] theorem dilationEquiv_apply (d : ℕ) (a : ℝ) (ha : a ≠ 0)
    (x : Euclidean d) : dilationEquiv d a ha x = a • x := by
  rfl
def dilate {d : ℕ} (f : TestFunction d) (a : ℝ) (ha : 0 < a) :
    TestFunction d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (dilationEquiv d a ha.ne') f
@[simp] theorem dilate_apply {d : ℕ} (f : TestFunction d)
    (a : ℝ) (ha : 0 < a) (x : Euclidean d) :
    dilate f a ha x = f (a • x) := by
  rfl
@[simp] theorem dilate_zero {d : ℕ} (f : TestFunction d)
    (a : ℝ) (ha : 0 < a) :
    dilate f a ha (0 : Euclidean d) = f 0 := by
  simp
theorem IsRealValued.dilate {d : ℕ} {f : TestFunction d}
    (hf : IsRealValued f) (a : ℝ) (ha : 0 < a) :
    IsRealValued (dilate f a ha) := by
  intro x
  exact hf (a • x)
theorem IsRadial.dilate {d : ℕ} {f : TestFunction d}
    (hf : IsRadial f) (a : ℝ) (ha : 0 < a) :
    IsRadial (dilate f a ha) := by
  intro x y hxy
  apply hf
  simp [norm_smul, hxy]
theorem fourier_dilate_apply {d : ℕ} (f : TestFunction d)
    (a : ℝ) (ha : 0 < a) (ξ : Euclidean d) :
    ((𝓕 (dilate f a ha) : TestFunction d) ξ) =
      (a ^ d)⁻¹ • ((𝓕 f : TestFunction d) (a⁻¹ • ξ)) := by
  have hinner (x : Euclidean d) :
      @inner ℝ (Euclidean d) _ (a • x) (a⁻¹ • ξ) =
        @inner ℝ (Euclidean d) _ x ξ := by
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  calc
    ((𝓕 (dilate f a ha) : TestFunction d) ξ) =
        (𝓕 ((dilate f a ha : TestFunction d) : Euclidean d → ℂ)) ξ :=
      congrFun (SchwartzMap.fourier_coe (dilate f a ha)) ξ
    _ = ∫ x : Euclidean d,
          Complex.exp
            ((↑(-2 * Real.pi * @inner ℝ (Euclidean d) _ x ξ) : ℂ) * Complex.I) •
              f (a • x) := by
      rw [Real.fourier_eq']
      rfl
    _ = ∫ x : Euclidean d,
          (fun y : Euclidean d =>
            Complex.exp
              ((↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ y (a⁻¹ • ξ)) : ℂ) * Complex.I) • f y)
            (a • x) := by
      congr 1
      funext x
      simp only [hinner x]
    _ = (a ^ d)⁻¹ •
          ∫ y : Euclidean d,
            Complex.exp
              ((↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ y (a⁻¹ • ξ)) : ℂ) * Complex.I) • f y := by
      simpa [finrank_euclideanSpace] using!
        (MeasureTheory.Measure.integral_comp_smul_of_nonneg
          (volume : Measure (Euclidean d))
          (fun y : Euclidean d =>
            Complex.exp
              ((↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ y (a⁻¹ • ξ)) : ℂ) * Complex.I) • f y)
          a (hR := ha.le))
    _ = (a ^ d)⁻¹ • ((𝓕 f : TestFunction d) (a⁻¹ • ξ)) := by
      rw [← Real.fourier_eq']
      rw [SchwartzMap.fourier_coe]
theorem fourier_dilate_zero {d : ℕ} (f : TestFunction d)
    (a : ℝ) (ha : 0 < a) :
    ((𝓕 (dilate f a ha) : TestFunction d) (0 : Euclidean d)) =
      (a ^ d)⁻¹ • ((𝓕 f : TestFunction d) (0 : Euclidean d)) := by
  simpa using! fourier_dilate_apply f a ha 0
def balancingScale {d : ℕ} (f : Admissible d) : ℝ :=
  (((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re /
      (f.function (0 : Euclidean d)).re) ^ ((d : ℝ)⁻¹)
theorem balancingScale_pos {d : ℕ} (f : Admissible d) :
    0 < balancingScale f := by
  unfold balancingScale
  exact Real.rpow_pos_of_pos
    (div_pos f.fourier_zero_pos (admissible_zero_pos f)) _
theorem balancingScale_pow {d : ℕ} (f : Admissible d) (hd : 0 < d) :
    balancingScale f ^ d =
      ((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re /
        (f.function (0 : Euclidean d)).re := by
  unfold balancingScale
  exact Real.rpow_inv_natCast_pow
    (div_pos f.fourier_zero_pos (admissible_zero_pos f)).le
    (Nat.ne_of_gt hd)
def balancedFunction {d : ℕ} (f : Admissible d) : TestFunction d :=
  dilate f.function (balancingScale f) (balancingScale_pos f)
@[simp] theorem balancedFunction_apply {d : ℕ} (f : Admissible d)
    (x : Euclidean d) :
    balancedFunction f x = f.function (balancingScale f • x) := by
  rfl
theorem balancedFunction_real {d : ℕ} (f : Admissible d) :
    IsRealValued (balancedFunction f) :=
  f.real.dilate (balancingScale f) (balancingScale_pos f)
theorem balancedFunction_radial {d : ℕ} (f : Admissible d) :
    IsRadial (balancedFunction f) :=
  f.radial.dilate (balancingScale f) (balancingScale_pos f)
theorem balancedFunction_fourier_real {d : ℕ} (f : Admissible d) :
    IsRealValued (𝓕 (balancedFunction f) : TestFunction d) := by
  intro ξ
  unfold balancedFunction
  rw [fourier_dilate_apply, Complex.smul_im,
    f.fourier_real ((balancingScale f)⁻¹ • ξ)]
  simp
theorem balancedFunction_fourier_nonneg {d : ℕ} (f : Admissible d)
    (ξ : Euclidean d) :
    0 ≤ ((𝓕 (balancedFunction f) : TestFunction d) ξ).re := by
  unfold balancedFunction
  rw [fourier_dilate_apply, Complex.smul_re]
  simpa [smul_eq_mul] using!
    mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (balancingScale_pos f).le d))
      (f.fourier_nonneg ((balancingScale f)⁻¹ • ξ))
theorem balancedFunction_fourier_radial {d : ℕ} (f : Admissible d) :
    IsRadial (𝓕 (balancedFunction f) : TestFunction d) := by
  intro x y hxy
  let A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d :=
    Submodule.reflection (ℝ ∙ (x - y))ᗮ
  have hA : A x = y := Submodule.reflection_sub hxy
  have hcomp :
      (balancedFunction f : Euclidean d → ℂ) ∘ A = balancedFunction f := by
    funext z
    exact balancedFunction_radial f (A z) z (A.norm_map z)
  change (𝓕 (balancedFunction f : Euclidean d → ℂ)) x =
    (𝓕 (balancedFunction f : Euclidean d → ℂ)) y
  calc
    (𝓕 (balancedFunction f : Euclidean d → ℂ)) x =
        (𝓕 ((balancedFunction f : Euclidean d → ℂ) ∘ A)) x := by
      rw [hcomp]
    _ = (𝓕 (balancedFunction f : Euclidean d → ℂ)) (A x) :=
      Real.fourier_comp_linearIsometry A
        (balancedFunction f : Euclidean d → ℂ) x
    _ = (𝓕 (balancedFunction f : Euclidean d → ℂ)) y := by rw [hA]
theorem balancedFunction_fourier_zero {d : ℕ} (f : Admissible d)
    (hd : 0 < d) :
    ((𝓕 (balancedFunction f) : TestFunction d)
      (0 : Euclidean d)) = balancedFunction f 0 := by
  unfold balancedFunction
  rw [fourier_dilate_zero, balancingScale_pow f hd, dilate_zero]
  apply Complex.ext
  · rw [Complex.smul_re]
    change
      (((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re /
        (f.function (0 : Euclidean d)).re)⁻¹ *
          ((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re =
        (f.function (0 : Euclidean d)).re
    field_simp [f.fourier_zero_pos.ne', (admissible_zero_pos f).ne']
  · rw [Complex.smul_im]
    change
      (((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re /
        (f.function (0 : Euclidean d)).re)⁻¹ *
          ((𝓕 f.function : TestFunction d) (0 : Euclidean d)).im =
        (f.function (0 : Euclidean d)).im
    rw [f.fourier_real, f.real]
    simp
theorem balancedFunction_outside_nonpos {d : ℕ} (f : Admissible d)
    (x : Euclidean d) (hx : (balancingScale f)⁻¹ ≤ ‖x‖) :
    (balancedFunction f x).re ≤ 0 := by
  apply f.outside_nonpos (balancingScale f • x)
  have h := mul_le_mul_of_nonneg_left hx (balancingScale_pos f).le
  rw [mul_inv_cancel₀ (balancingScale_pos f).ne'] at h
  simpa [norm_smul, Real.norm_eq_abs,
    abs_of_pos (balancingScale_pos f)] using! h
def balancedAntiFourierPart {d : ℕ} (f : Admissible d) : TestFunction d :=
  antiFourierPart (balancedFunction f)
theorem fourier_balancedAntiFourierPart {d : ℕ} (f : Admissible d) :
    (𝓕 (balancedAntiFourierPart f) : TestFunction d) =
      -balancedAntiFourierPart f := by
  exact fourier_antiFourierPart (balancedFunction f)
    (balancedFunction_radial f)
theorem balancedAntiFourierPart_zero {d : ℕ} (f : Admissible d)
    (hd : 0 < d) :
    balancedAntiFourierPart f (0 : Euclidean d) = 0 := by
  exact antiFourierPart_zero (balancedFunction f)
    (balancedFunction_fourier_zero f hd)
theorem balancedAntiFourierPart_real {d : ℕ} (f : Admissible d) :
    IsRealValued (balancedAntiFourierPart f) := by
  intro x
  change (((𝓕 (balancedFunction f) : TestFunction d) x) -
    balancedFunction f x).im = 0
  rw [Complex.sub_im, balancedFunction_fourier_real f x,
    balancedFunction_real f x]
  norm_num
theorem balancedAntiFourierPart_radial {d : ℕ} (f : Admissible d) :
    IsRadial (balancedAntiFourierPart f) := by
  intro x y hxy
  change
    ((𝓕 (balancedFunction f) : TestFunction d) x) -
        balancedFunction f x =
      ((𝓕 (balancedFunction f) : TestFunction d) y) -
        balancedFunction f y
  rw [balancedFunction_fourier_radial f x y hxy,
    balancedFunction_radial f x y hxy]
theorem balancedAntiFourierPart_nonneg {d : ℕ} (f : Admissible d)
    (x : Euclidean d) (hx : (balancingScale f)⁻¹ ≤ ‖x‖) :
    0 ≤ (balancedAntiFourierPart f x).re := by
  exact antiFourierPart_nonneg_of_signs
    (balancedFunction f) ((balancingScale f)⁻¹)
    (balancedFunction_fourier_nonneg f)
    (balancedFunction_outside_nonpos f) x hx
theorem balancedAntiFourierPart_eq_zero_iff {d : ℕ} (f : Admissible d) :
    balancedAntiFourierPart f = 0 ↔
      (𝓕 (balancedFunction f) : TestFunction d) = balancedFunction f := by
  change (𝓕 (balancedFunction f) : TestFunction d) -
    balancedFunction f = 0 ↔ _
  exact sub_eq_zero
theorem balancedFunction_support_subset_of_anti_zero {d : ℕ}
    (f : Admissible d) (hzero : balancedAntiFourierPart f = 0) :
    Function.support (balancedFunction f : Euclidean d → ℂ) ⊆
      Metric.closedBall (0 : Euclidean d) (balancingScale f)⁻¹ := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hnot
  have hlarge : (balancingScale f)⁻¹ < ‖x‖ := lt_of_not_ge hnot
  have hself := (balancedAntiFourierPart_eq_zero_iff f).mp hzero
  have hnonneg : 0 ≤ (balancedFunction f x).re := by
    have hpoint :
        ((𝓕 (balancedFunction f) : TestFunction d) x) =
          balancedFunction f x :=
      congrArg (fun g : TestFunction d => g x) hself
    calc
      0 ≤ ((𝓕 (balancedFunction f) : TestFunction d) x).re :=
        balancedFunction_fourier_nonneg f x
      _ = (balancedFunction f x).re := congrArg Complex.re hpoint
  have hnonpos : (balancedFunction f x).re ≤ 0 :=
    balancedFunction_outside_nonpos f x hlarge.le
  have hre : (balancedFunction f x).re = 0 :=
    le_antisymm hnonpos hnonneg
  apply hx
  apply Complex.ext
  · simpa using! hre
  · simpa using! balancedFunction_real f x
theorem balancedFunction_hasCompactSupport_of_anti_zero {d : ℕ}
    (f : Admissible d) (hzero : balancedAntiFourierPart f = 0) :
    HasCompactSupport (balancedFunction f : Euclidean d → ℂ) := by
  exact HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Euclidean d) (balancingScale f)⁻¹)
    (balancedFunction_support_subset_of_anti_zero f hzero)
def nonnegativeSchwartzDensity {d : ℕ} (g : TestFunction d)
    (hg : ∀ x : Euclidean d, 0 ≤ (g x).re) :
    Euclidean d → ℝ≥0 :=
  fun x => ⟨(g x).re, hg x⟩
theorem nonnegativeSchwartzDensity_continuous {d : ℕ}
    (g : TestFunction d) (hg : ∀ x : Euclidean d, 0 ≤ (g x).re) :
    Continuous (nonnegativeSchwartzDensity g hg) := by
  exact (Complex.continuous_re.comp g.continuous).subtype_mk hg
def nonnegativeSchwartzMeasure {d : ℕ} (g : TestFunction d)
    (hg : ∀ x : Euclidean d, 0 ≤ (g x).re) :
    Measure (Euclidean d) :=
  (volume : Measure (Euclidean d)).withDensity
    (fun x => (nonnegativeSchwartzDensity g hg x : ℝ≥0∞))
theorem integrableExpSet_nonnegativeSchwartzMeasure_eq_univ {d : ℕ}
    (g : TestFunction d) (hg : ∀ x : Euclidean d, 0 ≤ (g x).re)
    (hcompact : HasCompactSupport (g : Euclidean d → ℂ))
    (X : Euclidean d → ℝ) (hX : Continuous X) :
    ProbabilityTheory.integrableExpSet X
      (nonnegativeSchwartzMeasure g hg) = Set.univ := by
  ext t
  simp only [ProbabilityTheory.integrableExpSet, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  unfold nonnegativeSchwartzMeasure
  rw [integrable_withDensity_iff_integrable_smul
    (nonnegativeSchwartzDensity_continuous g hg).measurable]
  simp_rw [NNReal.smul_def, smul_eq_mul]
  have hrealcompact :
      HasCompactSupport (fun x : Euclidean d => (g x).re) := by
    change HasCompactSupport (Complex.re ∘
      (g : Euclidean d → ℂ))
    exact hcompact.comp_left (by simp)
  have hcontinuous :
      Continuous (fun x : Euclidean d =>
        (g x).re * Real.exp (t * X x)) := by
    exact (Complex.continuous_re.comp g.continuous).mul
      (Real.continuous_exp.comp (continuous_const.mul hX))
  exact hcontinuous.integrable_of_hasCompactSupport
    hrealcompact.mul_right
theorem nonnegativeSchwartz_complexMGF_analytic {d : ℕ}
    (g : TestFunction d) (hg : ∀ x : Euclidean d, 0 ≤ (g x).re)
    (hcompact : HasCompactSupport (g : Euclidean d → ℂ))
    (X : Euclidean d → ℝ) (hX : Continuous X) :
    AnalyticOnNhd ℂ
      (ProbabilityTheory.complexMGF X
        (nonnegativeSchwartzMeasure g hg)) Set.univ := by
  have hset := integrableExpSet_nonnegativeSchwartzMeasure_eq_univ
    g hg hcompact X hX
  simpa [hset] using!
    (ProbabilityTheory.analyticOnNhd_complexMGF
      (X := X) (μ := nonnegativeSchwartzMeasure g hg))
theorem nonnegativeSchwartz_complexMGF_mul_I {d : ℕ}
    (g : TestFunction d) (hreal : IsRealValued g)
    (hg : ∀ x : Euclidean d, 0 ≤ (g x).re)
    (e : Euclidean d) (t : ℝ) :
    ProbabilityTheory.complexMGF
        (fun x : Euclidean d =>
          -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
        (nonnegativeSchwartzMeasure g hg)
        ((t : ℂ) * Complex.I) =
      ((𝓕 g : TestFunction d) (t • e)) := by
  calc
    ProbabilityTheory.complexMGF
        (fun x : Euclidean d =>
          -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
        (nonnegativeSchwartzMeasure g hg)
        ((t : ℂ) * Complex.I) =
      ∫ x : Euclidean d,
        nonnegativeSchwartzDensity g hg x •
          Complex.exp
            (((t : ℂ) * Complex.I) *
              (↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ x e) : ℂ)) := by
        unfold ProbabilityTheory.complexMGF nonnegativeSchwartzMeasure
        rw [integral_withDensity_eq_integral_smul
          (nonnegativeSchwartzDensity_continuous g hg).measurable]
    _ = (𝓕 (g : Euclidean d → ℂ)) (t • e) := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards [] with x
      have hvalue : (↑((g x).re) : ℂ) = g x := by
        apply Complex.ext
        · simp
        · simpa using! (hreal x).symm
      have hexponent :
          ((t : ℂ) * Complex.I) *
              (↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ x e) : ℂ) =
            (↑(-2 * Real.pi *
              @inner ℝ (Euclidean d) _ x (t • e)) : ℂ) *
                Complex.I := by
        rw [real_inner_smul_right]
        push_cast
        ring
      rw [NNReal.smul_def, Complex.real_smul, hexponent]
      change (↑((g x).re) : ℂ) * _ = _ * g x
      rw [hvalue, mul_comm]
    _ = ((𝓕 g : TestFunction d) (t • e)) :=
      (congrFun (SchwartzMap.fourier_coe g) (t • e)).symm
theorem analytic_eq_zero_of_imaginary_ray
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ)
    (T : ℝ)
    (hvanish : ∀ t : ℝ, T < t → F ((t : ℂ) * Complex.I) = 0) :
    F = 0 := by
  let t₀ : ℝ := T + 1
  let z₀ : ℂ := (t₀ : ℂ) * Complex.I
  have hclosure :
      z₀ ∈ closure ({z : ℂ | F z = 0} \ {z₀}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let u : ℝ := t₀ + ε / 2
    let z : ℂ := (u : ℂ) * Complex.I
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · apply hvanish u
      try dsimp [u, t₀]
      linarith
    · intro hz
      have hu : u = t₀ := by
        have him := congrArg Complex.im hz
        simpa [z, z₀] using! him
      try dsimp [u] at hu
      linarith
    · dsimp [z₀, z, u]
      rw [dist_eq_norm, ← sub_mul, ← Complex.ofReal_sub, norm_mul,
        Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
      rw [show t₀ - (t₀ + ε / 2) = -(ε / 2) by ring,
        abs_neg, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
  have heq :=
    hF.eqOn_zero_of_preconnected_of_mem_closure
      isPreconnected_univ (Set.mem_univ z₀) hclosure
  funext z
  exact heq (Set.mem_univ z)
theorem nonnegative_compact_fourier_fixed_eq_zero {d : ℕ}
    (hd : 0 < d) (g : TestFunction d)
    (hreal : IsRealValued g)
    (hg : ∀ x : Euclidean d, 0 ≤ (g x).re)
    (hcompact : HasCompactSupport (g : Euclidean d → ℂ))
    (hfixed : (𝓕 g : TestFunction d) = g) :
    g = 0 := by
  classical
  letI : Nontrivial (Euclidean d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (M := Euclidean d)
      (by simpa [finrank_euclideanSpace] using! hd)
  obtain ⟨e, he⟩ :=
    exists_norm_eq (Euclidean d) (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨R, hR⟩ :=
    hcompact.isBounded.subset_closedBall (0 : Euclidean d)
  let X : Euclidean d → ℝ :=
    fun x => -2 * Real.pi * @inner ℝ (Euclidean d) _ x e
  have hX : Continuous X := by
    try dsimp [X]
    fun_prop
  let μ : Measure (Euclidean d) := nonnegativeSchwartzMeasure g hg
  let F : ℂ → ℂ := ProbabilityTheory.complexMGF X μ
  have hanalytic : AnalyticOnNhd ℂ F Set.univ := by
    try dsimp [F, μ]
    exact nonnegativeSchwartz_complexMGF_analytic g hg hcompact X hX
  have hvanish :
      ∀ t : ℝ, max R 0 < t → F ((t : ℂ) * Complex.I) = 0 := by
    intro t ht
    change
      ProbabilityTheory.complexMGF
          (fun x : Euclidean d =>
            -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
          (nonnegativeSchwartzMeasure g hg)
          ((t : ℂ) * Complex.I) = 0
    rw [nonnegativeSchwartz_complexMGF_mul_I g hreal hg e t,
      hfixed]
    by_contra hnonzero
    have hsupp :
        t • e ∈ Function.support (g : Euclidean d → ℂ) := by
      exact hnonzero
    have hbound : ‖t • e‖ ≤ R := by
      have hball := hR
        (subset_tsupport (g : Euclidean d → ℂ) hsupp)
      simpa only [Metric.mem_closedBall, dist_zero_right] using! hball
    have htpos : 0 < t := (le_max_right R 0).trans_lt ht
    have hnorm : ‖t • e‖ = t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, he, mul_one]
    rw [hnorm] at hbound
    exact (not_le_of_gt ((le_max_left R 0).trans_lt ht)) hbound
  have hFzero : F = 0 :=
    analytic_eq_zero_of_imaginary_ray F hanalytic (max R 0) hvanish
  have hFzero_at_zero : F 0 = 0 := by
    simpa using! congrFun hFzero (0 : ℂ)
  have hfourierzero :
      ((𝓕 g : TestFunction d) (0 : Euclidean d)) = 0 := by
    have hmomentzero :
        ProbabilityTheory.complexMGF
          (fun x : Euclidean d =>
            -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
          (nonnegativeSchwartzMeasure g hg) 0 = 0 := by
      exact hFzero_at_zero
    calc
      ((𝓕 g : TestFunction d) (0 : Euclidean d)) =
          ProbabilityTheory.complexMGF
            (fun x : Euclidean d =>
              -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
            (nonnegativeSchwartzMeasure g hg)
            ((0 : ℂ) * Complex.I) := by
        simpa using!
          (nonnegativeSchwartz_complexMGF_mul_I g hreal hg e 0).symm
      _ = 0 := by simpa using! hmomentzero
  have hfourier_integral :
      ((𝓕 g : TestFunction d) (0 : Euclidean d)) =
        ∫ x : Euclidean d, g x := by
    change (𝓕 (g : Euclidean d → ℂ)) 0 = _
    rw [Real.fourier_eq']
    simp
  have hintegral :
      (∫ x : Euclidean d, (g x).re) = 0 := by
    calc
      (∫ x : Euclidean d, (g x).re) =
          (∫ x : Euclidean d, g x).re :=
        integral_re g.integrable
      _ = ((𝓕 g : TestFunction d) (0 : Euclidean d)).re := by
        rw [hfourier_integral]
      _ = 0 := by rw [hfourierzero]; rfl
  by_contra hnonzero
  have hreal_nonzero :
      (fun x : Euclidean d => (g x).re) ≠ 0 := by
    intro hzero
    apply hnonzero
    ext x
    apply Complex.ext
    · simpa using! congrFun hzero x
    · simpa using! hreal x
  obtain ⟨x, hx⟩ :
      ∃ x : Euclidean d, (g x).re ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hreal_nonzero
    funext x
    simpa using! hnone x
  have hpositive :
      0 < ∫ x : Euclidean d, (g x).re :=
    integral_pos_of_integrable_nonneg_nonzero
      (Complex.continuous_re.comp g.continuous)
      g.integrable.re hg hx
  exact (ne_of_gt hpositive) hintegral
theorem balancedAntiFourierPart_ne_zero {d : ℕ}
    (f : Admissible d) (hd : 0 < d) :
    balancedAntiFourierPart f ≠ 0 := by
  intro hzero
  have hself := (balancedAntiFourierPart_eq_zero_iff f).mp hzero
  have hcompact := balancedFunction_hasCompactSupport_of_anti_zero f hzero
  have hnonneg :
      ∀ x : Euclidean d, 0 ≤ (balancedFunction f x).re := by
    intro x
    rw [← hself]
    exact balancedFunction_fourier_nonneg f x
  have hvanish :=
    nonnegative_compact_fourier_fixed_eq_zero hd
      (balancedFunction f) (balancedFunction_real f)
      hnonneg hcompact hself
  have horigin := congrArg
    (fun g : TestFunction d => (g (0 : Euclidean d)).re) hvanish
  have hpos : 0 < (balancedFunction f (0 : Euclidean d)).re := by
    simpa using! admissible_zero_pos f
  simpa using! hpos.ne' horigin
def AntiFourierWitness.monoRadius {d : ℕ} {R S : ℝ}
    (w : AntiFourierWitness d R) (hRS : R ≤ S) :
    AntiFourierWitness d S where
  function := w.function
  real := w.real
  radial := w.radial
  nonzero := w.nonzero
  anti_fourier := w.anti_fourier
  zero_value := w.zero_value
  eventually_nonneg := fun x hx =>
    w.eventually_nonneg x (hRS.trans hx)
def balancedAntiFourierWitness {d : ℕ} (f : Admissible d)
    (hd : 0 < d) :
    AntiFourierWitness d (balancingScale f)⁻¹ where
  function := balancedAntiFourierPart f
  real := balancedAntiFourierPart_real f
  radial := balancedAntiFourierPart_radial f
  nonzero := balancedAntiFourierPart_ne_zero f hd
  anti_fourier := fourier_balancedAntiFourierPart f
  zero_value := balancedAntiFourierPart_zero f hd
  eventually_nonneg := balancedAntiFourierPart_nonneg f
end
noncomputable section
open MeasureTheory Metric
open scoped ENNReal
theorem sqrt_pi_pow_eq_rpow (d : ℕ) :
    Real.sqrt Real.pi ^ d = Real.pi ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul Real.pi_nonneg]
  congr 1
  ring
theorem volume_unitBall {d : ℕ} (hd : 0 < d) :
    volume (ball (0 : Euclidean d) (1 : ℝ)) =
      ENNReal.ofReal (unitBallVolume d) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  simpa [Fintype.card_fin, unitBallVolume, sqrt_pi_pow_eq_rpow] using!
    (EuclideanSpace.volume_ball (Fin d) (0 : Euclidean d) (1 : ℝ))
end
noncomputable section
open Filter MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal
def radialUnitDirection {d : ℕ} (hd : 0 < d) : Euclidean d :=
  (EuclideanSpace.basisFun (Fin d) ℝ) ⟨0, hd⟩
theorem norm_radialUnitDirection {d : ℕ} (hd : 0 < d) :
    ‖radialUnitDirection hd‖ = 1 := by
  unfold radialUnitDirection
  exact (EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one _
def radialProfile {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (r : ℝ) : ℂ :=
  f (r • radialUnitDirection hd)
theorem radialProfile_norm {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (hf : IsRadial f) (x : Euclidean d) :
    radialProfile hd f ‖x‖ = f x := by
  unfold radialProfile
  apply hf
  simp [norm_smul, norm_radialUnitDirection hd]
theorem radialProfile_continuous {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) :
    Continuous (radialProfile hd f) := by
  unfold radialProfile
  exact f.continuous.comp (continuous_id.smul continuous_const)
@[simp] theorem radialProfile_zero {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) :
    radialProfile hd f 0 = f (0 : Euclidean d) := by
  simp [radialProfile]
theorem volume_real_unitBall {d : ℕ} (hd : 0 < d) :
    volume.real (ball (0 : Euclidean d) (1 : ℝ)) =
      unitBallVolume d := by
  change (volume (ball (0 : Euclidean d) (1 : ℝ))).toReal =
    unitBallVolume d
  rw [volume_unitBall hd, ENNReal.toReal_ofReal
    (unitBallVolume_pos d).le]
def radialSurfaceArea (d : ℕ) : ℝ :=
  (d : ℝ) * unitBallVolume d
theorem radialSurfaceArea_pos {d : ℕ} (hd : 0 < d) :
    0 < radialSurfaceArea d := by
  unfold radialSurfaceArea
  exact mul_pos (by exact_mod_cast hd) (unitBallVolume_pos d)
theorem integral_radialProfile_mul {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (hf : IsRadial f) (w : ℝ → ℂ) :
    (∫ x : Euclidean d, f x * w ‖x‖) =
      radialSurfaceArea d •
        ∫ r : ℝ in Ioi 0,
          r ^ (d - 1) • (radialProfile hd f r * w r) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  calc
    (∫ x : Euclidean d, f x * w ‖x‖) =
        ∫ x : Euclidean d,
          radialProfile hd f ‖x‖ * w ‖x‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [radialProfile_norm hd f hf x]
    _ = radialSurfaceArea d •
          ∫ r : ℝ in Ioi 0,
            r ^ (d - 1) • (radialProfile hd f r * w r) := by
      simpa [radialSurfaceArea, volume_real_unitBall hd,
        nsmul_eq_mul, finrank_euclideanSpace_fin, mul_assoc] using!
        (integral_fun_norm_addHaar
          (volume : Measure (Euclidean d))
          (fun r : ℝ => radialProfile hd f r * w r))
theorem integral_radialProfile_cpow {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (hf : IsRadial f) (s : ℂ) :
    (∫ x : Euclidean d,
      f x * (‖x‖ : ℂ) ^ (s - (d : ℂ))) =
      radialSurfaceArea d • mellin (radialProfile hd f) s := by
  rw [integral_radialProfile_mul hd f hf
    (fun r : ℝ => (r : ℂ) ^ (s - (d : ℂ)))]
  congr 1
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hrzero : (r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hcast :
      (((r ^ (d - 1) : ℝ) : ℂ)) =
        (r : ℂ) ^ ((d - 1 : ℕ) : ℂ) := by
    rw [Complex.cpow_natCast]
    norm_cast
  have hexponent :
      (((d - 1 : ℕ) : ℂ)) + (s - (d : ℂ)) = s - 1 := by
    rw [Nat.cast_sub hd]
    norm_num
  change
    (((r ^ (d - 1) : ℝ) : ℂ)) *
      (radialProfile hd f r * (r : ℂ) ^ (s - (d : ℂ))) =
        (r : ℂ) ^ (s - 1) * radialProfile hd f r
  rw [hcast]
  have hpower :
      (r : ℂ) ^ ((d - 1 : ℕ) : ℂ) *
        (r : ℂ) ^ (s - (d : ℂ)) =
          (r : ℂ) ^ (s - 1) := by
    rw [← Complex.cpow_add _ _ hrzero, hexponent]
  calc
    (r : ℂ) ^ ((d - 1 : ℕ) : ℂ) *
        (radialProfile hd f r *
          (r : ℂ) ^ (s - (d : ℂ))) =
      ((r : ℂ) ^ ((d - 1 : ℕ) : ℂ) *
        (r : ℂ) ^ (s - (d : ℂ))) * radialProfile hd f r := by
          ring
    _ = (r : ℂ) ^ (s - 1) * radialProfile hd f r := by
          rw [hpower]
def radialMellinFrequency {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (t : ℝ) : ℂ :=
  mellinFrequency ((d : ℝ) / 2) (radialProfile hd f) t
theorem radialMellinFrequency_eq_fourier {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (t : ℝ) :
    radialMellinFrequency hd f t =
      (𝓕 (fun u : ℝ =>
        Real.exp (-((d : ℝ) / 2) * u) •
          radialProfile hd f (Real.exp (-u))))
        (-t / (2 * Real.pi)) := by
  exact mellinFrequency_eq_fourier
    ((d : ℝ) / 2) (radialProfile hd f) t
end
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace
def gaussianMellinWeight (d : ℕ) (a : ℝ) (x : Euclidean d) : ℂ :=
  Complex.exp (-((a : ℂ) * (‖x‖ : ℂ) ^ 2))
theorem gaussianMellin_fourier_radial {d : ℕ} {f : TestFunction d}
    (hf : IsRadial f) : IsRadial (𝓕 f : TestFunction d) := by
  intro x y hxy
  let A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d :=
    Submodule.reflection (ℝ ∙ (x - y))ᗮ
  have hA : A x = y := Submodule.reflection_sub hxy
  have hcomp : (f : Euclidean d → ℂ) ∘ A = f := by
    funext z
    exact hf (A z) z (A.norm_map z)
  change (𝓕 (f : Euclidean d → ℂ)) x =
    (𝓕 (f : Euclidean d → ℂ)) y
  calc
    (𝓕 (f : Euclidean d → ℂ)) x =
        (𝓕 ((f : Euclidean d → ℂ) ∘ A)) x := by rw [hcomp]
    _ = (𝓕 (f : Euclidean d → ℂ)) (A x) :=
      Real.fourier_comp_linearIsometry A (f : Euclidean d → ℂ) x
    _ = (𝓕 (f : Euclidean d → ℂ)) y := by rw [hA]
theorem gaussianMellinWeight_integrable {d : ℕ}
    (a : ℝ) (ha : 0 < a) :
    Integrable (gaussianMellinWeight d a)
      (volume : Measure (Euclidean d)) := by
  have hcomplex : 0 < (a : ℂ).re := by
    simpa using! ha
  simpa [gaussianMellinWeight] using!
    (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := Euclidean d) hcomplex (0 : ℂ) (0 : Euclidean d))
theorem fourier_gaussianMellinWeight {d : ℕ}
    (a : ℝ) (ha : 0 < a) (ξ : Euclidean d) :
    (𝓕 (gaussianMellinWeight d a) : Euclidean d → ℂ) ξ =
      ((Real.pi : ℂ) / (a : ℂ)) ^ ((d : ℂ) / 2) *
        Complex.exp
          (-((Real.pi : ℂ) ^ 2) * (‖ξ‖ : ℂ) ^ 2 / (a : ℂ)) := by
  have hcomplex : 0 < (a : ℂ).re := by
    simpa using! ha
  simpa [gaussianMellinWeight, finrank_euclideanSpace] using!
    (fourier_gaussian_innerProductSpace (V := Euclidean d)
      hcomplex ξ)
theorem fourier_gaussianMellin_pairing {d : ℕ}
    (f : TestFunction d) (a : ℝ) (ha : 0 < a) :
    (∫ ξ : Euclidean d,
      ((𝓕 f : TestFunction d) ξ) * gaussianMellinWeight d a ξ) =
      ∫ x : Euclidean d,
        f x *
          (((Real.pi : ℂ) / (a : ℂ)) ^ ((d : ℂ) / 2) *
            Complex.exp
              (-((Real.pi : ℂ) ^ 2) * (‖x‖ : ℂ) ^ 2 /
                (a : ℂ))) := by
  have hflip :
      (innerₗ (Euclidean d)).flip = innerₗ (Euclidean d) := by
    ext x y
    change
      @inner ℝ (Euclidean d) _ y x =
        @inner ℝ (Euclidean d) _ x y
    exact real_inner_comm x y
  calc
    (∫ ξ : Euclidean d,
      ((𝓕 f : TestFunction d) ξ) * gaussianMellinWeight d a ξ) =
        ∫ ξ : Euclidean d,
          (𝓕 (f : Euclidean d → ℂ)) ξ *
            gaussianMellinWeight d a ξ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      exact congrArg
        (fun z : ℂ => z * gaussianMellinWeight d a ξ)
        (congrFun (SchwartzMap.fourier_coe f) ξ)
    _ = ∫ x : Euclidean d,
          f x *
            (𝓕 (gaussianMellinWeight d a) :
              Euclidean d → ℂ) x := by
      simpa only [smul_eq_mul, hflip] using!
        (VectorFourier.integral_fourierIntegral_smul_eq_flip
          (L := innerₗ (Euclidean d))
          (μ := (volume : Measure (Euclidean d)))
          (ν := (volume : Measure (Euclidean d)))
          (f := (f : Euclidean d → ℂ))
          (g := gaussianMellinWeight d a)
          Real.continuous_fourierChar continuous_inner
          f.integrable (gaussianMellinWeight_integrable a ha))
    _ = ∫ x : Euclidean d,
          f x *
            (((Real.pi : ℂ) / (a : ℂ)) ^ ((d : ℂ) / 2) *
              Complex.exp
                (-((Real.pi : ℂ) ^ 2) * (‖x‖ : ℂ) ^ 2 /
                  (a : ℂ))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [fourier_gaussianMellinWeight a ha x]
theorem schwartz_mul_norm_cpow_integrable {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (z : ℂ)
    (hlower : -(d : ℝ) < z.re) (hupper : z.re ≤ 0) :
    Integrable
      (fun x : Euclidean d => f x * (‖x‖ : ℂ) ^ z)
      (volume : Measure (Euclidean d)) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hpow : Measurable (fun x : Euclidean d => (‖x‖ : ℂ) ^ z) := by
    apply measurable_of_continuousOn_compl_singleton
      (0 : Euclidean d)
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hxzero : x ≠ 0 := by
      simpa only [mem_compl_iff, mem_singleton_iff] using! hx
    exact
      (Complex.continuousAt_ofReal_cpow_const ‖x‖ z
        (Or.inr (norm_ne_zero_iff.mpr hxzero))).comp
        continuous_norm.continuousAt
  have hmeas :
      AEStronglyMeasurable
        (fun x : Euclidean d => f x * (‖x‖ : ℂ) ^ z)
        (volume : Measure (Euclidean d)) :=
    (f.continuous.measurable.mul hpow).aestronglyMeasurable
  have hdim : 1 ≤ Module.finrank ℝ (Euclidean d) := by
    rw [finrank_euclideanSpace_fin]
    omega
  have hexponent :
      -z.re < (Module.finrank ℝ (Euclidean d) : ℝ) := by
    rw [finrank_euclideanSpace_fin]
    exact (neg_lt_of_neg_lt hlower)
  have hinner :
      IntegrableOn
        (fun x : Euclidean d => f x * (‖x‖ : ℂ) ^ z)
        (Metric.ball 0 1)
        (volume : Measure (Euclidean d)) := by
    apply MeasureTheory.integrableOn_ball_of_norm_le_rpow
      hdim hexponent (C := SchwartzMap.seminorm ℝ 0 0 f)
      (r := 1)
    · filter_upwards
        [ae_restrict_of_ae
          ((volume : Measure (Euclidean d)).ae_ne
            (0 : Euclidean d))] with x hx
      rw [norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos
          (norm_pos_iff.mpr hx), neg_neg]
      exact mul_le_mul_of_nonneg_right
        (SchwartzMap.norm_le_seminorm ℝ f x)
        (Real.rpow_nonneg (norm_nonneg x) z.re)
    · exact hmeas
  have houter :
      IntegrableOn
        (fun x : Euclidean d => f x * (‖x‖ : ℂ) ^ z)
        (Metric.ball (0 : Euclidean d) 1)ᶜ
        (volume : Measure (Euclidean d)) := by
    refine (f.integrable.norm.restrict).mono' hmeas.restrict ?_
    filter_upwards
      [ae_restrict_mem
        (Metric.isOpen_ball.measurableSet.compl)] with x hx
    have hnorm : 1 ≤ ‖x‖ := by
      have hnot : ¬ ‖x‖ < (1 : ℝ) := by
        simpa [Metric.mem_ball, dist_zero_right] using! hx
      exact le_of_not_gt hnot
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos
        (lt_of_lt_of_le zero_lt_one hnorm)]
    calc
      ‖f x‖ * ‖x‖ ^ z.re ≤ ‖f x‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos hnorm hupper)
          (norm_nonneg _)
      _ = ‖f x‖ := mul_one _
  have hglobal := hinner.union houter
  rwa [union_compl_self, integrableOn_univ] at hglobal
theorem gaussianMellinParameter_integrable
    (b : ℂ) (hb : 0 < b.re) (r : ℝ) (hr : 0 < r) :
    IntegrableOn
      (fun a : ℝ =>
        (a : ℂ) ^ (b - 1) *
          Complex.exp (-((r : ℂ) * (a : ℂ))))
      (Ioi 0) := by
  have hmeas :
      AEStronglyMeasurable
        (fun a : ℝ =>
          (a : ℂ) ^ (b - 1) *
            Complex.exp (-((r : ℂ) * (a : ℂ))))
        (volume.restrict (Ioi (0 : ℝ))) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply continuousOn_of_forall_continuousAt
    intro a ha
    apply
      (Complex.continuousAt_ofReal_cpow_const a (b - 1)
        (Or.inr (ne_of_gt ha))).mul
    fun_prop
  have hreal :
      IntegrableOn
        (fun a : ℝ =>
          a ^ (b.re - 1) * Real.exp (-(r * a)))
        (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using!
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := b.re - 1) (b := r)
        (by linarith) (by norm_num) hr)
  apply (integrable_norm_iff hmeas).mp
  apply hreal.congr_fun _ measurableSet_Ioi
  intro a ha
  try dsimp
  rw [norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos ha,
    Complex.norm_exp]
  simp
theorem gaussianMellinParameter_norm_integral
    (b : ℂ) (hb : 0 < b.re) (r : ℝ) (hr : 0 < r) :
    (∫ a : ℝ in Ioi 0,
      ‖(a : ℂ) ^ (b - 1) *
        Complex.exp (-((r : ℂ) * (a : ℂ)))‖) =
      (1 / r) ^ b.re * Real.Gamma b.re := by
  calc
    (∫ a : ℝ in Ioi 0,
      ‖(a : ℂ) ^ (b - 1) *
        Complex.exp (-((r : ℂ) * (a : ℂ)))‖) =
        ∫ a : ℝ in Ioi 0,
          a ^ (b.re - 1) * Real.exp (-(r * a)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a ha
      try dsimp
      rw [norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos ha,
        Complex.norm_exp]
      simp
    _ = (1 / r) ^ b.re * Real.Gamma b.re :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi hb hr
theorem gaussianMellin_inv_sq_rpow
    (r b : ℝ) (hr : 0 ≤ r) :
    (1 / r ^ 2) ^ b = r ^ (-(2 * b)) := by
  calc
    (1 / r ^ 2) ^ b = (r ^ 2) ^ (-b) := by
      rw [one_div, Real.rpow_neg_eq_inv_rpow]
    _ = r ^ ((2 : ℝ) * (-b)) := by
      simpa using! (Real.rpow_natCast_mul hr 2 (-b)).symm
    _ = r ^ (-(2 * b)) := by
      congr 1
      ring
theorem gaussianMellin_inv_sq_cpow
    (r : ℝ) (hr : 0 ≤ r) (b : ℂ) :
    (1 / (((r ^ 2 : ℝ) : ℂ))) ^ b =
      (r : ℂ) ^ (-(2 * b)) := by
  calc
    (1 / (((r ^ 2 : ℝ) : ℂ))) ^ b =
        (((r ^ (-2 : ℝ) : ℝ) : ℂ)) ^ b := by
      rw [Real.rpow_neg hr, Real.rpow_two, Complex.ofReal_inv]
      simp only [one_div]
    _ = (r : ℂ) ^ (((-2 : ℝ) : ℂ) * b) :=
      (Complex.cpow_mul_ofReal_nonneg hr (-2) b).symm
    _ = (r : ℂ) ^ (-(2 * b)) := by
      congr 1
      push_cast
      ring
theorem gaussianMellin_div_cpow
    (p a : ℝ) (hp : 0 < p) (ha : 0 < a) (b : ℂ) :
    ((p : ℂ) / (a : ℂ)) ^ b =
      (p : ℂ) ^ b * (a : ℂ) ^ (-b) := by
  have hinv :
      (((a⁻¹ : ℝ) : ℂ)) ^ b = (a : ℂ) ^ (-b) := by
    simpa [Real.rpow_neg_one] using!
      (Complex.cpow_mul_ofReal_nonneg ha.le (-1) b).symm
  calc
    ((p : ℂ) / (a : ℂ)) ^ b =
        ((p : ℂ) * (((a⁻¹ : ℝ) : ℂ))) ^ b := by
      rw [Complex.ofReal_inv]
      rfl
    _ = (p : ℂ) ^ b * (((a⁻¹ : ℝ) : ℂ)) ^ b :=
      Complex.mul_cpow_ofReal_nonneg hp.le
        (inv_nonneg.mpr ha.le) b
    _ = (p : ℂ) ^ b * (a : ℂ) ^ (-b) := by
      rw [hinv]
theorem gaussianMellin_pi_coefficient (b q : ℂ) :
    (Real.pi : ℂ) ^ q *
        (((Real.pi ^ 2 : ℝ) : ℂ) ^ (b - q)) =
      (Real.pi : ℂ) ^ (2 * b - q) := by
  have hsquare :
      (((Real.pi ^ 2 : ℝ) : ℂ) ^ (b - q)) =
        (Real.pi : ℂ) ^ (2 * (b - q)) := by
    simpa [Real.rpow_two] using!
      (Complex.cpow_mul_ofReal_nonneg Real.pi_pos.le
        (2 : ℝ) (b - q)).symm
  rw [hsquare,
    ← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')]
  congr 1
  ring
def gaussianMellinMixture {d : ℕ}
    (f : TestFunction d) (b : ℂ)
    (x : Euclidean d) (a : ℝ) : ℂ :=
  f x *
    ((a : ℂ) ^ (b - 1) *
      Complex.exp (-((‖x‖ : ℂ) ^ 2 * (a : ℂ))))
theorem gaussianMellinMixture_integrable {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (b : ℂ)
    (hb : 0 < b.re) (hbd : 2 * b.re < (d : ℝ)) :
    Integrable
      (Function.uncurry (gaussianMellinMixture f b))
      ((volume : Measure (Euclidean d)).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hpow : Measurable (fun a : ℝ => (a : ℂ) ^ (b - 1)) := by
    apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
    apply continuousOn_of_forall_continuousAt
    intro a ha
    have hane : a ≠ 0 := by
      simpa only [mem_compl_iff, mem_singleton_iff] using! ha
    exact Complex.continuousAt_ofReal_cpow_const a (b - 1)
      (Or.inr hane)
  have hexp :
      Measurable
        (fun p : Euclidean d × ℝ =>
          Complex.exp
            (-((‖p.1‖ : ℂ) ^ 2 * (p.2 : ℂ)))) := by
    fun_prop
  have hmeas :
      AEStronglyMeasurable
        (Function.uncurry (gaussianMellinMixture f b))
        ((volume : Measure (Euclidean d)).prod
          (volume.restrict (Ioi (0 : ℝ)))) := by
    change
      AEStronglyMeasurable
        (fun p : Euclidean d × ℝ =>
          f p.1 *
            ((p.2 : ℂ) ^ (b - 1) *
              Complex.exp
                (-((‖p.1‖ : ℂ) ^ 2 * (p.2 : ℂ)))))
        _
    exact
      ((f.continuous.measurable.comp measurable_fst).mul
        ((hpow.comp measurable_snd).mul hexp)).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards
      [(volume : Measure (Euclidean d)).ae_ne
        (0 : Euclidean d)] with x hx
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hsquare : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hnorm
    simpa only [gaussianMellinMixture, Complex.ofReal_pow] using!
      (gaussianMellinParameter_integrable b hb (‖x‖ ^ 2)
        hsquare).const_mul (f x)
  · have hnegative :
        -(d : ℝ) <
          ((-(2 * b.re) : ℝ) : ℂ).re := by
      simpa using! (show -(d : ℝ) < -(2 * b.re) by linarith)
    have hnonpositive :
        ((-(2 * b.re) : ℝ) : ℂ).re ≤ 0 := by
      simpa using! (show -(2 * b.re) ≤ 0 by linarith)
    have hrieszComplex :=
      schwartz_mul_norm_cpow_integrable hd f
        ((-(2 * b.re) : ℝ) : ℂ) hnegative hnonpositive
    have hriesz :
        Integrable
          (fun x : Euclidean d =>
            ‖f x‖ * ‖x‖ ^ (-(2 * b.re)))
          (volume : Measure (Euclidean d)) := by
      apply hrieszComplex.norm.congr
      filter_upwards
        [(volume : Measure (Euclidean d)).ae_ne
          (0 : Euclidean d)] with x hx
      rw [norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos
          (norm_pos_iff.mpr hx)]
      simp
    apply (hriesz.mul_const (Real.Gamma b.re)).congr
    filter_upwards
      [(volume : Measure (Euclidean d)).ae_ne
        (0 : Euclidean d)] with x hx
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hsquare : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hnorm
    change
      (‖f x‖ * ‖x‖ ^ (-(2 * b.re))) * Real.Gamma b.re =
        ∫ a : ℝ in Ioi 0,
          ‖gaussianMellinMixture f b x a‖
    calc
      (‖f x‖ * ‖x‖ ^ (-(2 * b.re))) * Real.Gamma b.re =
          ‖f x‖ *
            ((1 / ‖x‖ ^ 2) ^ b.re * Real.Gamma b.re) := by
        rw [gaussianMellin_inv_sq_rpow ‖x‖ b.re
          (norm_nonneg x)]
        ring
      _ = ‖f x‖ *
          (∫ a : ℝ in Ioi 0,
            ‖(a : ℂ) ^ (b - 1) *
              Complex.exp
                (-(((‖x‖ ^ 2 : ℝ) : ℂ) * (a : ℂ)))‖) := by
        rw [gaussianMellinParameter_norm_integral
          b hb (‖x‖ ^ 2) hsquare]
      _ = ∫ a : ℝ in Ioi 0,
          ‖f x‖ *
            ‖(a : ℂ) ^ (b - 1) *
              Complex.exp
                (-(((‖x‖ ^ 2 : ℝ) : ℂ) * (a : ℂ)))‖ := by
        rw [integral_const_mul]
      _ = ∫ a : ℝ in Ioi 0,
          ‖gaussianMellinMixture f b x a‖ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro a _
        simp only [gaussianMellinMixture, norm_mul,
          Complex.ofReal_pow]
theorem gaussianMellinMixture_fubini {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (b : ℂ)
    (hb : 0 < b.re) (hbd : 2 * b.re < (d : ℝ)) :
    (∫ x : Euclidean d,
      ∫ a : ℝ in Ioi 0, gaussianMellinMixture f b x a) =
      ∫ a : ℝ in Ioi 0,
        ∫ x : Euclidean d, gaussianMellinMixture f b x a := by
  exact integral_integral_swap
    (gaussianMellinMixture_integrable hd f b hb hbd)
theorem gaussianMellinMixture_parameter_integral {d : ℕ}
    (f : TestFunction d) (b : ℂ) (hb : 0 < b.re)
    (x : Euclidean d) (hx : x ≠ 0) :
    (∫ a : ℝ in Ioi 0, gaussianMellinMixture f b x a) =
      f x *
        ((‖x‖ : ℂ) ^ (-(2 * b)) * Complex.Gamma b) := by
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsquare : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hnorm
  change
    (∫ a : ℝ in Ioi 0,
      f x *
        ((a : ℂ) ^ (b - 1) *
          Complex.exp (-((‖x‖ : ℂ) ^ 2 * (a : ℂ))))) = _
  rw [integral_const_mul]
  have hgamma :=
    Complex.integral_cpow_mul_exp_neg_mul_Ioi hb hsquare
  have hgamma' :
      (∫ a : ℝ in Ioi 0,
        (a : ℂ) ^ (b - 1) *
          Complex.exp (-((‖x‖ : ℂ) ^ 2 * (a : ℂ)))) =
        (1 / (((‖x‖ ^ 2 : ℝ) : ℂ))) ^ b *
          Complex.Gamma b := by
    simpa only [Complex.ofReal_pow] using! hgamma
  rw [hgamma',
    gaussianMellin_inv_sq_cpow ‖x‖ (norm_nonneg x) b]
def gaussianMellinPairingProfile {d : ℕ}
    (f : TestFunction d) (a : ℝ) : ℂ :=
  ∫ x : Euclidean d, f x * gaussianMellinWeight d a x
theorem mellin_gaussianMellinPairingProfile {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (b : ℂ)
    (hb : 0 < b.re) (hbd : 2 * b.re < (d : ℝ)) :
    mellin (gaussianMellinPairingProfile f) b =
      Complex.Gamma b *
        (∫ x : Euclidean d,
          f x * (‖x‖ : ℂ) ^ (-(2 * b))) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  unfold mellin
  simp only [smul_eq_mul]
  calc
    (∫ a : ℝ in Ioi 0,
      (a : ℂ) ^ (b - 1) * gaussianMellinPairingProfile f a) =
        ∫ a : ℝ in Ioi 0,
          ∫ x : Euclidean d, gaussianMellinMixture f b x a := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a _
      try dsimp
      unfold gaussianMellinPairingProfile
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [gaussianMellinWeight, gaussianMellinMixture]
      have hexp :
          Complex.exp (-((a : ℂ) * (‖x‖ : ℂ) ^ 2)) =
            Complex.exp (-((‖x‖ : ℂ) ^ 2 * (a : ℂ))) := by
        congr 1
        ring
      rw [hexp]
      ring
    _ = ∫ x : Euclidean d,
          ∫ a : ℝ in Ioi 0,
            gaussianMellinMixture f b x a :=
      (gaussianMellinMixture_fubini hd f b hb hbd).symm
    _ = ∫ x : Euclidean d,
          f x *
            ((‖x‖ : ℂ) ^ (-(2 * b)) * Complex.Gamma b) := by
      apply integral_congr_ae
      filter_upwards
        [(volume : Measure (Euclidean d)).ae_ne
          (0 : Euclidean d)] with x hx
      exact gaussianMellinMixture_parameter_integral
        f b hb x hx
    _ = Complex.Gamma b *
          (∫ x : Euclidean d,
            f x * (‖x‖ : ℂ) ^ (-(2 * b))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
theorem gaussianMellinPairingProfile_fourier {d : ℕ}
    (f : TestFunction d) (a : ℝ) (ha : 0 < a) :
    gaussianMellinPairingProfile (𝓕 f : TestFunction d) a =
      ((Real.pi : ℂ) / (a : ℂ)) ^ ((d : ℂ) / 2) *
        gaussianMellinPairingProfile f (Real.pi ^ 2 / a) := by
  unfold gaussianMellinPairingProfile
  rw [fourier_gaussianMellin_pairing f a ha,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold gaussianMellinWeight
  push_cast
  have hexp :
      Complex.exp
          (-((Real.pi : ℂ) ^ 2) * (‖x‖ : ℂ) ^ 2 / (a : ℂ)) =
        Complex.exp
          (-((Real.pi : ℂ) ^ 2 / (a : ℂ) * (‖x‖ : ℂ) ^ 2)) := by
    congr 1
    ring
  rw [hexp]
  ring
theorem mellin_gaussianMellinPairingProfile_fourier {d : ℕ}
    (f : TestFunction d) (b : ℂ) :
    mellin
        (gaussianMellinPairingProfile (𝓕 f : TestFunction d)) b =
      (Real.pi : ℂ) ^ ((d : ℂ) / 2) *
        (((Real.pi ^ 2 : ℝ) : ℂ) ^
          (b - (d : ℂ) / 2) *
            mellin (gaussianMellinPairingProfile f)
              ((d : ℂ) / 2 - b)) := by
  let q : ℂ := (d : ℂ) / 2
  let P : ℝ := Real.pi ^ 2
  have hP : 0 < P := by
    try dsimp [P]
    positivity
  have hrewrite :
      mellin
          (gaussianMellinPairingProfile
            (𝓕 f : TestFunction d)) b =
        mellin
          (fun a : ℝ =>
            (Real.pi : ℂ) ^ q •
              ((a : ℂ) ^ (-q) •
                gaussianMellinPairingProfile f (P * a⁻¹))) b := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro a ha
    simp only [smul_eq_mul]
    rw [gaussianMellinPairingProfile_fourier f a ha]
    change
      (a : ℂ) ^ (b - 1) *
          (((Real.pi : ℂ) / (a : ℂ)) ^ q *
            gaussianMellinPairingProfile f (P / a)) =
        (a : ℂ) ^ (b - 1) *
          ((Real.pi : ℂ) ^ q *
            ((a : ℂ) ^ (-q) *
              gaussianMellinPairingProfile f (P * a⁻¹)))
    rw [gaussianMellin_div_cpow Real.pi a Real.pi_pos ha q,
      div_eq_mul_inv]
    ring
  calc
    mellin
        (gaussianMellinPairingProfile
          (𝓕 f : TestFunction d)) b =
        mellin
          (fun a : ℝ =>
            (Real.pi : ℂ) ^ q •
              ((a : ℂ) ^ (-q) •
                gaussianMellinPairingProfile f (P * a⁻¹))) b :=
      hrewrite
    _ = (Real.pi : ℂ) ^ q *
          mellin
            (fun a : ℝ =>
              (a : ℂ) ^ (-q) •
                gaussianMellinPairingProfile f (P * a⁻¹)) b := by
      simpa only [smul_eq_mul] using!
        (mellin_const_smul
          (fun a : ℝ =>
            (a : ℂ) ^ (-q) •
              gaussianMellinPairingProfile f (P * a⁻¹))
          b ((Real.pi : ℂ) ^ q))
    _ = (Real.pi : ℂ) ^ q *
          mellin
            (fun a : ℝ =>
              gaussianMellinPairingProfile f (P * a⁻¹))
            (b - q) := by
      rw [mellin_cpow_smul]
      simp only [sub_eq_add_neg]
    _ = (Real.pi : ℂ) ^ q *
          mellin
            (fun a : ℝ => gaussianMellinPairingProfile f (P * a))
            (-(b - q)) := by
      rw [mellin_comp_inv
        (fun a : ℝ => gaussianMellinPairingProfile f (P * a))
        (b - q)]
    _ = (Real.pi : ℂ) ^ q *
          ((P : ℂ) ^ (b - q) *
            mellin (gaussianMellinPairingProfile f) (q - b)) := by
      rw [mellin_comp_mul_left
        (gaussianMellinPairingProfile f) (-(b - q)) hP]
      simp only [smul_eq_mul, neg_sub]
    _ = (Real.pi : ℂ) ^ ((d : ℂ) / 2) *
          (((Real.pi ^ 2 : ℝ) : ℂ) ^
            (b - (d : ℂ) / 2) *
              mellin (gaussianMellinPairingProfile f)
                ((d : ℂ) / 2 - b)) := by
      rfl
theorem fourier_riesz_pairing {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (b : ℂ)
    (hb : 0 < b.re) (hbd : 2 * b.re < (d : ℝ)) :
    Complex.Gamma b *
        (∫ ξ : Euclidean d,
          (𝓕 f : TestFunction d) ξ *
            (‖ξ‖ : ℂ) ^ (-(2 * b))) =
      (Real.pi : ℂ) ^ ((d : ℂ) / 2) *
        (((Real.pi ^ 2 : ℝ) : ℂ) ^
          (b - (d : ℂ) / 2) *
            (Complex.Gamma ((d : ℂ) / 2 - b) *
              (∫ x : Euclidean d,
                f x *
                  (‖x‖ : ℂ) ^
                    (-(2 * ((d : ℂ) / 2 - b)))))) := by
  have hdual : 0 < (((d : ℂ) / 2 - b).re) := by
    norm_num
    linarith
  have hdual_dimension :
      2 * (((d : ℂ) / 2 - b).re) < (d : ℝ) := by
    norm_num
    linarith
  calc
    Complex.Gamma b *
        (∫ ξ : Euclidean d,
          (𝓕 f : TestFunction d) ξ *
            (‖ξ‖ : ℂ) ^ (-(2 * b))) =
          mellin
            (gaussianMellinPairingProfile
              (𝓕 f : TestFunction d)) b :=
      (mellin_gaussianMellinPairingProfile
        hd (𝓕 f : TestFunction d) b hb hbd).symm
    _ = (Real.pi : ℂ) ^ ((d : ℂ) / 2) *
          (((Real.pi ^ 2 : ℝ) : ℂ) ^
            (b - (d : ℂ) / 2) *
              mellin (gaussianMellinPairingProfile f)
                ((d : ℂ) / 2 - b)) :=
      mellin_gaussianMellinPairingProfile_fourier f b
    _ = (Real.pi : ℂ) ^ ((d : ℂ) / 2) *
          (((Real.pi ^ 2 : ℝ) : ℂ) ^
            (b - (d : ℂ) / 2) *
              (Complex.Gamma ((d : ℂ) / 2 - b) *
                (∫ x : Euclidean d,
                  f x *
                    (‖x‖ : ℂ) ^
                      (-(2 * ((d : ℂ) / 2 - b)))))) := by
      rw [mellin_gaussianMellinPairingProfile hd f
        ((d : ℂ) / 2 - b) hdual hdual_dimension]
theorem fourier_riesz_pairing_strip {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (s : ℂ)
    (hs : 0 < s.re) (hsd : s.re < (d : ℝ)) :
    Complex.Gamma (((d : ℂ) - s) / 2) *
        (∫ ξ : Euclidean d,
          (𝓕 f : TestFunction d) ξ *
            (‖ξ‖ : ℂ) ^ (s - (d : ℂ))) =
      (Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
        (Complex.Gamma (s / 2) *
          (∫ x : Euclidean d,
            f x * (‖x‖ : ℂ) ^ (-s))) := by
  let b : ℂ := ((d : ℂ) - s) / 2
  have hb : 0 < b.re := by
    try dsimp [b]
    norm_num
    linarith
  have hbd : 2 * b.re < (d : ℝ) := by
    try dsimp [b]
    norm_num
    linarith
  have hleft : -(2 * b) = s - (d : ℂ) := by
    try dsimp [b]
    ring
  have hdual : (d : ℂ) / 2 - b = s / 2 := by
    try dsimp [b]
    ring
  have hpi :
      2 * b - (d : ℂ) / 2 = (d : ℂ) / 2 - s := by
    try dsimp [b]
    ring
  have hright : -(2 * (s / 2)) = -s := by
    ring
  have h := fourier_riesz_pairing hd f b hb hbd
  rw [← mul_assoc] at h
  rw [gaussianMellin_pi_coefficient b ((d : ℂ) / 2),
    hleft, hdual, hpi, hright] at h
  simpa only [b] using! h
theorem radial_fourier_mellin_strip {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (s : ℂ) (hs : 0 < s.re) (hsd : s.re < (d : ℝ)) :
    mellin (radialProfile hd (𝓕 f : TestFunction d)) s =
      ((Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
        Complex.Gamma (s / 2) /
          Complex.Gamma (((d : ℂ) - s) / 2)) *
            mellin (radialProfile hd f) ((d : ℂ) - s) := by
  have hdual : 0 < ((((d : ℂ) - s) / 2).re) := by
    norm_num
    linarith
  have hgamma :
      Complex.Gamma (((d : ℂ) - s) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hdual
  have hsurface : (radialSurfaceArea d : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (radialSurfaceArea_pos hd).ne'
  have hhat :=
    integral_radialProfile_cpow hd
      (𝓕 f : TestFunction d)
      (gaussianMellin_fourier_radial hf) s
  have hprimal :
      (∫ x : Euclidean d,
        f x * (‖x‖ : ℂ) ^ (-s)) =
        radialSurfaceArea d •
          mellin (radialProfile hd f) ((d : ℂ) - s) := by
    have hexponent :
        ((d : ℂ) - s) - (d : ℂ) = -s := by
      ring
    simpa only [hexponent] using!
      (integral_radialProfile_cpow hd f hf ((d : ℂ) - s))
  have h := fourier_riesz_pairing_strip hd f s hs hsd
  rw [hhat, hprimal] at h
  simp only [Complex.real_smul] at h
  have hcancel :
      Complex.Gamma (((d : ℂ) - s) / 2) *
          mellin (radialProfile hd (𝓕 f : TestFunction d)) s =
        (Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
          (Complex.Gamma (s / 2) *
            mellin (radialProfile hd f) ((d : ℂ) - s)) := by
    apply mul_left_cancel₀ hsurface
    calc
      (radialSurfaceArea d : ℂ) *
          (Complex.Gamma (((d : ℂ) - s) / 2) *
            mellin (radialProfile hd (𝓕 f : TestFunction d)) s) =
          Complex.Gamma (((d : ℂ) - s) / 2) *
            ((radialSurfaceArea d : ℂ) *
              mellin (radialProfile hd (𝓕 f : TestFunction d)) s) := by
        ring
      _ = (Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
            (Complex.Gamma (s / 2) *
              ((radialSurfaceArea d : ℂ) *
                mellin (radialProfile hd f) ((d : ℂ) - s))) := h
      _ = (radialSurfaceArea d : ℂ) *
            ((Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
              (Complex.Gamma (s / 2) *
                mellin (radialProfile hd f) ((d : ℂ) - s))) := by
        ring
  calc
    mellin (radialProfile hd (𝓕 f : TestFunction d)) s =
        ((Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
          (Complex.Gamma (s / 2) *
            mellin (radialProfile hd f) ((d : ℂ) - s))) /
            Complex.Gamma (((d : ℂ) - s) / 2) := by
      apply (eq_div_iff hgamma).2
      simpa only [mul_comm] using! hcancel
    _ = ((Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
          Complex.Gamma (s / 2) /
            Complex.Gamma (((d : ℂ) - s) / 2)) *
              mellin (radialProfile hd f) ((d : ℂ) - s) := by
      ring
theorem radialMellinMultiplier {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (t : ℝ) :
    radialMellinFrequency hd (𝓕 f : TestFunction d) t =
      mellinMultiplier ((d : ℝ) / 2) t *
        radialMellinFrequency hd f (-t) := by
  let q : ℂ := (d : ℂ) / 2
  let s : ℂ := q - Complex.I * (t : ℂ)
  have hs : 0 < s.re := by
    try dsimp [s, q]
    norm_num
    exact Nat.cast_pos.mpr hd
  have hsd : s.re < (d : ℝ) := by
    try dsimp [s, q]
    norm_num
    exact Nat.cast_pos.mpr hd
  have hphase :
      (Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) =
        Complex.exp
          (Complex.I * (t : ℂ) *
            (Real.log Real.pi : ℂ)) := by
    have hexponent :
        (d : ℂ) / 2 - s = Complex.I * (t : ℂ) := by
      try dsimp [s, q]
      ring
    rw [hexponent,
      Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'),
      ← Complex.ofReal_log Real.pi_pos.le]
    congr 1
    ring
  have hcomplement :
      (d : ℂ) - s = q + Complex.I * (t : ℂ) := by
    try dsimp [s, q]
    ring
  have h := radial_fourier_mellin_strip hd f hf s hs hsd
  rw [hphase, hcomplement] at h
  unfold radialMellinFrequency mellinFrequency mellinMultiplier
  simpa [s, q, mul_neg, sub_neg_eq_add] using! h
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
def shellOscillation (B T : ℝ) : ℝ :=
  ∫ a in B..B + 1, (1 - Real.cos (a * T))
theorem cosh_ratio_upper {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    Real.cosh ((1 + δ) * a) / Real.cosh a ≤ Real.exp (δ * a) := by
  apply (div_le_iff₀ (Real.cosh_pos a)).2
  rw [show (1 + δ) * a = a + δ * a by ring, Real.cosh_add]
  have hs : Real.sinh a ≤ Real.cosh a :=
    (Real.sinh_lt_cosh (x := a)).le
  have hq : 0 ≤ Real.sinh (δ * a) :=
    Real.sinh_nonneg_iff.mpr (mul_nonneg hδ ha)
  calc
    Real.cosh a * Real.cosh (δ * a) +
        Real.sinh a * Real.sinh (δ * a)
      ≤ Real.cosh a * Real.cosh (δ * a) +
          Real.cosh a * Real.sinh (δ * a) := by gcongr
    _ = Real.cosh a *
          (Real.cosh (δ * a) + Real.sinh (δ * a)) := by ring
    _ = Real.exp (δ * a) * Real.cosh a := by
      rw [Real.cosh_eq (δ * a), Real.sinh_eq (δ * a)]
      ring
def positiveShellDensity (ε a : ℝ) : ℝ :=
  shellWeight ε / Real.cosh a
def positiveShellDamping (ε ℓ δ T : ℝ) : ℝ :=
  ℓ * ∫ a in shellLocation ε..shellLocation ε + 1,
    positiveShellDensity ε a * Real.cosh ((1 + δ) * a) *
      (1 - Real.cos (a * T))
def positiveShellRadiusContribution (ε : ℝ) : ℝ :=
  ∫ a in shellLocation ε..shellLocation ε + 1,
    positiveShellDensity ε a * a *
      Real.sinh ((1 + ε / 4) * a)
theorem positiveShellRadiusContribution_bounds {ε : ℝ} (hε : 0 < ε) :
    0 ≤ positiveShellRadiusContribution ε ∧
      positiveShellRadiusContribution ε ≤
        (shellLocation ε + 1) * shellWeight ε *
          Real.exp ((ε / 4) * (shellLocation ε + 1)) := by
  let B : ℝ := shellLocation ε
  let δ : ℝ := ε / 4
  let K : ℝ := (B + 1) * shellWeight ε * Real.exp (δ * (B + 1))
  have hB : 0 ≤ B := by
    try dsimp [B, shellLocation]
    positivity
  have hδ : 0 ≤ δ := by
    try dsimp [δ]
    positivity
  have hQ : 0 < shellWeight ε := shellWeight_pos ε
  have hden : Continuous (fun a : ℝ => positiveShellDensity ε a) := by
    unfold positiveShellDensity
    exact continuous_const.div Real.continuous_cosh
      (fun a => (Real.cosh_pos a).ne')
  have hright : Continuous
      (fun a : ℝ => positiveShellDensity ε a * a *
        Real.sinh ((1 + δ) * a)) := by
    have hsinh : Continuous (fun a : ℝ => Real.sinh ((1 + δ) * a)) := by
      fun_prop
    exact (hden.mul continuous_id).mul hsinh
  have hnonneg : ∀ a ∈ Set.Icc B (B + 1),
      0 ≤ positiveShellDensity ε a * a *
        Real.sinh ((1 + δ) * a) := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have hden0 : 0 ≤ positiveShellDensity ε a := by
      unfold positiveShellDensity
      exact (div_pos hQ (Real.cosh_pos a)).le
    exact mul_nonneg (mul_nonneg hden0 ha0)
      (Real.sinh_nonneg_iff.mpr
        (mul_nonneg (by linarith : 0 ≤ 1 + δ) ha0))
  have hpoint : ∀ a ∈ Set.Icc B (B + 1),
      positiveShellDensity ε a * a * Real.sinh ((1 + δ) * a) ≤ K := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have hden0 : 0 ≤ positiveShellDensity ε a := by
      unfold positiveShellDensity
      exact (div_pos hQ (Real.cosh_pos a)).le
    have hratio := cosh_ratio_upper ha0 hδ
    have he := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ha.2 hδ)
    calc
      positiveShellDensity ε a * a * Real.sinh ((1 + δ) * a)
        ≤ positiveShellDensity ε a * a *
          Real.cosh ((1 + δ) * a) := by
            gcongr
            exact (Real.sinh_lt_cosh (x := (1 + δ) * a)).le
      _ = shellWeight ε * a *
          (Real.cosh ((1 + δ) * a) / Real.cosh a) := by
            unfold positiveShellDensity
            ring
      _ ≤ shellWeight ε * (B + 1) *
          Real.exp (δ * (B + 1)) := by
            gcongr
            · exact ha.2
            · exact hratio.trans he
      _ = K := by
            try dsimp [K]
            ring
  constructor
  · change 0 ≤ ∫ a in B..B + 1,
        positiveShellDensity ε a * a * Real.sinh ((1 + δ) * a)
    exact intervalIntegral.integral_nonneg (by linarith) hnonneg
  · change (∫ a in B..B + 1,
        positiveShellDensity ε a * a * Real.sinh ((1 + δ) * a)) ≤ K
    have hmono := intervalIntegral.integral_mono_on (μ := volume)
      (show B ≤ B + 1 by linarith)
      (hright.intervalIntegrable _ _)
      ((continuous_const : Continuous (fun _ : ℝ => K)).intervalIntegrable _ _)
      hpoint
    simpa using! hmono
def shortShellDensity (ε a : ℝ) : ℝ :=
  -(shortMargin ε a * Real.exp (-2 * a) /
    (2 * a ^ 2 * Real.cosh a))
def mellinShellPhase (ε : ℝ) (z : ℂ) : ℂ :=
  (∫ a in shortCutoff ε..shortEndpoint ε,
    (shortShellDensity ε a : ℂ) *
      (Complex.cos ((a : ℂ) * z) - 1)) +
  (∫ a in shellLocation ε..shellLocation ε + 1,
    (positiveShellDensity ε a : ℂ) *
      (Complex.cos ((a : ℂ) * z) - 1))
theorem mellinShellPhase_neg (ε : ℝ) (z : ℂ) :
    mellinShellPhase ε (-z) = mellinShellPhase ε z := by
  unfold mellinShellPhase
  congr 1
  · apply intervalIntegral.integral_congr
    intro a _
    simp
  · apply intervalIntegral.integral_congr
    intro a _
    simp
def realOscillatoryShellPhase (ε t : ℝ) : ℝ :=
  (∫ a in shortCutoff ε..shortEndpoint ε,
    shortShellDensity ε a * (Real.cos (a * t) - 1)) +
  (∫ a in shellLocation ε..shellLocation ε + 1,
    positiveShellDensity ε a * (Real.cos (a * t) - 1))
def realHyperbolicShellPhase (ε u : ℝ) : ℝ :=
  (∫ a in shortCutoff ε..shortEndpoint ε,
    shortShellDensity ε a * (Real.cosh (a * u) - 1)) +
  (∫ a in shellLocation ε..shellLocation ε + 1,
    positiveShellDensity ε a * (Real.cosh (a * u) - 1))
theorem mellinShellPhase_ofReal (ε t : ℝ) :
    mellinShellPhase ε (t : ℂ) =
      (realOscillatoryShellPhase ε t : ℂ) := by
  unfold mellinShellPhase realOscillatoryShellPhase
  push_cast
  congr 1
  · calc
      (∫ a in shortCutoff ε..shortEndpoint ε,
        (shortShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * (t : ℂ)) - 1)) =
          ∫ a in shortCutoff ε..shortEndpoint ε,
            (↑(shortShellDensity ε a *
              (Real.cos (a * t) - 1)) : ℂ) := by
              apply intervalIntegral.integral_congr
              intro a _
              try dsimp
              rw [show (a : ℂ) * (t : ℂ) =
                ((a * t : ℝ) : ℂ) by
                  push_cast
                  rfl,
                ← Complex.ofReal_cos]
              push_cast
              rfl
      _ = (↑(∫ a in shortCutoff ε..shortEndpoint ε,
            shortShellDensity ε a * (Real.cos (a * t) - 1)) : ℂ) :=
          intervalIntegral.integral_ofReal
  · calc
      (∫ a in shellLocation ε..shellLocation ε + 1,
        (positiveShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * (t : ℂ)) - 1)) =
          ∫ a in shellLocation ε..shellLocation ε + 1,
            (↑(positiveShellDensity ε a *
              (Real.cos (a * t) - 1)) : ℂ) := by
              apply intervalIntegral.integral_congr
              intro a _
              try dsimp
              rw [show (a : ℂ) * (t : ℂ) =
                ((a * t : ℝ) : ℂ) by
                  push_cast
                  rfl,
                ← Complex.ofReal_cos]
              push_cast
              rfl
      _ = (↑(∫ a in shellLocation ε..shellLocation ε + 1,
            positiveShellDensity ε a * (Real.cos (a * t) - 1)) : ℂ) :=
          intervalIntegral.integral_ofReal
theorem mellinShellPhase_imaginary (ε u : ℝ) :
    mellinShellPhase ε (Complex.I * (u : ℂ)) =
      (realHyperbolicShellPhase ε u : ℂ) := by
  unfold mellinShellPhase realHyperbolicShellPhase
  push_cast
  congr 1
  · calc
      (∫ a in shortCutoff ε..shortEndpoint ε,
        (shortShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * (Complex.I * (u : ℂ))) - 1)) =
          ∫ a in shortCutoff ε..shortEndpoint ε,
            (↑(shortShellDensity ε a *
              (Real.cosh (a * u) - 1)) : ℂ) := by
              apply intervalIntegral.integral_congr
              intro a _
              try dsimp
              rw [show (a : ℂ) * (Complex.I * (u : ℂ)) =
                ((a * u : ℝ) : ℂ) * Complex.I by
                  push_cast
                  ring,
                Complex.cos_mul_I, ← Complex.ofReal_cosh]
              push_cast
              rfl
      _ = (↑(∫ a in shortCutoff ε..shortEndpoint ε,
            shortShellDensity ε a * (Real.cosh (a * u) - 1)) : ℂ) :=
          intervalIntegral.integral_ofReal
  · calc
      (∫ a in shellLocation ε..shellLocation ε + 1,
        (positiveShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * (Complex.I * (u : ℂ))) - 1)) =
          ∫ a in shellLocation ε..shellLocation ε + 1,
            (↑(positiveShellDensity ε a *
              (Real.cosh (a * u) - 1)) : ℂ) := by
              apply intervalIntegral.integral_congr
              intro a _
              try dsimp
              rw [show (a : ℂ) * (Complex.I * (u : ℂ)) =
                ((a * u : ℝ) : ℂ) * Complex.I by
                  push_cast
                  ring,
                Complex.cos_mul_I, ← Complex.ofReal_cosh]
              push_cast
              rfl
      _ = (↑(∫ a in shellLocation ε..shellLocation ε + 1,
            positiveShellDensity ε a * (Real.cosh (a * u) - 1)) : ℂ) :=
          intervalIntegral.integral_ofReal
theorem positiveShellDensity_continuous (ε : ℝ) :
    Continuous (positiveShellDensity ε) := by
  unfold positiveShellDensity
  exact continuous_const.div Real.continuous_cosh
    (fun a => (Real.cosh_pos a).ne')
theorem shortShellDensity_intervalIntegrable {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    IntervalIntegrable (shortShellDensity ε) volume
      (shortCutoff ε) (shortEndpoint ε) := by
  have hn : Continuous (fun a : ℝ =>
      shortMargin ε a * Real.exp (-2 * a)) := by
    unfold shortMargin
    fun_prop
  have hd : Continuous (fun a : ℝ =>
      2 * a ^ 2 * Real.cosh a) := by
    fun_prop
  apply ContinuousOn.intervalIntegrable_of_Icc horder
  unfold shortShellDensity
  apply (hn.continuousOn.div hd.continuousOn ?_).neg
  intro a ha
  have hcutoff : 0 < shortCutoff ε := by
    unfold shortCutoff
    positivity
  have ha0 : 0 < a := hcutoff.trans_le ha.1
  positivity
theorem shortShellOscillatoryIntegral_continuous {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Continuous (fun t : ℝ =>
      ∫ a in shortCutoff ε..shortEndpoint ε,
        shortShellDensity ε a * (Real.cos (a * t) - 1)) := by
  have hcutoff : 0 < shortCutoff ε := by
    unfold shortCutoff
    positivity
  let w : ℝ → ℝ := fun a =>
    shortShellDensity ε (max a (shortCutoff ε))
  have hmax (a : ℝ) : 0 < max a (shortCutoff ε) :=
    hcutoff.trans_le (le_max_right _ _)
  have hw : Continuous w := by
    have hn : Continuous (fun a : ℝ =>
        shortMargin ε (max a (shortCutoff ε)) *
          Real.exp (-2 * max a (shortCutoff ε))) := by
      unfold shortMargin
      fun_prop
    have hd : Continuous (fun a : ℝ =>
        2 * (max a (shortCutoff ε)) ^ 2 *
          Real.cosh (max a (shortCutoff ε))) := by
      fun_prop
    try dsimp [w]
    unfold shortShellDensity
    exact (hn.div hd (fun a => by positivity [hmax a])).neg
  let F : ℝ → ℝ → ℝ := fun t a =>
    w a * (Real.cos (a * t) - 1)
  have hF : Continuous (Function.uncurry F) := by
    try dsimp [F, Function.uncurry]
    exact (hw.comp continuous_snd).mul (by fun_prop)
  have hparam : Continuous (fun t : ℝ =>
      ∫ a in Set.Icc (shortCutoff ε) (shortEndpoint ε), F t a) :=
    continuous_parametric_integral_of_continuous
      (μ := volume) hF isCompact_Icc
  have hident (t : ℝ) :
      (∫ a in shortCutoff ε..shortEndpoint ε,
        shortShellDensity ε a * (Real.cos (a * t) - 1)) =
      (∫ a in Set.Icc (shortCutoff ε) (shortEndpoint ε), F t a) := by
    rw [intervalIntegral.integral_of_le horder,
      ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro a ha
    try dsimp [F, w]
    rw [max_eq_left ha.1]
  exact hparam.congr (fun t => (hident t).symm)
theorem positiveShellOscillatoryIntegral_continuous (ε : ℝ) :
    Continuous (fun t : ℝ =>
      ∫ a in shellLocation ε..shellLocation ε + 1,
        positiveShellDensity ε a * (Real.cos (a * t) - 1)) := by
  let F : ℝ → ℝ → ℝ := fun t a =>
    positiveShellDensity ε a * (Real.cos (a * t) - 1)
  have hF : Continuous (Function.uncurry F) := by
    try dsimp [F, Function.uncurry]
    exact ((positiveShellDensity_continuous ε).comp continuous_snd).mul
      (by fun_prop)
  have hparam : Continuous (fun t : ℝ =>
      ∫ a in Set.Icc (shellLocation ε) (shellLocation ε + 1), F t a) :=
    continuous_parametric_integral_of_continuous
      (μ := volume) hF isCompact_Icc
  have horder : shellLocation ε ≤ shellLocation ε + 1 := by
    linarith
  have hident (t : ℝ) :
      (∫ a in shellLocation ε..shellLocation ε + 1,
        positiveShellDensity ε a * (Real.cos (a * t) - 1)) =
      (∫ a in Set.Icc (shellLocation ε) (shellLocation ε + 1),
        F t a) := by
    rw [intervalIntegral.integral_of_le horder,
      ← integral_Icc_eq_integral_Ioc]
  exact hparam.congr (fun t => (hident t).symm)
theorem realOscillatoryShellPhase_continuous {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Continuous (realOscillatoryShellPhase ε) := by
  unfold realOscillatoryShellPhase
  exact (shortShellOscillatoryIntegral_continuous hε horder).add
    (positiveShellOscillatoryIntegral_continuous ε)
theorem complexShellInterval_differentiable
    (w : ℝ → ℝ) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) :
    Differentiable ℂ (fun z : ℂ =>
      ∫ x in a..b,
        (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)) := by
  let F : ℂ → ℝ → ℂ := fun z x =>
    (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)
  let F' : ℂ → ℝ → ℂ := fun z x =>
    (w x : ℂ) * (-(Complex.sin ((x : ℂ) * z)) * (x : ℂ))
  have hF (z : ℂ) : Continuous (F z) := by
    try dsimp [F]
    exact (Complex.continuous_ofReal.comp hw).mul (by fun_prop)
  have hF' (z : ℂ) : Continuous (F' z) := by
    try dsimp [F']
    exact (Complex.continuous_ofReal.comp hw).mul (by fun_prop)
  have hF'joint : Continuous (Function.uncurry F') := by
    try dsimp [F', Function.uncurry]
    exact (Complex.continuous_ofReal.comp
      (hw.comp continuous_snd)).mul (by fun_prop)
  have hderiv (x : ℝ) (z : ℂ) :
      HasDerivAt (fun u : ℂ => F u x) (F' z x) z := by
    have hlinear : HasDerivAt
        (fun u : ℂ => (x : ℂ) * u) (x : ℂ) z := by
      simpa using! (hasDerivAt_id z).const_mul (x : ℂ)
    have hcos := (Complex.hasDerivAt_cos
      ((x : ℂ) * z)).comp z hlinear
    simpa [F, F', mul_assoc] using!
      (hcos.sub_const (1 : ℂ)).const_mul (w x : ℂ)
  have hrewrite :
      (fun z : ℂ =>
        ∫ x in a..b,
          (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)) =
        (fun z : ℂ => ∫ x in Set.Icc a b, F z x) := by
    funext z
    rw [intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc]
  rw [hrewrite]
  intro z₀
  have hcompact :
      IsCompact (Metric.closedBall z₀ 1 ×ˢ Set.Icc a b) :=
    (isCompact_closedBall z₀ 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ :=
    hcompact.bddAbove_image hF'joint.norm.continuousOn
  have hbound : ∀ᵐ x ∂volume.restrict (Set.Icc a b),
      ∀ z ∈ Metric.ball z₀ 1, ‖F' z x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    intro z hz
    have hpair :
        (z, x) ∈ Metric.closedBall z₀ 1 ×ˢ Set.Icc a b :=
      ⟨Metric.ball_subset_closedBall hz, hx⟩
    exact hC (Set.mem_image_of_mem
      (fun p : ℂ × ℝ => ‖F' p.1 p.2‖)
      hpair)
  have hmeas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (F z)
        (volume.restrict (Set.Icc a b)) :=
    Eventually.of_forall (fun z => (hF z).aestronglyMeasurable)
  have hint : Integrable (F z₀)
      (volume.restrict (Set.Icc a b)) :=
    (hF z₀).integrableOn_Icc
  have hderivmeas : AEStronglyMeasurable (F' z₀)
      (volume.restrict (Set.Icc a b)) :=
    (hF' z₀).aestronglyMeasurable
  have hconstant : Integrable (fun _ : ℝ => C)
      (volume.restrict (Set.Icc a b)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hdifferentiable : ∀ᵐ x ∂volume.restrict (Set.Icc a b),
      ∀ z ∈ Metric.ball z₀ 1,
        HasDerivAt (fun u : ℂ => F u x) (F' z x) z :=
    Eventually.of_forall (fun x z _ => hderiv x z)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc a b))
    (s := Metric.ball z₀ 1) (bound := fun _ : ℝ => C)
    (Metric.ball_mem_nhds z₀ zero_lt_one)
    hmeas hint hderivmeas hbound hconstant
    hdifferentiable).2.differentiableAt
theorem mellinShellPhase_differentiable {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Differentiable ℂ (mellinShellPhase ε) := by
  have hcutoff : 0 < shortCutoff ε := by
    unfold shortCutoff
    positivity
  let w : ℝ → ℝ := fun a =>
    shortShellDensity ε (max a (shortCutoff ε))
  have hmax (a : ℝ) : 0 < max a (shortCutoff ε) :=
    hcutoff.trans_le (le_max_right _ _)
  have hw : Continuous w := by
    have hn : Continuous (fun a : ℝ =>
        shortMargin ε (max a (shortCutoff ε)) *
          Real.exp (-2 * max a (shortCutoff ε))) := by
      unfold shortMargin
      fun_prop
    have hd : Continuous (fun a : ℝ =>
        2 * (max a (shortCutoff ε)) ^ 2 *
          Real.cosh (max a (shortCutoff ε))) := by
      fun_prop
    try dsimp [w]
    unfold shortShellDensity
    exact (hn.div hd (fun a => by positivity [hmax a])).neg
  have hshort_eq :
      (fun z : ℂ =>
        ∫ a in shortCutoff ε..shortEndpoint ε,
          (shortShellDensity ε a : ℂ) *
            (Complex.cos ((a : ℂ) * z) - 1)) =
      (fun z : ℂ =>
        ∫ a in shortCutoff ε..shortEndpoint ε,
          (w a : ℂ) *
            (Complex.cos ((a : ℂ) * z) - 1)) := by
    funext z
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le horder] at ha
    try dsimp [w]
    rw [max_eq_left ha.1]
  have hshort : Differentiable ℂ (fun z : ℂ =>
      ∫ a in shortCutoff ε..shortEndpoint ε,
        (shortShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * z) - 1)) := by
    rw [hshort_eq]
    exact complexShellInterval_differentiable w hw horder
  have hremote : shellLocation ε ≤ shellLocation ε + 1 := by
    linarith
  have hpositive : Differentiable ℂ (fun z : ℂ =>
      ∫ a in shellLocation ε..shellLocation ε + 1,
        (positiveShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * z) - 1)) :=
    complexShellInterval_differentiable
      (positiveShellDensity ε)
      (positiveShellDensity_continuous ε) hremote
  exact hshort.add hpositive
def saddleShellTotalVariation (ε : ℝ) : ℝ :=
  (∫ a in shortCutoff ε..shortEndpoint ε,
    |shortShellDensity ε a|) +
  (∫ a in shellLocation ε..shellLocation ε + 1,
    |positiveShellDensity ε a|)
theorem abs_realOscillatoryShellPhase_le {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (t : ℝ) :
    |realOscillatoryShellPhase ε t| ≤
      2 * saddleShellTotalVariation ε := by
  have hcos (a : ℝ) : |Real.cos (a * t) - 1| ≤ 2 := by
    apply (abs_le).2
    constructor
    · linarith [Real.neg_one_le_cos (a * t)]
    · linarith [Real.cos_le_one (a * t)]
  have hosc : Continuous (fun a : ℝ => Real.cos (a * t) - 1) := by
    fun_prop
  have hs := shortShellDensity_intervalIntegrable hε horder
  have hp : IntervalIntegrable (positiveShellDensity ε) volume
      (shellLocation ε) (shellLocation ε + 1) :=
    (positiveShellDensity_continuous ε).intervalIntegrable
      (shellLocation ε) (shellLocation ε + 1)
  have hshort :
      |∫ a in shortCutoff ε..shortEndpoint ε,
        shortShellDensity ε a * (Real.cos (a * t) - 1)| ≤
          2 * ∫ a in shortCutoff ε..shortEndpoint ε,
            |shortShellDensity ε a| := by
    calc
      |∫ a in shortCutoff ε..shortEndpoint ε,
          shortShellDensity ε a * (Real.cos (a * t) - 1)|
        ≤ ∫ a in shortCutoff ε..shortEndpoint ε,
            |shortShellDensity ε a * (Real.cos (a * t) - 1)| :=
              intervalIntegral.abs_integral_le_integral_abs horder
      _ ≤ ∫ a in shortCutoff ε..shortEndpoint ε,
            2 * |shortShellDensity ε a| := by
              apply intervalIntegral.integral_mono_on horder
                (hs.mul_continuousOn hosc.continuousOn).abs
                (hs.abs.const_mul 2)
              intro a _
              rw [abs_mul]
              calc
                |shortShellDensity ε a| *
                    |Real.cos (a * t) - 1|
                  ≤ |shortShellDensity ε a| * 2 := by
                      gcongr
                      exact hcos a
                _ = 2 * |shortShellDensity ε a| := by ring
      _ = 2 * ∫ a in shortCutoff ε..shortEndpoint ε,
            |shortShellDensity ε a| := by
              rw [intervalIntegral.integral_const_mul]
  have hpositive :
      |∫ a in shellLocation ε..shellLocation ε + 1,
        positiveShellDensity ε a * (Real.cos (a * t) - 1)| ≤
          2 * ∫ a in shellLocation ε..shellLocation ε + 1,
            |positiveShellDensity ε a| := by
    have hB : shellLocation ε ≤ shellLocation ε + 1 := by
      linarith
    calc
      |∫ a in shellLocation ε..shellLocation ε + 1,
          positiveShellDensity ε a * (Real.cos (a * t) - 1)|
        ≤ ∫ a in shellLocation ε..shellLocation ε + 1,
            |positiveShellDensity ε a * (Real.cos (a * t) - 1)| :=
              intervalIntegral.abs_integral_le_integral_abs hB
      _ ≤ ∫ a in shellLocation ε..shellLocation ε + 1,
            2 * |positiveShellDensity ε a| := by
              apply intervalIntegral.integral_mono_on hB
                (hp.mul_continuousOn hosc.continuousOn).abs
                (hp.abs.const_mul 2)
              intro a _
              rw [abs_mul]
              calc
                |positiveShellDensity ε a| *
                    |Real.cos (a * t) - 1|
                  ≤ |positiveShellDensity ε a| * 2 := by
                      gcongr
                      exact hcos a
                _ = 2 * |positiveShellDensity ε a| := by ring
      _ = 2 * ∫ a in shellLocation ε..shellLocation ε + 1,
            |positiveShellDensity ε a| := by
              rw [intervalIntegral.integral_const_mul]
  unfold realOscillatoryShellPhase saddleShellTotalVariation
  calc
    |(∫ a in shortCutoff ε..shortEndpoint ε,
        shortShellDensity ε a * (Real.cos (a * t) - 1)) +
      (∫ a in shellLocation ε..shellLocation ε + 1,
        positiveShellDensity ε a * (Real.cos (a * t) - 1))|
      ≤ |∫ a in shortCutoff ε..shortEndpoint ε,
          shortShellDensity ε a * (Real.cos (a * t) - 1)| +
        |∫ a in shellLocation ε..shellLocation ε + 1,
          positiveShellDensity ε a * (Real.cos (a * t) - 1)| :=
          abs_add_le _ _
    _ ≤ 2 * (∫ a in shortCutoff ε..shortEndpoint ε,
          |shortShellDensity ε a|) +
        2 * (∫ a in shellLocation ε..shellLocation ε + 1,
          |positiveShellDensity ε a|) :=
          add_le_add hshort hpositive
    _ = 2 * ((∫ a in shortCutoff ε..shortEndpoint ε,
          |shortShellDensity ε a|) +
        (∫ a in shellLocation ε..shellLocation ε + 1,
          |positiveShellDensity ε a|)) := by ring
theorem mellinShellPhase_real_conj (ε t : ℝ) :
    starRingEnd ℂ (mellinShellPhase ε (t : ℂ)) =
      mellinShellPhase ε (t : ℂ) := by
  rw [mellinShellPhase_ofReal]
  exact Complex.conj_ofReal _
def saddleEnvelope (ε ℓ t : ℝ) : ℂ :=
  Complex.exp
      (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ) / 2) *
    Complex.Gamma (((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2) *
    Complex.exp ((ℓ : ℂ) *
      mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ)))
def plusSaddleSpectrum (ε ℓ t : ℝ) : ℂ :=
  saddleEnvelope ε ℓ t *
    plusPolynomial ε ((t : ℂ) / (ℓ : ℂ))
def minusSaddleSpectrum (ε ℓ t : ℝ) : ℂ :=
  saddleEnvelope ε ℓ t *
    minusPolynomial ε ((t : ℂ) / (ℓ : ℂ))
theorem saddleVerticalGamma_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Continuous (fun t : ℝ =>
      Complex.Gamma (((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let z : ℂ := ((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2
  have hz : 0 < z.re := by
    try dsimp [z]
    simpa using! half_pos hℓ
  have hpoles : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have harg : ContinuousAt
      (fun u : ℝ => ((ℓ : ℂ) - Complex.I * (u : ℂ)) / 2) t := by
    fun_prop
  simpa [Function.comp_def] using!
    (Complex.continuousAt_Gamma z hpoles).comp_of_eq harg (by rfl)
theorem saddleShellPhase_continuous {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (ℓ : ℝ) :
    Continuous (fun t : ℝ =>
      mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ))) := by
  have hreal : Continuous (fun t : ℝ =>
      realOscillatoryShellPhase ε (t / ℓ)) :=
    (realOscillatoryShellPhase_continuous hε horder).comp
      (by fun_prop)
  have hcomplex : Continuous (fun t : ℝ =>
      (realOscillatoryShellPhase ε (t / ℓ) : ℂ)) :=
    Complex.continuous_ofReal.comp hreal
  apply hcomplex.congr
  intro t
  rw [show (t : ℂ) / (ℓ : ℂ) = ((t / ℓ : ℝ) : ℂ) by
    push_cast
    rfl, mellinShellPhase_ofReal]
theorem saddleEnvelope_continuous {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Continuous (saddleEnvelope ε ℓ) := by
  have hunit : Continuous (fun t : ℝ =>
      Complex.exp
        (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ) / 2)) := by
    fun_prop
  have hgamma := saddleVerticalGamma_continuous hℓ
  have hphase : Continuous (fun t : ℝ =>
      Complex.exp ((ℓ : ℂ) *
        mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ)))) :=
    Complex.continuous_exp.comp
      (continuous_const.mul (saddleShellPhase_continuous
        hε horder ℓ))
  exact (hunit.mul hgamma).mul hphase
theorem plusSaddleSpectrum_continuous {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Continuous (plusSaddleSpectrum ε ℓ) := by
  have hp : Continuous (fun t : ℝ =>
      plusPolynomial ε ((t : ℂ) / (ℓ : ℂ))) := by
    unfold plusPolynomial
    fun_prop
  exact (saddleEnvelope_continuous hε hℓ horder).mul hp
theorem minusSaddleSpectrum_continuous {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Continuous (minusSaddleSpectrum ε ℓ) := by
  have hp : Continuous (fun t : ℝ =>
      minusPolynomial ε ((t : ℂ) / (ℓ : ℂ))) := by
    unfold minusPolynomial
    fun_prop
  exact (saddleEnvelope_continuous hε hℓ horder).mul hp
def saddleOriginValue (ε ℓ : ℝ) : ℝ :=
  2 * Real.pi ^ (ℓ / 2) *
    Real.exp (ℓ * realHyperbolicShellPhase ε 1) * beta ε
theorem saddleOriginValue_pos {ε : ℝ} (hε : 0 < ε) (ℓ : ℝ) :
    0 < saddleOriginValue ε ℓ := by
  unfold saddleOriginValue
  positivity [beta_pos hε, Real.pi_pos]
def saddleMellinEnvelope (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp
      (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2) *
    Complex.Gamma (z / 2) *
    Complex.exp ((ℓ : ℂ) *
      mellinShellPhase ε
        (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)))
def plusSaddleMellinData (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleMellinEnvelope ε ℓ z *
    plusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))
def minusSaddleMellinData (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleMellinEnvelope ε ℓ z *
    minusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))
def saddleRegularMellinFactor (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp
      (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2) *
    Complex.exp ((ℓ : ℂ) *
      mellinShellPhase ε
        (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)))
def plusSaddleRegularMellinFactor (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleRegularMellinFactor ε ℓ z *
    plusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))
def minusSaddleRegularMellinFactor (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleRegularMellinFactor ε ℓ z *
    minusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))
theorem plusSaddleMellinData_eq_gamma_mul_regular
    (ε ℓ : ℝ) (z : ℂ) :
    plusSaddleMellinData ε ℓ z =
      Complex.Gamma (z / 2) *
        plusSaddleRegularMellinFactor ε ℓ z := by
  unfold plusSaddleMellinData saddleMellinEnvelope
    plusSaddleRegularMellinFactor saddleRegularMellinFactor
  ring
theorem minusSaddleMellinData_eq_gamma_mul_regular
    (ε ℓ : ℝ) (z : ℂ) :
    minusSaddleMellinData ε ℓ z =
      Complex.Gamma (z / 2) *
        minusSaddleRegularMellinFactor ε ℓ z := by
  unfold minusSaddleMellinData saddleMellinEnvelope
    minusSaddleRegularMellinFactor saddleRegularMellinFactor
  ring
theorem saddleRegularMellinFactor_differentiable {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (ℓ : ℝ) :
    Differentiable ℂ (saddleRegularMellinFactor ε ℓ) := by
  have hpi : Differentiable ℂ (fun z : ℂ =>
      Complex.exp
        (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2)) := by
    fun_prop
  have harg : Differentiable ℂ (fun z : ℂ =>
      Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)) := by
    fun_prop
  have hphase : Differentiable ℂ (fun z : ℂ =>
      Complex.exp ((ℓ : ℂ) *
        mellinShellPhase ε
          (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)))) :=
    Complex.differentiable_exp.comp
      (((mellinShellPhase_differentiable hε horder).comp
        harg).const_mul (ℓ : ℂ))
  exact hpi.mul hphase
theorem plusSaddleRegularMellinFactor_differentiable {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (ℓ : ℝ) :
    Differentiable ℂ (plusSaddleRegularMellinFactor ε ℓ) := by
  have hp : Differentiable ℂ (fun z : ℂ =>
      plusPolynomial ε
        (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))) := by
    unfold plusPolynomial
    fun_prop
  exact (saddleRegularMellinFactor_differentiable
    hε horder ℓ).mul hp
theorem minusSaddleRegularMellinFactor_differentiable {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (ℓ : ℝ) :
    Differentiable ℂ (minusSaddleRegularMellinFactor ε ℓ) := by
  have hp : Differentiable ℂ (fun z : ℂ =>
      minusPolynomial ε
        (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))) := by
    unfold minusPolynomial
    fun_prop
  exact (saddleRegularMellinFactor_differentiable
    hε horder ℓ).mul hp
theorem plusSaddleRegularMellinFactor_analyticOnNhd {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (ℓ : ℝ) :
    AnalyticOnNhd ℂ (plusSaddleRegularMellinFactor ε ℓ) Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (plusSaddleRegularMellinFactor_differentiable hε horder ℓ)
theorem minusSaddleRegularMellinFactor_analyticOnNhd {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (ℓ : ℝ) :
    AnalyticOnNhd ℂ (minusSaddleRegularMellinFactor ε ℓ) Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (minusSaddleRegularMellinFactor_differentiable hε horder ℓ)
theorem saddleMellinGamma_meromorphic :
    Meromorphic (fun z : ℂ => Complex.Gamma (z / 2)) := by
  intro z
  have hg : MeromorphicAt Complex.Gamma (z / 2) :=
    Meromorphic.Gamma (z / 2)
  have ha : AnalyticAt ℂ (fun u : ℂ => u / 2) z := by
    fun_prop
  simpa [Function.comp_def] using!
    (MeromorphicAt.comp_analyticAt
      (g := fun u : ℂ => u / 2) (x := z) hg ha)
theorem plusSaddleMellinData_meromorphic {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (ℓ : ℝ) :
    Meromorphic (plusSaddleMellinData ε ℓ) := by
  have hregular : Meromorphic (plusSaddleRegularMellinFactor ε ℓ) :=
    meromorphicOn_univ.mp
      (plusSaddleRegularMellinFactor_analyticOnNhd
        hε horder ℓ).meromorphicOn
  have hproduct := saddleMellinGamma_meromorphic.mul hregular
  intro z
  rw [show plusSaddleMellinData ε ℓ =
      (fun w : ℂ => Complex.Gamma (w / 2) *
        plusSaddleRegularMellinFactor ε ℓ w) by
    funext w
    exact plusSaddleMellinData_eq_gamma_mul_regular ε ℓ w]
  exact hproduct z
theorem minusSaddleMellinData_meromorphic {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (ℓ : ℝ) :
    Meromorphic (minusSaddleMellinData ε ℓ) := by
  have hregular : Meromorphic (minusSaddleRegularMellinFactor ε ℓ) :=
    meromorphicOn_univ.mp
      (minusSaddleRegularMellinFactor_analyticOnNhd
        hε horder ℓ).meromorphicOn
  have hproduct := saddleMellinGamma_meromorphic.mul hregular
  intro z
  rw [show minusSaddleMellinData ε ℓ =
      (fun w : ℂ => Complex.Gamma (w / 2) *
        minusSaddleRegularMellinFactor ε ℓ w) by
    funext w
    exact minusSaddleMellinData_eq_gamma_mul_regular ε ℓ w]
  exact hproduct z
theorem saddleMellinGamma_differentiableAt_of_re_pos
    {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) z := by
  have hhalf : 0 < (z / 2).re := by
    simpa using! half_pos hz
  have hg : DifferentiableAt ℂ Complex.Gamma (z / 2) :=
    Complex.differentiableAt_Gamma (z / 2) (by
      intro n hn
      have hnonpositive : (-(n : ℂ)).re ≤ 0 := by simp
      exact (not_lt_of_ge hnonpositive) (hn ▸ hhalf))
  exact hg.comp z (by fun_prop)
theorem saddleMellinGamma_differentiableOn_rightHalfPlane :
    DifferentiableOn ℂ
      (fun z : ℂ => Complex.Gamma (z / 2))
      {z : ℂ | 0 < z.re} := by
  intro z hz
  exact (saddleMellinGamma_differentiableAt_of_re_pos
    hz).differentiableWithinAt
theorem plusSaddleMellinData_differentiableOn_rightHalfPlane
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (ℓ : ℝ) :
    DifferentiableOn ℂ (plusSaddleMellinData ε ℓ)
      {z : ℂ | 0 < z.re} := by
  rw [show plusSaddleMellinData ε ℓ =
      (fun z : ℂ => Complex.Gamma (z / 2) *
        plusSaddleRegularMellinFactor ε ℓ z) by
    funext z
    exact plusSaddleMellinData_eq_gamma_mul_regular ε ℓ z]
  exact saddleMellinGamma_differentiableOn_rightHalfPlane.mul
    (plusSaddleRegularMellinFactor_differentiable
      hε horder ℓ).differentiableOn
theorem minusSaddleMellinData_differentiableOn_rightHalfPlane
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (ℓ : ℝ) :
    DifferentiableOn ℂ (minusSaddleMellinData ε ℓ)
      {z : ℂ | 0 < z.re} := by
  rw [show minusSaddleMellinData ε ℓ =
      (fun z : ℂ => Complex.Gamma (z / 2) *
        minusSaddleRegularMellinFactor ε ℓ z) by
    funext z
    exact minusSaddleMellinData_eq_gamma_mul_regular ε ℓ z]
  exact saddleMellinGamma_differentiableOn_rightHalfPlane.mul
    (minusSaddleRegularMellinFactor_differentiable
      hε horder ℓ).differentiableOn
theorem saddleMellinShellArgument_zero {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    Complex.I * ((0 : ℂ) - (ℓ : ℂ)) / (ℓ : ℂ) =
      -Complex.I := by
  have hc : (ℓ : ℂ) ≠ 0 := by
    exact_mod_cast hℓ.ne'
  field_simp [hc]; ring
theorem mellinShellPhase_neg_I (ε : ℝ) :
    mellinShellPhase ε (-Complex.I) =
      (realHyperbolicShellPhase ε 1 : ℂ) := by
  calc
    mellinShellPhase ε (-Complex.I) =
        mellinShellPhase ε Complex.I :=
          mellinShellPhase_neg ε Complex.I
    _ = (realHyperbolicShellPhase ε 1 : ℂ) := by
          simpa using! mellinShellPhase_imaginary ε 1
theorem plusPolynomial_neg_I (ε : ℝ) :
    plusPolynomial ε (-Complex.I) = (beta ε : ℂ) := by
  simpa using! plusPolynomial_imaginary ε (-1)
theorem minusPolynomial_neg_I (ε : ℝ) :
    minusPolynomial ε (-Complex.I) = (beta ε : ℂ) := by
  simpa using! minusPolynomial_imaginary ε (-1)
theorem saddleRegularMellinFactor_zero
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    saddleRegularMellinFactor ε ℓ 0 =
      ((Real.pi ^ (ℓ / 2) *
        Real.exp (ℓ * realHyperbolicShellPhase ε 1) : ℝ) : ℂ) := by
  have hpi :
      Complex.exp
        (((ℓ : ℂ) - (0 : ℂ)) *
          (Real.log Real.pi : ℂ) / 2) =
        ((Real.pi ^ (ℓ / 2) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos Real.pi_pos, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hphase :
      Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε (-Complex.I)) =
        (Real.exp
          (ℓ * realHyperbolicShellPhase ε 1) : ℂ) := by
    rw [mellinShellPhase_neg_I,
      ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  unfold saddleRegularMellinFactor
  rw [saddleMellinShellArgument_zero hℓ, hpi, hphase,
    ← Complex.ofReal_mul]
theorem two_mul_plusSaddleRegularMellinFactor_zero
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    (2 : ℂ) * plusSaddleRegularMellinFactor ε ℓ 0 =
      (saddleOriginValue ε ℓ : ℂ) := by
  unfold plusSaddleRegularMellinFactor saddleOriginValue
  rw [saddleRegularMellinFactor_zero hℓ,
    saddleMellinShellArgument_zero hℓ,
    plusPolynomial_neg_I]
  push_cast
  ring
theorem two_mul_minusSaddleRegularMellinFactor_zero
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    (2 : ℂ) * minusSaddleRegularMellinFactor ε ℓ 0 =
      (saddleOriginValue ε ℓ : ℂ) := by
  unfold minusSaddleRegularMellinFactor saddleOriginValue
  rw [saddleRegularMellinFactor_zero hℓ,
    saddleMellinShellArgument_zero hℓ,
    minusPolynomial_neg_I]
  push_cast
  ring
theorem complexGamma_residue_neg_nat (n : ℕ) :
    Tendsto (fun z : ℂ => (z + (n : ℂ)) * Complex.Gamma z)
      (𝓝[≠] (-(n : ℂ)))
      (𝓝 (((-1 : ℂ) ^ n) / (n.factorial : ℂ))) := by
  induction n with
  | zero =>
      simpa using! Complex.tendsto_self_mul_Gamma_nhds_zero
  | succ n ih =>
      have hshift : Tendsto (fun z : ℂ => z + 1)
          (𝓝[≠] (-((n + 1 : ℕ) : ℂ)))
          (𝓝[≠] (-(n : ℂ))) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · convert! ((tendsto_id.add_const (1 : ℂ)).mono_left
            nhdsWithin_le_nhds) using 1; simp [Nat.cast_add, Nat.cast_one]
        · filter_upwards [self_mem_nhdsWithin] with z hz
          simp only [Set.mem_compl_iff,
            Set.mem_singleton_iff] at hz ⊢
          intro heq
          apply hz
          simp only [Nat.cast_add, Nat.cast_one]
          linear_combination heq
      have hnonzero : (-((n + 1 : ℕ) : ℂ)) ≠ 0 := by
        exact neg_ne_zero.mpr (by
          exact_mod_cast Nat.succ_ne_zero n)
      have hden : Tendsto (fun z : ℂ => z)
          (𝓝[≠] (-((n + 1 : ℕ) : ℂ)))
          (𝓝 (-((n + 1 : ℕ) : ℂ))) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hquot := (ih.comp hshift).div hden hnonzero
      have hne : ∀ᶠ z in (𝓝[≠] (-((n + 1 : ℕ) : ℂ))),
          z ≠ (0 : ℂ) :=
        ((continuousAt_id :
          ContinuousAt (fun z : ℂ => z)
            (-((n + 1 : ℕ) : ℂ))).eventually_ne
              hnonzero).filter_mono nhdsWithin_le_nhds
      have htarget :
          (((-1 : ℂ) ^ n / (n.factorial : ℂ)) /
            (-((n + 1 : ℕ) : ℂ))) =
              ((-1 : ℂ) ^ (n + 1)) /
                ((n + 1).factorial : ℂ) := by
        have hn : ((n : ℂ) + 1) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        have hf : (n.factorial : ℂ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero n
        rw [Nat.factorial_succ, Nat.cast_mul,
          Nat.cast_succ, pow_succ]
        field_simp [hn, hf]
      rw [← htarget]
      refine hquot.congr' ?_
      filter_upwards [hne] with z hz
      change
        ((z + 1 + (n : ℂ)) * Complex.Gamma (z + 1)) / z =
          (z + ((n + 1 : ℕ) : ℂ)) * Complex.Gamma z
      rw [Complex.Gamma_add_one z hz]
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp [hz]; ring
theorem saddleGamma_residue_neg_even (n : ℕ) :
    Tendsto
      (fun z : ℂ =>
        (z + ((2 * n : ℕ) : ℂ)) * Complex.Gamma (z / 2))
      (𝓝[≠] (-((2 * n : ℕ) : ℂ)))
      (𝓝 ((2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ))) := by
  have hscale : Tendsto (fun z : ℂ => z / 2)
      (𝓝[≠] (-((2 * n : ℕ) : ℂ)))
      (𝓝[≠] (-(n : ℂ))) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · convert! ((tendsto_id.div_const (2 : ℂ)).mono_left
        nhdsWithin_le_nhds) using 1; simp [Nat.cast_mul]; ring
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Set.mem_compl_iff,
        Set.mem_singleton_iff] at hz ⊢
      intro heq
      apply hz
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      linear_combination 2 * heq
  have hresidue :=
    ((complexGamma_residue_neg_nat n).comp hscale).const_mul
      (2 : ℂ)
  convert! hresidue using 1
  · funext z
    change
      (z + ((2 * n : ℕ) : ℂ)) * Complex.Gamma (z / 2) =
        2 * ((z / 2 + (n : ℂ)) * Complex.Gamma (z / 2))
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  · ring_nf
theorem gamma_add_nat_eq_product_of_lt (z : ℂ) (k : ℕ)
    (hz : ∀ j : ℕ, j < k → z + (j : ℂ) ≠ 0) :
    Complex.Gamma (z + (k : ℂ)) =
      Complex.Gamma z *
        ∏ j ∈ Finset.range k, (z + (j : ℂ)) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
      have hprevious : ∀ j : ℕ, j < k → z + (j : ℂ) ≠ 0 := by
        intro j hj
        exact hz j (Nat.lt_succ_of_lt hj)
      have hlast : z + (k : ℂ) ≠ 0 :=
        hz k (Nat.lt_succ_self k)
      rw [Nat.cast_succ, ← add_assoc,
        Complex.Gamma_add_one (z + (k : ℂ)) hlast,
        ih z hprevious, Finset.prod_range_succ]
      ring
def saddlePoleStrip (n : ℕ) : Set ℂ :=
  {z : ℂ |
    -(2 * ((n : ℝ) + 1)) < z.re ∧
      z.re < -(2 * (n : ℝ)) + 1}
theorem saddlePole_mem_strip (n : ℕ) :
    (-((2 * n : ℕ) : ℂ)) ∈ saddlePoleStrip n := by
  change
    -(2 * ((n : ℝ) + 1)) <
        (-((2 * n : ℕ) : ℂ)).re ∧
      (-((2 * n : ℕ) : ℂ)).re <
        -(2 * (n : ℝ)) + 1
  constructor <;>
    norm_num [Nat.cast_mul, Complex.mul_re]
theorem isOpen_saddlePoleStrip (n : ℕ) :
    IsOpen (saddlePoleStrip n) := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
def saddlePoleLowerProduct (n : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.range n, (z / 2 + (j : ℂ))
theorem saddlePoleLowerProduct_ne_zero
    {n : ℕ} {z : ℂ} (hz : z ∈ saddlePoleStrip n) :
    saddlePoleLowerProduct n z ≠ 0 := by
  unfold saddlePoleLowerProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  have hjreal : (j : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hjn
  intro hzero
  have hre := congrArg Complex.re hzero
  norm_num at hre
  change
    -(2 * ((n : ℝ) + 1)) < z.re ∧
      z.re < -(2 * (n : ℝ)) + 1 at hz
  linarith
def saddleNthGammaPoleNumerator (n : ℕ) (z : ℂ) : ℂ :=
  (2 : ℂ) *
    Complex.Gamma (z / 2 + ((n + 1 : ℕ) : ℂ)) /
      saddlePoleLowerProduct n z
theorem saddlePoleLowerProduct_differentiable (n : ℕ) :
    Differentiable ℂ (saddlePoleLowerProduct n) := by
  unfold saddlePoleLowerProduct
  fun_prop
theorem saddleGamma_eq_nthPoleNumerator_div
    {n : ℕ} {z : ℂ}
    (hstrip : z ∈ saddlePoleStrip n)
    (hpole : z ≠ (-((2 * n : ℕ) : ℂ))) :
    Complex.Gamma (z / 2) =
      saddleNthGammaPoleNumerator n z /
        (z + ((2 * n : ℕ) : ℂ)) := by
  have hden : saddlePoleLowerProduct n z ≠ 0 :=
    saddlePoleLowerProduct_ne_zero hstrip
  have hterms :
      ∀ j : ℕ, j < n → z / 2 + (j : ℂ) ≠ 0 := by
    have hproduct :
        (∏ j ∈ Finset.range n,
          (z / 2 + (j : ℂ))) ≠ 0 := by
      simpa [saddlePoleLowerProduct] using! hden
    intro j hj
    exact (Finset.prod_ne_zero_iff.mp hproduct)
      j (Finset.mem_range.mpr hj)
  have hfinite :
      ∀ j : ℕ, j < n + 1 →
        z / 2 + (j : ℂ) ≠ 0 := by
    intro j hj
    by_cases heq : j = n
    · subst j
      intro hzero
      apply hpole
      push_cast at hzero ⊢
      linear_combination 2 * hzero
    · exact hterms j (by omega)
  have hrec :=
    gamma_add_nat_eq_product_of_lt (z / 2)
      (n + 1) hfinite
  rw [Finset.prod_range_succ] at hrec
  have hcoordinate :
      z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
    intro hzero
    apply hpole
    push_cast at hzero ⊢
    linear_combination hzero
  unfold saddleNthGammaPoleNumerator
  rw [hrec]
  change Complex.Gamma (z / 2) =
    2 *
      (Complex.Gamma (z / 2) *
        ((∏ j ∈ Finset.range n,
          (z / 2 + (j : ℂ))) *
          (z / 2 + (n : ℂ)))) /
      saddlePoleLowerProduct n z /
        (z + ((2 * n : ℕ) : ℂ))
  rw [show saddlePoleLowerProduct n z =
      ∏ j ∈ Finset.range n, (z / 2 + (j : ℂ)) by rfl]
  have hproduct :
      (∏ j ∈ Finset.range n,
        (z / 2 + (j : ℂ))) ≠ 0 := by
    simpa [saddlePoleLowerProduct] using! hden
  have hcancel :
      2 *
        (Complex.Gamma (z / 2) *
          ((∏ j ∈ Finset.range n,
            (z / 2 + (j : ℂ))) *
            (z / 2 + (n : ℂ)))) /
          (∏ j ∈ Finset.range n,
            (z / 2 + (j : ℂ))) =
        2 * Complex.Gamma (z / 2) *
          (z / 2 + (n : ℂ)) := by
    calc
      _ =
          (2 * Complex.Gamma (z / 2) *
            (z / 2 + (n : ℂ))) *
              (∏ j ∈ Finset.range n,
                (z / 2 + (j : ℂ))) /
              (∏ j ∈ Finset.range n,
                (z / 2 + (j : ℂ))) := by
            congr 1
            ring
      _ = _ := mul_div_cancel_right₀ _ hproduct
  rw [hcancel]
  field_simp [hcoordinate]; push_cast; ring
theorem saddleNthGammaPoleNumerator_differentiableOn (n : ℕ) :
    DifferentiableOn ℂ (saddleNthGammaPoleNumerator n)
      (saddlePoleStrip n) := by
  intro z hz
  have hpositive :
      0 < (z / 2 + ((n + 1 : ℕ) : ℂ)).re := by
    norm_num [Nat.cast_add]
    change
      -(2 * ((n : ℝ) + 1)) < z.re ∧
        z.re < -(2 * (n : ℝ)) + 1 at hz
    linarith [hz.1]
  have hgamma :
      DifferentiableAt ℂ Complex.Gamma
        (z / 2 + ((n + 1 : ℕ) : ℂ)) :=
    Complex.differentiableAt_Gamma _ (by
      intro m hm
      have hnonpositive : (-(m : ℂ)).re ≤ 0 := by simp
      exact (not_lt_of_ge hnonpositive) (hm ▸ hpositive))
  have hcompose :
      DifferentiableAt ℂ
        (fun w : ℂ =>
          Complex.Gamma
            (w / 2 + ((n + 1 : ℕ) : ℂ))) z :=
    hgamma.comp z (by fun_prop)
  have hnumerator := hcompose.const_mul (2 : ℂ)
  have hdenominator := saddlePoleLowerProduct_differentiable n z
  exact (hnumerator.div hdenominator
    (saddlePoleLowerProduct_ne_zero hz)).differentiableWithinAt
theorem saddleNthGammaPoleNumerator_at_pole (n : ℕ) :
    saddleNthGammaPoleNumerator n
        (-((2 * n : ℕ) : ℂ)) =
      (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) := by
  have hpole :
      (-((2 * n : ℕ) : ℂ)) ∈ saddlePoleStrip n :=
    saddlePole_mem_strip n
  have hanalytic :
      DifferentiableAt ℂ (saddleNthGammaPoleNumerator n)
        (-((2 * n : ℕ) : ℂ)) :=
    (saddleNthGammaPoleNumerator_differentiableOn n).differentiableAt
      ((isOpen_saddlePoleStrip n).mem_nhds hpole)
  have hcontinuous :
      Tendsto (saddleNthGammaPoleNumerator n)
        (𝓝[≠] (-((2 * n : ℕ) : ℂ)))
        (𝓝 (saddleNthGammaPoleNumerator n
          (-((2 * n : ℕ) : ℂ)))) :=
    hanalytic.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hstrip :
      ∀ᶠ z in (𝓝[≠] (-((2 * n : ℕ) : ℂ))),
        z ∈ saddlePoleStrip n :=
    nhdsWithin_le_nhds
      ((isOpen_saddlePoleStrip n).mem_nhds hpole)
  have heventual :
      (fun z : ℂ =>
        (z + ((2 * n : ℕ) : ℂ)) *
          Complex.Gamma (z / 2)) =ᶠ[𝓝[≠]
            (-((2 * n : ℕ) : ℂ))]
          saddleNthGammaPoleNumerator n := by
    filter_upwards [hstrip, self_mem_nhdsWithin]
      with z hz hne
    simp only [Set.mem_compl_iff,
      Set.mem_singleton_iff] at hne
    rw [saddleGamma_eq_nthPoleNumerator_div hz hne]
    have hcoordinate :
        z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
      intro hzero
      apply hne
      linear_combination hzero
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ hcoordinate
  exact (tendsto_nhds_unique_of_eventuallyEq
    (saddleGamma_residue_neg_even n)
    hcontinuous heventual).symm
def plusSaddleNthPoleNumerator
    (ε ℓ : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  saddleNthGammaPoleNumerator n z *
    plusSaddleRegularMellinFactor ε ℓ z
def minusSaddleNthPoleNumerator
    (ε ℓ : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  saddleNthGammaPoleNumerator n z *
    minusSaddleRegularMellinFactor ε ℓ z
theorem plusSaddleNthPoleNumerator_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (n : ℕ) :
    DifferentiableOn ℂ (plusSaddleNthPoleNumerator ε ℓ n)
      (saddlePoleStrip n) := by
  unfold plusSaddleNthPoleNumerator
  exact (saddleNthGammaPoleNumerator_differentiableOn n).mul
    (plusSaddleRegularMellinFactor_differentiable
      hε horder ℓ).differentiableOn
theorem minusSaddleNthPoleNumerator_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (n : ℕ) :
    DifferentiableOn ℂ (minusSaddleNthPoleNumerator ε ℓ n)
      (saddlePoleStrip n) := by
  unfold minusSaddleNthPoleNumerator
  exact (saddleNthGammaPoleNumerator_differentiableOn n).mul
    (minusSaddleRegularMellinFactor_differentiable
      hε horder ℓ).differentiableOn
theorem plusSaddleMellinData_eq_nthPoleNumerator_div
    (ε ℓ : ℝ) {n : ℕ} {z : ℂ}
    (hstrip : z ∈ saddlePoleStrip n)
    (hpole : z ≠ (-((2 * n : ℕ) : ℂ))) :
    plusSaddleMellinData ε ℓ z =
      plusSaddleNthPoleNumerator ε ℓ n z /
        (z + ((2 * n : ℕ) : ℂ)) := by
  rw [plusSaddleMellinData_eq_gamma_mul_regular,
    saddleGamma_eq_nthPoleNumerator_div hstrip hpole]
  unfold plusSaddleNthPoleNumerator
  ring
theorem minusSaddleMellinData_eq_nthPoleNumerator_div
    (ε ℓ : ℝ) {n : ℕ} {z : ℂ}
    (hstrip : z ∈ saddlePoleStrip n)
    (hpole : z ≠ (-((2 * n : ℕ) : ℂ))) :
    minusSaddleMellinData ε ℓ z =
      minusSaddleNthPoleNumerator ε ℓ n z /
        (z + ((2 * n : ℕ) : ℂ)) := by
  rw [minusSaddleMellinData_eq_gamma_mul_regular,
    saddleGamma_eq_nthPoleNumerator_div hstrip hpole]
  unfold minusSaddleNthPoleNumerator
  ring
theorem plusSaddleNthPoleNumerator_at_pole
    (ε ℓ : ℝ) (n : ℕ) :
    plusSaddleNthPoleNumerator ε ℓ n
        (-((2 * n : ℕ) : ℂ)) =
      (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) *
        plusSaddleRegularMellinFactor ε ℓ
          (-((2 * n : ℕ) : ℂ)) := by
  unfold plusSaddleNthPoleNumerator
  rw [saddleNthGammaPoleNumerator_at_pole]
theorem minusSaddleNthPoleNumerator_at_pole
    (ε ℓ : ℝ) (n : ℕ) :
    minusSaddleNthPoleNumerator ε ℓ n
        (-((2 * n : ℕ) : ℂ)) =
      (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) *
        minusSaddleRegularMellinFactor ε ℓ
          (-((2 * n : ℕ) : ℂ)) := by
  unfold minusSaddleNthPoleNumerator
  rw [saddleNthGammaPoleNumerator_at_pole]
def plusSaddlePoleResidue (ε ℓ : ℝ) (n : ℕ) : ℂ :=
  (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) *
    plusSaddleRegularMellinFactor ε ℓ
      (-((2 * n : ℕ) : ℂ))
def minusSaddlePoleResidue (ε ℓ : ℝ) (n : ℕ) : ℂ :=
  (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) *
    minusSaddleRegularMellinFactor ε ℓ
      (-((2 * n : ℕ) : ℂ))
theorem plusSaddleNthPoleNumerator_poleResidue
    (ε ℓ : ℝ) (n : ℕ) :
    plusSaddleNthPoleNumerator ε ℓ n
        (-((2 * n : ℕ) : ℂ)) =
      plusSaddlePoleResidue ε ℓ n := by
  exact plusSaddleNthPoleNumerator_at_pole ε ℓ n
theorem minusSaddleNthPoleNumerator_poleResidue
    (ε ℓ : ℝ) (n : ℕ) :
    minusSaddleNthPoleNumerator ε ℓ n
        (-((2 * n : ℕ) : ℂ)) =
      minusSaddlePoleResidue ε ℓ n := by
  exact minusSaddleNthPoleNumerator_at_pole ε ℓ n
def plusSaddleNthPoleRegularPart
    (ε ℓ : ℝ) (n : ℕ) : ℂ → ℂ :=
  dslope (plusSaddleNthPoleNumerator ε ℓ n)
    (-((2 * n : ℕ) : ℂ))
def minusSaddleNthPoleRegularPart
    (ε ℓ : ℝ) (n : ℕ) : ℂ → ℂ :=
  dslope (minusSaddleNthPoleNumerator ε ℓ n)
    (-((2 * n : ℕ) : ℂ))
theorem plusSaddleNthPoleRegularPart_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (n : ℕ) :
    DifferentiableOn ℂ (plusSaddleNthPoleRegularPart ε ℓ n)
      (saddlePoleStrip n) := by
  unfold plusSaddleNthPoleRegularPart
  exact (Complex.differentiableOn_dslope
    ((isOpen_saddlePoleStrip n).mem_nhds
      (saddlePole_mem_strip n))).mpr
        (plusSaddleNthPoleNumerator_differentiableOn
          hε horder ℓ n)
theorem minusSaddleNthPoleRegularPart_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (n : ℕ) :
    DifferentiableOn ℂ (minusSaddleNthPoleRegularPart ε ℓ n)
      (saddlePoleStrip n) := by
  unfold minusSaddleNthPoleRegularPart
  exact (Complex.differentiableOn_dslope
    ((isOpen_saddlePoleStrip n).mem_nhds
      (saddlePole_mem_strip n))).mpr
        (minusSaddleNthPoleNumerator_differentiableOn
          hε horder ℓ n)
theorem plusSaddleMellinData_nthPole_decomposition
    (ε ℓ : ℝ) {n : ℕ} {z : ℂ}
    (hstrip : z ∈ saddlePoleStrip n)
    (hpole : z ≠ (-((2 * n : ℕ) : ℂ))) :
    plusSaddleMellinData ε ℓ z =
      plusSaddlePoleResidue ε ℓ n /
          (z + ((2 * n : ℕ) : ℂ)) +
        plusSaddleNthPoleRegularPart ε ℓ n z := by
  have hslope :
      (z + ((2 * n : ℕ) : ℂ)) *
          plusSaddleNthPoleRegularPart ε ℓ n z =
        plusSaddleNthPoleNumerator ε ℓ n z -
          plusSaddlePoleResidue ε ℓ n := by
    have hbase := sub_smul_dslope
      (plusSaddleNthPoleNumerator ε ℓ n)
        (-((2 * n : ℕ) : ℂ)) z
    rw [plusSaddleNthPoleNumerator_poleResidue
      ε ℓ n] at hbase
    simpa only [plusSaddleNthPoleRegularPart,
      sub_neg_eq_add, smul_eq_mul] using! hbase
  have hnumerator :
      plusSaddleNthPoleNumerator ε ℓ n z =
        plusSaddlePoleResidue ε ℓ n +
          (z + ((2 * n : ℕ) : ℂ)) *
            plusSaddleNthPoleRegularPart ε ℓ n z := by
    rw [hslope]
    ring
  rw [plusSaddleMellinData_eq_nthPoleNumerator_div
    ε ℓ hstrip hpole, hnumerator]
  have hcoordinate :
      z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
    intro hzero
    apply hpole
    linear_combination hzero
  field_simp [hcoordinate]
theorem minusSaddleMellinData_nthPole_decomposition
    (ε ℓ : ℝ) {n : ℕ} {z : ℂ}
    (hstrip : z ∈ saddlePoleStrip n)
    (hpole : z ≠ (-((2 * n : ℕ) : ℂ))) :
    minusSaddleMellinData ε ℓ z =
      minusSaddlePoleResidue ε ℓ n /
          (z + ((2 * n : ℕ) : ℂ)) +
        minusSaddleNthPoleRegularPart ε ℓ n z := by
  have hslope :
      (z + ((2 * n : ℕ) : ℂ)) *
          minusSaddleNthPoleRegularPart ε ℓ n z =
        minusSaddleNthPoleNumerator ε ℓ n z -
          minusSaddlePoleResidue ε ℓ n := by
    have hbase := sub_smul_dslope
      (minusSaddleNthPoleNumerator ε ℓ n)
        (-((2 * n : ℕ) : ℂ)) z
    rw [minusSaddleNthPoleNumerator_poleResidue
      ε ℓ n] at hbase
    simpa only [minusSaddleNthPoleRegularPart,
      sub_neg_eq_add, smul_eq_mul] using! hbase
  have hnumerator :
      minusSaddleNthPoleNumerator ε ℓ n z =
        minusSaddlePoleResidue ε ℓ n +
          (z + ((2 * n : ℕ) : ℂ)) *
            minusSaddleNthPoleRegularPart ε ℓ n z := by
    rw [hslope]
    ring
  rw [minusSaddleMellinData_eq_nthPoleNumerator_div
    ε ℓ hstrip hpole, hnumerator]
  have hcoordinate :
      z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
    intro hzero
    apply hpole
    linear_combination hzero
  field_simp [hcoordinate]
def saddleFinitePoleHalfPlane (N : ℕ) : Set ℂ :=
  {z : ℂ | -(2 * ((N : ℝ) + 1)) < z.re}
theorem saddlePole_mem_finiteHalfPlane_iff
    (N n : ℕ) :
    (-((2 * n : ℕ) : ℂ)) ∈
        saddleFinitePoleHalfPlane N ↔ n ≤ N := by
  change
    -(2 * ((N : ℝ) + 1)) <
      (-((2 * n : ℕ) : ℂ)).re ↔ n ≤ N
  norm_num [Nat.cast_mul, Complex.mul_re]
  constructor
  · intro hreal
    have hstrict : (n : ℝ) < (N : ℝ) + 1 := by
      linarith
    have hn : n < N + 1 := by
      exact_mod_cast hstrict
    omega
  · intro hn
    have hreal : (n : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hn
    linarith
theorem saddleMellinGamma_differentiableAt_of_not_pole
    {z : ℂ}
    (hz : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    DifferentiableAt ℂ
      (fun w : ℂ => Complex.Gamma (w / 2)) z := by
  have hhalf : ∀ n : ℕ, z / 2 ≠ -(n : ℂ) := by
    intro n hzero
    apply hz n
    push_cast at hzero ⊢
    linear_combination 2 * hzero
  exact (Complex.differentiableAt_Gamma (z / 2)
    hhalf).comp z (by fun_prop)
theorem plusSaddleMellinData_differentiableAt_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) {z : ℂ}
    (hz : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    DifferentiableAt ℂ (plusSaddleMellinData ε ℓ) z := by
  rw [show plusSaddleMellinData ε ℓ =
      (fun w : ℂ => Complex.Gamma (w / 2) *
        plusSaddleRegularMellinFactor ε ℓ w) by
    funext w
    exact plusSaddleMellinData_eq_gamma_mul_regular ε ℓ w]
  exact (saddleMellinGamma_differentiableAt_of_not_pole hz).mul
    (plusSaddleRegularMellinFactor_differentiable
      hε horder ℓ z)
theorem minusSaddleMellinData_differentiableAt_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) {z : ℂ}
    (hz : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    DifferentiableAt ℂ (minusSaddleMellinData ε ℓ) z := by
  rw [show minusSaddleMellinData ε ℓ =
      (fun w : ℂ => Complex.Gamma (w / 2) *
        minusSaddleRegularMellinFactor ε ℓ w) by
    funext w
    exact minusSaddleMellinData_eq_gamma_mul_regular ε ℓ w]
  exact (saddleMellinGamma_differentiableAt_of_not_pole hz).mul
    (minusSaddleRegularMellinFactor_differentiable
      hε horder ℓ z)
def plusSaddleFinitePoleSubtraction
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  plusSaddleMellinData ε ℓ z -
    ∑ n ∈ Finset.range (N + 1),
      plusSaddlePoleResidue ε ℓ n /
        (z + ((2 * n : ℕ) : ℂ))
def minusSaddleFinitePoleSubtraction
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  minusSaddleMellinData ε ℓ z -
    ∑ n ∈ Finset.range (N + 1),
      minusSaddlePoleResidue ε ℓ n /
        (z + ((2 * n : ℕ) : ℂ))
theorem plusSaddleFinitePoleSubtraction_meromorphic
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) :
    Meromorphic (plusSaddleFinitePoleSubtraction ε ℓ N) := by
  have hsum : Meromorphic
      (fun z : ℂ =>
        ∑ n ∈ Finset.range (N + 1),
          plusSaddlePoleResidue ε ℓ n /
            (z + ((2 * n : ℕ) : ℂ))) := by
    intro z
    exact MeromorphicAt.fun_sum
      (fun n _ => by fun_prop)
  exact (plusSaddleMellinData_meromorphic
    hε horder ℓ).sub hsum
theorem minusSaddleFinitePoleSubtraction_meromorphic
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) :
    Meromorphic (minusSaddleFinitePoleSubtraction ε ℓ N) := by
  have hsum : Meromorphic
      (fun z : ℂ =>
        ∑ n ∈ Finset.range (N + 1),
          minusSaddlePoleResidue ε ℓ n /
            (z + ((2 * n : ℕ) : ℂ))) := by
    intro z
    exact MeromorphicAt.fun_sum
      (fun n _ => by fun_prop)
  exact (minusSaddleMellinData_meromorphic
    hε horder ℓ).sub hsum
def plusSaddleFinitePoleRegularPart
    (ε ℓ : ℝ) (N : ℕ) : ℂ → ℂ :=
  toMeromorphicNFOn
    (plusSaddleFinitePoleSubtraction ε ℓ N)
      (saddleFinitePoleHalfPlane N)
def minusSaddleFinitePoleRegularPart
    (ε ℓ : ℝ) (N : ℕ) : ℂ → ℂ :=
  toMeromorphicNFOn
    (minusSaddleFinitePoleSubtraction ε ℓ N)
      (saddleFinitePoleHalfPlane N)
theorem plusSaddleFinitePoleRegularPart_meromorphicNFOn
    (ε ℓ : ℝ) (N : ℕ) :
    MeromorphicNFOn
      (plusSaddleFinitePoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) := by
  unfold plusSaddleFinitePoleRegularPart
  exact meromorphicNFOn_toMeromorphicNFOn _ _
theorem minusSaddleFinitePoleRegularPart_meromorphicNFOn
    (ε ℓ : ℝ) (N : ℕ) :
    MeromorphicNFOn
      (minusSaddleFinitePoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) := by
  unfold minusSaddleFinitePoleRegularPart
  exact meromorphicNFOn_toMeromorphicNFOn _ _
theorem plusSaddleFinitePoleRegularPart_eq_on_punctured
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N) :
    plusSaddleFinitePoleRegularPart ε ℓ N =ᶠ[𝓝[≠] z]
      plusSaddleFinitePoleSubtraction ε ℓ N := by
  unfold plusSaddleFinitePoleRegularPart
  exact (plusSaddleFinitePoleSubtraction_meromorphic
    hε horder ℓ N).meromorphicOn
      |>.toMeromorphicNFOn_eq_self_on_nhdsNE hz
theorem minusSaddleFinitePoleRegularPart_eq_on_punctured
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N) :
    minusSaddleFinitePoleRegularPart ε ℓ N =ᶠ[𝓝[≠] z]
      minusSaddleFinitePoleSubtraction ε ℓ N := by
  unfold minusSaddleFinitePoleRegularPart
  exact (minusSaddleFinitePoleSubtraction_meromorphic
    hε horder ℓ N).meromorphicOn
      |>.toMeromorphicNFOn_eq_self_on_nhdsNE hz
theorem saddlePoleCoordinate_ne_zero_at_other
    {m n : ℕ} (hmn : m ≠ n) :
    -((2 * n : ℕ) : ℂ) +
      ((2 * m : ℕ) : ℂ) ≠ 0 := by
  intro hzero
  apply hmn
  have hreal := congrArg Complex.re hzero
  norm_num [Nat.cast_mul, Complex.mul_re] at hreal
  have heq : (m : ℝ) = (n : ℝ) := by
    linarith
  exact_mod_cast heq
def plusSaddleFinitePoleRemaining
    (ε ℓ : ℝ) (N n : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ (Finset.range (N + 1)).erase n,
    plusSaddlePoleResidue ε ℓ m /
      (z + ((2 * m : ℕ) : ℂ))
def minusSaddleFinitePoleRemaining
    (ε ℓ : ℝ) (N n : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ (Finset.range (N + 1)).erase n,
    minusSaddlePoleResidue ε ℓ m /
      (z + ((2 * m : ℕ) : ℂ))
theorem plusSaddleFinitePoleRemaining_differentiableAt_pole
    (ε ℓ : ℝ) (N n : ℕ) :
    DifferentiableAt ℂ
      (plusSaddleFinitePoleRemaining ε ℓ N n)
      (-((2 * n : ℕ) : ℂ)) := by
  unfold plusSaddleFinitePoleRemaining
  apply DifferentiableAt.fun_sum
  intro m hm
  have hdistinct : m ≠ n :=
    (Finset.mem_erase.mp hm).1
  have hcoordinate :=
    saddlePoleCoordinate_ne_zero_at_other hdistinct
  have hconstant :
      DifferentiableAt ℂ
        (fun _ : ℂ => plusSaddlePoleResidue ε ℓ m)
          (-((2 * n : ℕ) : ℂ)) := by
    fun_prop
  have hdenominator :
      DifferentiableAt ℂ
        (fun z : ℂ => z + ((2 * m : ℕ) : ℂ))
          (-((2 * n : ℕ) : ℂ)) := by
    fun_prop
  exact hconstant.div hdenominator hcoordinate
theorem minusSaddleFinitePoleRemaining_differentiableAt_pole
    (ε ℓ : ℝ) (N n : ℕ) :
    DifferentiableAt ℂ
      (minusSaddleFinitePoleRemaining ε ℓ N n)
      (-((2 * n : ℕ) : ℂ)) := by
  unfold minusSaddleFinitePoleRemaining
  apply DifferentiableAt.fun_sum
  intro m hm
  have hdistinct : m ≠ n :=
    (Finset.mem_erase.mp hm).1
  have hcoordinate :=
    saddlePoleCoordinate_ne_zero_at_other hdistinct
  have hconstant :
      DifferentiableAt ℂ
        (fun _ : ℂ => minusSaddlePoleResidue ε ℓ m)
          (-((2 * n : ℕ) : ℂ)) := by
    fun_prop
  have hdenominator :
      DifferentiableAt ℂ
        (fun z : ℂ => z + ((2 * m : ℕ) : ℂ))
          (-((2 * n : ℕ) : ℂ)) := by
    fun_prop
  exact hconstant.div hdenominator hcoordinate
theorem plusSaddleFinitePoleSubtraction_differentiableAt_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    DifferentiableAt ℂ
      (plusSaddleFinitePoleSubtraction ε ℓ N) z := by
  unfold plusSaddleFinitePoleSubtraction
  apply (plusSaddleMellinData_differentiableAt_of_not_pole
    hε horder ℓ hz).sub
  apply DifferentiableAt.fun_sum
  intro n _
  have hcoordinate :
      z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
    intro hzero
    apply hz n
    linear_combination hzero
  have hconstant :
      DifferentiableAt ℂ
        (fun _ : ℂ => plusSaddlePoleResidue ε ℓ n) z := by
    fun_prop
  have hdenominator :
      DifferentiableAt ℂ
        (fun w : ℂ => w + ((2 * n : ℕ) : ℂ)) z := by
    fun_prop
  exact hconstant.div hdenominator hcoordinate
theorem minusSaddleFinitePoleSubtraction_differentiableAt_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    DifferentiableAt ℂ
      (minusSaddleFinitePoleSubtraction ε ℓ N) z := by
  unfold minusSaddleFinitePoleSubtraction
  apply (minusSaddleMellinData_differentiableAt_of_not_pole
    hε horder ℓ hz).sub
  apply DifferentiableAt.fun_sum
  intro n _
  have hcoordinate :
      z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
    intro hzero
    apply hz n
    linear_combination hzero
  have hconstant :
      DifferentiableAt ℂ
        (fun _ : ℂ => minusSaddlePoleResidue ε ℓ n) z := by
    fun_prop
  have hdenominator :
      DifferentiableAt ℂ
        (fun w : ℂ => w + ((2 * n : ℕ) : ℂ)) z := by
    fun_prop
  exact hconstant.div hdenominator hcoordinate
theorem plusSaddleFinitePoleSubtraction_eventually_eq_poleRegular
    (ε ℓ : ℝ) (N n : ℕ) (hn : n ≤ N) :
    plusSaddleFinitePoleSubtraction ε ℓ N =ᶠ[𝓝[≠]
      (-((2 * n : ℕ) : ℂ))]
        (fun z : ℂ =>
          plusSaddleNthPoleRegularPart ε ℓ n z -
            plusSaddleFinitePoleRemaining ε ℓ N n z) := by
  have hmem : n ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (by omega)
  have hstrip :
      ∀ᶠ z in (𝓝[≠] (-((2 * n : ℕ) : ℂ))),
        z ∈ saddlePoleStrip n :=
    nhdsWithin_le_nhds
      ((isOpen_saddlePoleStrip n).mem_nhds
        (saddlePole_mem_strip n))
  filter_upwards [hstrip, self_mem_nhdsWithin]
    with z hz hne
  simp only [Set.mem_compl_iff,
    Set.mem_singleton_iff] at hne
  have hsum :
      (∑ m ∈ (Finset.range (N + 1)).erase n,
        plusSaddlePoleResidue ε ℓ m /
          (z + ((2 * m : ℕ) : ℂ))) +
        plusSaddlePoleResidue ε ℓ n /
          (z + ((2 * n : ℕ) : ℂ)) =
      ∑ m ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ m /
          (z + ((2 * m : ℕ) : ℂ)) :=
    (Finset.range (N + 1)).sum_erase_add
      (fun m : ℕ =>
        plusSaddlePoleResidue ε ℓ m /
          (z + ((2 * m : ℕ) : ℂ))) hmem
  unfold plusSaddleFinitePoleSubtraction
    plusSaddleFinitePoleRemaining
  rw [plusSaddleMellinData_nthPole_decomposition
    ε ℓ hz hne, ← hsum]
  ring
theorem minusSaddleFinitePoleSubtraction_eventually_eq_poleRegular
    (ε ℓ : ℝ) (N n : ℕ) (hn : n ≤ N) :
    minusSaddleFinitePoleSubtraction ε ℓ N =ᶠ[𝓝[≠]
      (-((2 * n : ℕ) : ℂ))]
        (fun z : ℂ =>
          minusSaddleNthPoleRegularPart ε ℓ n z -
            minusSaddleFinitePoleRemaining ε ℓ N n z) := by
  have hmem : n ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (by omega)
  have hstrip :
      ∀ᶠ z in (𝓝[≠] (-((2 * n : ℕ) : ℂ))),
        z ∈ saddlePoleStrip n :=
    nhdsWithin_le_nhds
      ((isOpen_saddlePoleStrip n).mem_nhds
        (saddlePole_mem_strip n))
  filter_upwards [hstrip, self_mem_nhdsWithin]
    with z hz hne
  simp only [Set.mem_compl_iff,
    Set.mem_singleton_iff] at hne
  have hsum :
      (∑ m ∈ (Finset.range (N + 1)).erase n,
        minusSaddlePoleResidue ε ℓ m /
          (z + ((2 * m : ℕ) : ℂ))) +
        minusSaddlePoleResidue ε ℓ n /
          (z + ((2 * n : ℕ) : ℂ)) =
      ∑ m ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ m /
          (z + ((2 * m : ℕ) : ℂ)) :=
    (Finset.range (N + 1)).sum_erase_add
      (fun m : ℕ =>
        minusSaddlePoleResidue ε ℓ m /
          (z + ((2 * m : ℕ) : ℂ))) hmem
  unfold minusSaddleFinitePoleSubtraction
    minusSaddleFinitePoleRemaining
  rw [minusSaddleMellinData_nthPole_decomposition
    ε ℓ hz hne, ← hsum]
  ring
theorem plusSaddleFinitePoleSubtraction_tendsto_at_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N n : ℕ) (hn : n ≤ N) :
    Tendsto (plusSaddleFinitePoleSubtraction ε ℓ N)
      (𝓝[≠] (-((2 * n : ℕ) : ℂ)))
      (𝓝 (plusSaddleNthPoleRegularPart ε ℓ n
          (-((2 * n : ℕ) : ℂ)) -
        plusSaddleFinitePoleRemaining ε ℓ N n
          (-((2 * n : ℕ) : ℂ)))) := by
  have hregular :
      DifferentiableAt ℂ
        (plusSaddleNthPoleRegularPart ε ℓ n)
          (-((2 * n : ℕ) : ℂ)) :=
    (plusSaddleNthPoleRegularPart_differentiableOn
      hε horder ℓ n).differentiableAt
        ((isOpen_saddlePoleStrip n).mem_nhds
          (saddlePole_mem_strip n))
  have hremaining :=
    plusSaddleFinitePoleRemaining_differentiableAt_pole
      ε ℓ N n
  have hlimit :
      Tendsto
        (fun z : ℂ =>
          plusSaddleNthPoleRegularPart ε ℓ n z -
            plusSaddleFinitePoleRemaining ε ℓ N n z)
        (𝓝[≠] (-((2 * n : ℕ) : ℂ)))
        (𝓝 (plusSaddleNthPoleRegularPart ε ℓ n
            (-((2 * n : ℕ) : ℂ)) -
          plusSaddleFinitePoleRemaining ε ℓ N n
            (-((2 * n : ℕ) : ℂ)))) :=
    (hregular.sub hremaining).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  exact hlimit.congr'
    (plusSaddleFinitePoleSubtraction_eventually_eq_poleRegular
      ε ℓ N n hn).symm
theorem minusSaddleFinitePoleSubtraction_tendsto_at_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N n : ℕ) (hn : n ≤ N) :
    Tendsto (minusSaddleFinitePoleSubtraction ε ℓ N)
      (𝓝[≠] (-((2 * n : ℕ) : ℂ)))
      (𝓝 (minusSaddleNthPoleRegularPart ε ℓ n
          (-((2 * n : ℕ) : ℂ)) -
        minusSaddleFinitePoleRemaining ε ℓ N n
          (-((2 * n : ℕ) : ℂ)))) := by
  have hregular :
      DifferentiableAt ℂ
        (minusSaddleNthPoleRegularPart ε ℓ n)
          (-((2 * n : ℕ) : ℂ)) :=
    (minusSaddleNthPoleRegularPart_differentiableOn
      hε horder ℓ n).differentiableAt
        ((isOpen_saddlePoleStrip n).mem_nhds
          (saddlePole_mem_strip n))
  have hremaining :=
    minusSaddleFinitePoleRemaining_differentiableAt_pole
      ε ℓ N n
  have hlimit :
      Tendsto
        (fun z : ℂ =>
          minusSaddleNthPoleRegularPart ε ℓ n z -
            minusSaddleFinitePoleRemaining ε ℓ N n z)
        (𝓝[≠] (-((2 * n : ℕ) : ℂ)))
        (𝓝 (minusSaddleNthPoleRegularPart ε ℓ n
            (-((2 * n : ℕ) : ℂ)) -
          minusSaddleFinitePoleRemaining ε ℓ N n
            (-((2 * n : ℕ) : ℂ)))) :=
    (hregular.sub hremaining).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  exact hlimit.congr'
    (minusSaddleFinitePoleSubtraction_eventually_eq_poleRegular
      ε ℓ N n hn).symm
theorem plusSaddleFinitePoleSubtraction_tendsto_of_mem
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N) :
    ∃ c : ℂ,
      Tendsto (plusSaddleFinitePoleSubtraction ε ℓ N)
        (𝓝[≠] z) (𝓝 c) := by
  by_cases hpole :
      ∃ n : ℕ, z = (-((2 * n : ℕ) : ℂ))
  · obtain ⟨n, hn⟩ := hpole
    subst z
    have hindex : n ≤ N :=
      (saddlePole_mem_finiteHalfPlane_iff N n).mp hz
    exact ⟨plusSaddleNthPoleRegularPart ε ℓ n
        (-((2 * n : ℕ) : ℂ)) -
      plusSaddleFinitePoleRemaining ε ℓ N n
        (-((2 * n : ℕ) : ℂ)),
      plusSaddleFinitePoleSubtraction_tendsto_at_pole
        hε horder ℓ N n hindex⟩
  · have hnot : ∀ n : ℕ,
        z ≠ (-((2 * n : ℕ) : ℂ)) := by
      intro n hn
      exact hpole ⟨n, hn⟩
    refine ⟨plusSaddleFinitePoleSubtraction ε ℓ N z,
      ?_⟩
    exact (plusSaddleFinitePoleSubtraction_differentiableAt_of_not_pole
      hε horder ℓ N hnot).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
theorem minusSaddleFinitePoleSubtraction_tendsto_of_mem
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N) :
    ∃ c : ℂ,
      Tendsto (minusSaddleFinitePoleSubtraction ε ℓ N)
        (𝓝[≠] z) (𝓝 c) := by
  by_cases hpole :
      ∃ n : ℕ, z = (-((2 * n : ℕ) : ℂ))
  · obtain ⟨n, hn⟩ := hpole
    subst z
    have hindex : n ≤ N :=
      (saddlePole_mem_finiteHalfPlane_iff N n).mp hz
    exact ⟨minusSaddleNthPoleRegularPart ε ℓ n
        (-((2 * n : ℕ) : ℂ)) -
      minusSaddleFinitePoleRemaining ε ℓ N n
        (-((2 * n : ℕ) : ℂ)),
      minusSaddleFinitePoleSubtraction_tendsto_at_pole
        hε horder ℓ N n hindex⟩
  · have hnot : ∀ n : ℕ,
        z ≠ (-((2 * n : ℕ) : ℂ)) := by
      intro n hn
      exact hpole ⟨n, hn⟩
    refine ⟨minusSaddleFinitePoleSubtraction ε ℓ N z,
      ?_⟩
    exact (minusSaddleFinitePoleSubtraction_differentiableAt_of_not_pole
      hε horder ℓ N hnot).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
theorem plusSaddleFinitePoleRegularPart_analyticOnNhd
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) :
    AnalyticOnNhd ℂ
      (plusSaddleFinitePoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) := by
  intro z hz
  have hnormal :=
    plusSaddleFinitePoleRegularPart_meromorphicNFOn
      ε ℓ N hz
  obtain ⟨c, hlimit⟩ :=
    plusSaddleFinitePoleSubtraction_tendsto_of_mem
      hε horder ℓ N hz
  have hregular :
      Tendsto (plusSaddleFinitePoleRegularPart ε ℓ N)
        (𝓝[≠] z) (𝓝 c) :=
    hlimit.congr'
      (plusSaddleFinitePoleRegularPart_eq_on_punctured
        hε horder ℓ N hz).symm
  exact hnormal.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    ((tendsto_nhds_iff_meromorphicOrderAt_nonneg
      hnormal.meromorphicAt).mp ⟨c, hregular⟩)
theorem minusSaddleFinitePoleRegularPart_analyticOnNhd
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) :
    AnalyticOnNhd ℂ
      (minusSaddleFinitePoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) := by
  intro z hz
  have hnormal :=
    minusSaddleFinitePoleRegularPart_meromorphicNFOn
      ε ℓ N hz
  obtain ⟨c, hlimit⟩ :=
    minusSaddleFinitePoleSubtraction_tendsto_of_mem
      hε horder ℓ N hz
  have hregular :
      Tendsto (minusSaddleFinitePoleRegularPart ε ℓ N)
        (𝓝[≠] z) (𝓝 c) :=
    hlimit.congr'
      (minusSaddleFinitePoleRegularPart_eq_on_punctured
        hε horder ℓ N hz).symm
  exact hnormal.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    ((tendsto_nhds_iff_meromorphicOrderAt_nonneg
      hnormal.meromorphicAt).mp ⟨c, hregular⟩)
theorem plusSaddleFinitePoleRegularPart_eq_subtraction_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hpole : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    plusSaddleFinitePoleRegularPart ε ℓ N z =
      plusSaddleFinitePoleSubtraction ε ℓ N z := by
  have hregular :=
    (plusSaddleFinitePoleRegularPart_analyticOnNhd
      hε horder ℓ N z hz).continuousAt
  have hsubtraction :=
    (plusSaddleFinitePoleSubtraction_differentiableAt_of_not_pole
      hε horder ℓ N hpole).continuousAt
  have hpunctured :=
    plusSaddleFinitePoleRegularPart_eq_on_punctured
      hε horder ℓ N hz
  exact ((hregular.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hsubtraction).mp hpunctured).eq_of_nhds
theorem minusSaddleFinitePoleRegularPart_eq_subtraction_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hpole : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    minusSaddleFinitePoleRegularPart ε ℓ N z =
      minusSaddleFinitePoleSubtraction ε ℓ N z := by
  have hregular :=
    (minusSaddleFinitePoleRegularPart_analyticOnNhd
      hε horder ℓ N z hz).continuousAt
  have hsubtraction :=
    (minusSaddleFinitePoleSubtraction_differentiableAt_of_not_pole
      hε horder ℓ N hpole).continuousAt
  have hpunctured :=
    minusSaddleFinitePoleRegularPart_eq_on_punctured
      hε horder ℓ N hz
  exact ((hregular.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hsubtraction).mp hpunctured).eq_of_nhds
theorem plusSaddleFinitePoleRegularPart_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) :
    DifferentiableOn ℂ
      (plusSaddleFinitePoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) :=
  (plusSaddleFinitePoleRegularPart_analyticOnNhd
    hε horder ℓ N).differentiableOn
theorem minusSaddleFinitePoleRegularPart_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) :
    DifferentiableOn ℂ
      (minusSaddleFinitePoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) :=
  (minusSaddleFinitePoleRegularPart_analyticOnNhd
    hε horder ℓ N).differentiableOn
theorem saddleFinitePoleHalfPlane_reProdIm_subset
    {N : ℕ} {z w : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hw : w ∈ saddleFinitePoleHalfPlane N) :
    ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) ⊆
      saddleFinitePoleHalfPlane N := by
  intro u hu
  have hre : u.re ∈ [[z.re, w.re]] :=
    (Complex.mem_reProdIm.mp hu).1
  change -(2 * ((N : ℝ) + 1)) < z.re at hz
  change -(2 * ((N : ℝ) + 1)) < w.re at hw
  change -(2 * ((N : ℝ) + 1)) < u.re
  rcases Set.mem_uIcc.mp hre with hleft | hright
  · exact hz.trans_le hleft.1
  · exact hw.trans_le hright.1
def saddleMellinInversePower (r : ℝ) (z : ℂ) : ℂ :=
  (r : ℂ) ^ (-z)
theorem saddleMellinInversePower_differentiable
    {r : ℝ} (hr : 0 < r) :
    Differentiable ℂ (saddleMellinInversePower r) := by
  have hnonzero : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  have hform :
      (fun z : ℂ => (r : ℂ) ^ (-z)) =
        (fun z : ℂ =>
          Complex.exp
            (Complex.log (r : ℂ) * (-z))) := by
    funext z
    exact Complex.cpow_def_of_ne_zero hnonzero (-z)
  change Differentiable ℂ
    (fun z : ℂ => (r : ℂ) ^ (-z))
  rw [hform]
  fun_prop
def saddleGaussianPoleSlope (z : ℂ) : ℂ :=
  dslope (fun w : ℂ => Complex.exp (w ^ 2)) 0 z
theorem saddleGaussianPoleSlope_differentiable :
    Differentiable ℂ saddleGaussianPoleSlope := by
  have hgaussian :
      Differentiable ℂ
        (fun w : ℂ => Complex.exp (w ^ 2)) := by
    fun_prop
  unfold saddleGaussianPoleSlope
  exact differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope
      (s := Set.univ) (c := (0 : ℂ))
      (show Set.univ ∈ 𝓝 (0 : ℂ) from univ_mem)).mpr
        hgaussian.differentiableOn)
theorem saddleGaussianPoleSlope_mul (z : ℂ) :
    z * saddleGaussianPoleSlope z =
      Complex.exp (z ^ 2) - 1 := by
  have h := sub_smul_dslope
    (fun w : ℂ => Complex.exp (w ^ 2)) 0 z
  simpa [saddleGaussianPoleSlope, smul_eq_mul] using! h
theorem saddleGaussianPoleSlope_eq_of_ne
    {z : ℂ} (hz : z ≠ 0) :
    saddleGaussianPoleSlope z =
      (Complex.exp (z ^ 2) - 1) / z := by
  apply (eq_div_iff hz).2
  simpa [mul_comm] using! saddleGaussianPoleSlope_mul z
def saddleGaussianPoleRepresentative
    (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ((z + ((2 * n : ℕ) : ℂ)) ^ 2) /
    (z + ((2 * n : ℕ) : ℂ))
def plusSaddleFiniteRapidPoleSubtraction
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  plusSaddleMellinData ε ℓ z -
    ∑ n ∈ Finset.range (N + 1),
      plusSaddlePoleResidue ε ℓ n *
        saddleGaussianPoleRepresentative n z
def minusSaddleFiniteRapidPoleSubtraction
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  minusSaddleMellinData ε ℓ z -
    ∑ n ∈ Finset.range (N + 1),
      minusSaddlePoleResidue ε ℓ n *
        saddleGaussianPoleRepresentative n z
def plusSaddleFiniteRapidPoleRegularPart
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  plusSaddleFinitePoleRegularPart ε ℓ N z -
    ∑ n ∈ Finset.range (N + 1),
      plusSaddlePoleResidue ε ℓ n *
        saddleGaussianPoleSlope
          (z + ((2 * n : ℕ) : ℂ))
def minusSaddleFiniteRapidPoleRegularPart
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  minusSaddleFinitePoleRegularPart ε ℓ N z -
    ∑ n ∈ Finset.range (N + 1),
      minusSaddlePoleResidue ε ℓ n *
        saddleGaussianPoleSlope
          (z + ((2 * n : ℕ) : ℂ))
theorem plusSaddleFiniteRapidPoleRegularPart_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) :
    DifferentiableOn ℂ
      (plusSaddleFiniteRapidPoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) := by
  unfold plusSaddleFiniteRapidPoleRegularPart
  apply (plusSaddleFinitePoleRegularPart_differentiableOn
    hε horder ℓ N).sub
  apply DifferentiableOn.fun_sum
  intro n _
  have hconstant : DifferentiableOn ℂ
      (fun _ : ℂ => plusSaddlePoleResidue ε ℓ n)
      (saddleFinitePoleHalfPlane N) := by
    fun_prop
  have hslope : Differentiable ℂ
      (fun z : ℂ => saddleGaussianPoleSlope
        (z + ((2 * n : ℕ) : ℂ))) :=
    saddleGaussianPoleSlope_differentiable.comp (by fun_prop)
  exact hconstant.mul hslope.differentiableOn
theorem minusSaddleFiniteRapidPoleRegularPart_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) :
    DifferentiableOn ℂ
      (minusSaddleFiniteRapidPoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) := by
  unfold minusSaddleFiniteRapidPoleRegularPart
  apply (minusSaddleFinitePoleRegularPart_differentiableOn
    hε horder ℓ N).sub
  apply DifferentiableOn.fun_sum
  intro n _
  have hconstant : DifferentiableOn ℂ
      (fun _ : ℂ => minusSaddlePoleResidue ε ℓ n)
      (saddleFinitePoleHalfPlane N) := by
    fun_prop
  have hslope : Differentiable ℂ
      (fun z : ℂ => saddleGaussianPoleSlope
        (z + ((2 * n : ℕ) : ℂ))) :=
    saddleGaussianPoleSlope_differentiable.comp (by fun_prop)
  exact hconstant.mul hslope.differentiableOn
theorem plusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hpole : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    plusSaddleFiniteRapidPoleRegularPart ε ℓ N z =
      plusSaddleFiniteRapidPoleSubtraction ε ℓ N z := by
  unfold plusSaddleFiniteRapidPoleRegularPart
    plusSaddleFiniteRapidPoleSubtraction
  rw [plusSaddleFinitePoleRegularPart_eq_subtraction_of_not_pole
    hε horder ℓ N hz hpole]
  unfold plusSaddleFinitePoleSubtraction
  have hsum :
      (∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n /
          (z + ((2 * n : ℕ) : ℂ))) +
      (∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          saddleGaussianPoleSlope
            (z + ((2 * n : ℕ) : ℂ))) =
      ∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          saddleGaussianPoleRepresentative n z := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    have hcoordinate :
        z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
      intro hzero
      apply hpole n
      linear_combination hzero
    rw [saddleGaussianPoleSlope_eq_of_ne hcoordinate]
    unfold saddleGaussianPoleRepresentative
    field_simp [hcoordinate]
    ring
  linear_combination -hsum
theorem minusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hpole : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    minusSaddleFiniteRapidPoleRegularPart ε ℓ N z =
      minusSaddleFiniteRapidPoleSubtraction ε ℓ N z := by
  unfold minusSaddleFiniteRapidPoleRegularPart
    minusSaddleFiniteRapidPoleSubtraction
  rw [minusSaddleFinitePoleRegularPart_eq_subtraction_of_not_pole
    hε horder ℓ N hz hpole]
  unfold minusSaddleFinitePoleSubtraction
  have hsum :
      (∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n /
          (z + ((2 * n : ℕ) : ℂ))) +
      (∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n *
          saddleGaussianPoleSlope
            (z + ((2 * n : ℕ) : ℂ))) =
      ∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n *
          saddleGaussianPoleRepresentative n z := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    have hcoordinate :
        z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
      intro hzero
      apply hpole n
      linear_combination hzero
    rw [saddleGaussianPoleSlope_eq_of_ne hcoordinate]
    unfold saddleGaussianPoleRepresentative
    field_simp [hcoordinate]
    ring
  linear_combination -hsum
def plusSaddleFiniteRapidContourIntegrand
    (ε ℓ : ℝ) (N : ℕ) (r : ℝ) (z : ℂ) : ℂ :=
  saddleMellinInversePower r z *
    plusSaddleFiniteRapidPoleRegularPart ε ℓ N z
def minusSaddleFiniteRapidContourIntegrand
    (ε ℓ : ℝ) (N : ℕ) (r : ℝ) (z : ℂ) : ℂ :=
  saddleMellinInversePower r z *
    minusSaddleFiniteRapidPoleRegularPart ε ℓ N z
theorem plusSaddleFiniteRapidContourIntegrand_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    DifferentiableOn ℂ
      (plusSaddleFiniteRapidContourIntegrand ε ℓ N r)
      (saddleFinitePoleHalfPlane N) := by
  unfold plusSaddleFiniteRapidContourIntegrand
  exact (saddleMellinInversePower_differentiable hr).differentiableOn.mul
    (plusSaddleFiniteRapidPoleRegularPart_differentiableOn
      hε horder ℓ N)
theorem minusSaddleFiniteRapidContourIntegrand_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    DifferentiableOn ℂ
      (minusSaddleFiniteRapidContourIntegrand ε ℓ N r)
      (saddleFinitePoleHalfPlane N) := by
  unfold minusSaddleFiniteRapidContourIntegrand
  exact (saddleMellinInversePower_differentiable hr).differentiableOn.mul
    (minusSaddleFiniteRapidPoleRegularPart_differentiableOn
      hε horder ℓ N)
theorem plusSaddleFiniteRapidContourIntegrand_boundary_rectangle
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r)
    (z w : ℂ)
    (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hw : w ∈ saddleFinitePoleHalfPlane N) :
    (∫ x : ℝ in z.re..w.re,
      plusSaddleFiniteRapidContourIntegrand ε ℓ N r
        (x + z.im * Complex.I)) -
    (∫ x : ℝ in z.re..w.re,
      plusSaddleFiniteRapidContourIntegrand ε ℓ N r
        (x + w.im * Complex.I)) +
    Complex.I •
      (∫ y : ℝ in z.im..w.im,
        plusSaddleFiniteRapidContourIntegrand ε ℓ N r
          (w.re + y * Complex.I)) -
    Complex.I •
      (∫ y : ℝ in z.im..w.im,
        plusSaddleFiniteRapidContourIntegrand ε ℓ N r
          (z.re + y * Complex.I)) = 0 := by
  refine Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (plusSaddleFiniteRapidContourIntegrand ε ℓ N r) z w ?_
  exact (plusSaddleFiniteRapidContourIntegrand_differentiableOn
    hε horder ℓ N hr).mono
      (saddleFinitePoleHalfPlane_reProdIm_subset hz hw)
theorem minusSaddleFiniteRapidContourIntegrand_boundary_rectangle
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r)
    (z w : ℂ)
    (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hw : w ∈ saddleFinitePoleHalfPlane N) :
    (∫ x : ℝ in z.re..w.re,
      minusSaddleFiniteRapidContourIntegrand ε ℓ N r
        (x + z.im * Complex.I)) -
    (∫ x : ℝ in z.re..w.re,
      minusSaddleFiniteRapidContourIntegrand ε ℓ N r
        (x + w.im * Complex.I)) +
    Complex.I •
      (∫ y : ℝ in z.im..w.im,
        minusSaddleFiniteRapidContourIntegrand ε ℓ N r
          (w.re + y * Complex.I)) -
    Complex.I •
      (∫ y : ℝ in z.im..w.im,
        minusSaddleFiniteRapidContourIntegrand ε ℓ N r
          (z.re + y * Complex.I)) = 0 := by
  refine Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (minusSaddleFiniteRapidContourIntegrand ε ℓ N r) z w ?_
  exact (minusSaddleFiniteRapidContourIntegrand_differentiableOn
    hε horder ℓ N hr).mono
      (saddleFinitePoleHalfPlane_reProdIm_subset hz hw)
theorem saddleMellinEnvelope_vertical (ε ℓ t : ℝ) :
    saddleMellinEnvelope ε ℓ
      ((ℓ : ℂ) - Complex.I * (t : ℂ)) =
        saddleEnvelope ε ℓ t := by
  have hfrequency :
      Complex.I *
        (((ℓ : ℂ) - Complex.I * (t : ℂ)) - (ℓ : ℂ)) /
          (ℓ : ℂ) = (t : ℂ) / (ℓ : ℂ) := by
    congr 1
    ring_nf
    simp [Complex.I_sq]
  have hpi :
      (((ℓ : ℂ) - ((ℓ : ℂ) - Complex.I * (t : ℂ))) *
        (Real.log Real.pi : ℂ) / 2) =
        Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ) / 2 := by
    ring
  unfold saddleMellinEnvelope saddleEnvelope
  rw [hfrequency, hpi]
theorem plusSaddleMellinData_vertical (ε ℓ t : ℝ) :
    plusSaddleMellinData ε ℓ
      ((ℓ : ℂ) - Complex.I * (t : ℂ)) =
        plusSaddleSpectrum ε ℓ t := by
  have hfrequency :
      Complex.I *
        (((ℓ : ℂ) - Complex.I * (t : ℂ)) - (ℓ : ℂ)) /
          (ℓ : ℂ) = (t : ℂ) / (ℓ : ℂ) := by
    congr 1
    ring_nf
    simp [Complex.I_sq]
  unfold plusSaddleMellinData plusSaddleSpectrum
  rw [saddleMellinEnvelope_vertical, hfrequency]
theorem minusSaddleMellinData_vertical (ε ℓ t : ℝ) :
    minusSaddleMellinData ε ℓ
      ((ℓ : ℂ) - Complex.I * (t : ℂ)) =
        minusSaddleSpectrum ε ℓ t := by
  have hfrequency :
      Complex.I *
        (((ℓ : ℂ) - Complex.I * (t : ℂ)) - (ℓ : ℂ)) /
          (ℓ : ℂ) = (t : ℂ) / (ℓ : ℂ) := by
    congr 1
    ring_nf
    simp [Complex.I_sq]
  unfold minusSaddleMellinData minusSaddleSpectrum
  rw [saddleMellinEnvelope_vertical, hfrequency]
def plusSaddleProfile (ε ℓ r : ℝ) : ℂ :=
  if r = 0 then (saddleOriginValue ε ℓ : ℂ)
  else mellinInv ℓ (plusSaddleMellinData ε ℓ) r
def minusSaddleProfile (ε ℓ r : ℝ) : ℂ :=
  if r = 0 then (saddleOriginValue ε ℓ : ℂ)
  else mellinInv ℓ (minusSaddleMellinData ε ℓ) r
def plusSaddleFunction (ε : ℝ) (d : ℕ) (x : Euclidean d) : ℂ :=
  plusSaddleProfile ε ((d : ℝ) / 2) ‖x‖
def minusSaddleFunction (ε : ℝ) (d : ℕ) (x : Euclidean d) : ℂ :=
  minusSaddleProfile ε ((d : ℝ) / 2) ‖x‖
theorem plusSaddleFunction_radial (ε : ℝ) (d : ℕ)
    (x y : Euclidean d) (hxy : ‖x‖ = ‖y‖) :
    plusSaddleFunction ε d x = plusSaddleFunction ε d y := by
  simp only [plusSaddleFunction, hxy]
theorem minusSaddleFunction_radial (ε : ℝ) (d : ℕ)
    (x y : Euclidean d) (hxy : ‖x‖ = ‖y‖) :
    minusSaddleFunction ε d x = minusSaddleFunction ε d y := by
  simp only [minusSaddleFunction, hxy]
@[simp] theorem plusSaddleFunction_zero (ε : ℝ) (d : ℕ) :
    plusSaddleFunction ε d (0 : Euclidean d) =
      (saddleOriginValue ε ((d : ℝ) / 2) : ℂ) := by
  simp [plusSaddleFunction, plusSaddleProfile]
@[simp] theorem minusSaddleFunction_zero (ε : ℝ) (d : ℕ) :
    minusSaddleFunction ε d (0 : Euclidean d) =
      (saddleOriginValue ε ((d : ℝ) / 2) : ℂ) := by
  simp [minusSaddleFunction, minusSaddleProfile]
theorem saddleFunction_zero_pos {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    0 < (plusSaddleFunction ε d (0 : Euclidean d)).re ∧
      0 < (minusSaddleFunction ε d (0 : Euclidean d)).re := by
  constructor
  · simpa using! saddleOriginValue_pos hε ((d : ℝ) / 2)
  · simpa using! saddleOriginValue_pos hε ((d : ℝ) / 2)
theorem minusPolynomial_neg (ε : ℝ) (z : ℂ) :
    minusPolynomial ε (-z) = plusPolynomial ε z := by
  unfold minusPolynomial plusPolynomial
  ring
theorem plusPolynomial_conj (ε : ℝ) (z : ℂ) :
    starRingEnd ℂ (plusPolynomial ε z) =
      minusPolynomial ε (starRingEnd ℂ z) := by
  unfold plusPolynomial minusPolynomial
  simp only [map_add, map_mul, map_pow, map_one,
    Complex.conj_ofReal, Complex.conj_I]
  ring
theorem minusPolynomial_conj (ε : ℝ) (z : ℂ) :
    starRingEnd ℂ (minusPolynomial ε z) =
      plusPolynomial ε (starRingEnd ℂ z) := by
  unfold minusPolynomial plusPolynomial
  simp only [map_add, map_sub, map_mul, map_pow, map_one,
    Complex.conj_ofReal, Complex.conj_I]
  ring
theorem norm_plusPolynomial_le (ε : ℝ) (z : ℂ) :
    ‖plusPolynomial ε z‖ ≤
      (1 + |beta ε|) * (1 + ‖z‖) ^ 3 := by
  have hz : 0 ≤ ‖z‖ := norm_nonneg _
  have hbase : ‖(1 : ℂ) + z ^ 2‖ ≤ 1 + ‖z‖ ^ 2 := by
    calc
      ‖(1 : ℂ) + z ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2‖ :=
        norm_add_le _ _
      _ = 1 + ‖z‖ ^ 2 := by simp [norm_pow]
  have hsq : 1 + ‖z‖ ^ 2 ≤ (1 + ‖z‖) ^ 2 := by
    nlinarith
  have hcube : (1 : ℝ) ≤ (1 + ‖z‖) ^ 3 :=
    one_le_pow₀ (by linarith)
  unfold plusPolynomial
  calc
    ‖1 + z ^ 2 + (beta ε : ℂ) +
      Complex.I * z * (1 + z ^ 2)‖
      ≤ ‖1 + z ^ 2 + (beta ε : ℂ)‖ +
          ‖Complex.I * z * (1 + z ^ 2)‖ :=
            norm_add_le _ _
    _ ≤ (1 + ‖z‖ ^ 2 + |beta ε|) +
          ‖z‖ * (1 + ‖z‖ ^ 2) := by
            have hfirst :
                ‖1 + z ^ 2 + (beta ε : ℂ)‖ ≤
                  1 + ‖z‖ ^ 2 + |beta ε| := by
              calc
                ‖1 + z ^ 2 + (beta ε : ℂ)‖ ≤
                    ‖1 + z ^ 2‖ + ‖(beta ε : ℂ)‖ :=
                      norm_add_le _ _
                _ ≤ 1 + ‖z‖ ^ 2 + |beta ε| := by
                      simpa using! add_le_add_right hbase |beta ε|
            have hsecond :
                ‖Complex.I * z * (1 + z ^ 2)‖ ≤
                  ‖z‖ * (1 + ‖z‖ ^ 2) := by
              rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
              gcongr
            exact add_le_add hfirst hsecond
    _ ≤ (1 + ‖z‖) ^ 2 + |beta ε| +
          ‖z‖ * (1 + ‖z‖) ^ 2 := by
            gcongr
    _ = (1 + ‖z‖) ^ 3 + |beta ε| := by ring
    _ ≤ (1 + |beta ε|) * (1 + ‖z‖) ^ 3 := by
          nlinarith [mul_le_mul_of_nonneg_left hcube
            (abs_nonneg (beta ε))]
theorem norm_minusPolynomial_le (ε : ℝ) (z : ℂ) :
    ‖minusPolynomial ε z‖ ≤
      (1 + |beta ε|) * (1 + ‖z‖) ^ 3 := by
  have h := norm_plusPolynomial_le ε (starRingEnd ℂ z)
  rw [RCLike.norm_conj] at h
  have hconj := plusPolynomial_conj ε (starRingEnd ℂ z)
  rw [Complex.conj_conj] at hconj
  rw [← hconj, RCLike.norm_conj]
  exact h
theorem norm_complexGamma_le_realGamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral,
    Real.Gamma_eq_integral hz]
  calc
    ‖∫ x in Set.Ioi (0 : ℝ),
      (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)‖
      ≤ ∫ x in Set.Ioi (0 : ℝ),
          ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)‖ :=
            norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0 : ℝ),
          Real.exp (-x) * x ^ (z.re - 1) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            try dsimp
            rw [norm_mul,
              Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
              Complex.norm_cpow_eq_rpow_re_of_pos hx]
            simp
theorem complexGamma_vertical_polynomial_bound {z : ℂ}
    (hz : 0 < z.re) (k : ℕ) :
    |z.im| ^ k * ‖Complex.Gamma z‖ ≤
      Real.Gamma (z.re + k) := by
  have hnonzero : ∀ j : ℕ, z + (j : ℂ) ≠ 0 := by
    intro j hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hprod :
      |z.im| ^ k ≤
        ∏ j ∈ Finset.range k, ‖z + (j : ℂ)‖ := by
    simpa using!
      (Finset.prod_le_prod
        (s := Finset.range k)
        (f := fun _ : ℕ => |z.im|)
        (g := fun j : ℕ => ‖z + (j : ℂ)‖)
        (fun _ _ => abs_nonneg _)
        (fun j _ => by
          simpa using! Complex.abs_im_le_norm (z + (j : ℂ))))
  have hshift : 0 < (z + (k : ℂ)).re := by
    simpa using! add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg k)
  calc
    |z.im| ^ k * ‖Complex.Gamma z‖ ≤
        (∏ j ∈ Finset.range k, ‖z + (j : ℂ)‖) *
          ‖Complex.Gamma z‖ := by
            gcongr
    _ = ‖Complex.Gamma z *
          ∏ j ∈ Finset.range k, (z + (j : ℂ))‖ := by
            rw [norm_mul, norm_prod]
            ring
    _ = ‖Complex.Gamma (z + (k : ℂ))‖ := by
            rw [gamma_add_nat_eq_product z hnonzero k]
    _ ≤ Real.Gamma (z.re + k) := by
            simpa using! norm_complexGamma_le_realGamma hshift
theorem complexGamma_shifted_vertical_polynomial_bound
    {z : ℂ} (hz : z.im ≠ 0) (k : ℕ)
    (hshift : 0 < z.re + k) :
    |z.im| ^ k * ‖Complex.Gamma z‖ ≤
      Real.Gamma (z.re + k) := by
  have hnonzero : ∀ j : ℕ, z + (j : ℂ) ≠ 0 := by
    intro j hzero
    apply hz
    have him := congrArg Complex.im hzero
    simpa using! him
  have hprod :
      |z.im| ^ k ≤
        ∏ j ∈ Finset.range k, ‖z + (j : ℂ)‖ := by
    simpa using!
      (Finset.prod_le_prod
        (s := Finset.range k)
        (f := fun _ : ℕ => |z.im|)
        (g := fun j : ℕ => ‖z + (j : ℂ)‖)
        (fun _ _ => abs_nonneg _)
        (fun j _ => by
          simpa using! Complex.abs_im_le_norm (z + (j : ℂ))))
  have hpositive : 0 < (z + (k : ℂ)).re := by
    simpa using! hshift
  calc
    |z.im| ^ k * ‖Complex.Gamma z‖ ≤
        (∏ j ∈ Finset.range k, ‖z + (j : ℂ)‖) *
          ‖Complex.Gamma z‖ := by
            gcongr
    _ = ‖Complex.Gamma z *
          ∏ j ∈ Finset.range k, (z + (j : ℂ))‖ := by
            rw [norm_mul, norm_prod]
            ring
    _ = ‖Complex.Gamma (z + (k : ℂ))‖ := by
            rw [gamma_add_nat_eq_product z hnonzero k]
    _ ≤ Real.Gamma (z.re + k) := by
            simpa using! norm_complexGamma_le_realGamma hpositive
theorem saddleGamma_shiftedLine_polynomial_bound
    (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|)
    (k m : ℕ) (hshift : 0 < a / 2 + (k : ℝ)) :
    |t| ^ m *
        ‖Complex.Gamma
          (((a : ℂ) + (t : ℂ) * Complex.I) / 2)‖ ≤
      (2 : ℝ) ^ (k + m) *
        Real.Gamma (a / 2 + ((k + m : ℕ) : ℝ)) := by
  let z : ℂ :=
    ((a : ℂ) + (t : ℂ) * Complex.I) / 2
  have hre : z.re = a / 2 := by
    try dsimp [z]
    norm_num [Complex.mul_re, Complex.mul_im]
  have him : z.im = t / 2 := by
    try dsimp [z]
    norm_num [Complex.mul_re, Complex.mul_im]
  have htzero : t ≠ 0 := by
    intro hzero
    have himpossible : (1 : ℝ) ≤ 0 := by
      simpa [hzero] using! ht
    norm_num at himpossible
  have hnonzero : z.im ≠ 0 := by
    rw [him]
    exact div_ne_zero htzero (by norm_num)
  have hpositive :
      0 < z.re + ((k + m : ℕ) : ℝ) := by
    rw [hre, Nat.cast_add]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hgamma :
      (|t| / 2) ^ (k + m) *
          ‖Complex.Gamma z‖ ≤
        Real.Gamma
          (a / 2 + ((k + m : ℕ) : ℝ)) := by
    simpa [hre, him, abs_div] using!
      (complexGamma_shifted_vertical_polynomial_bound
        hnonzero (k + m) hpositive)
  have hpow : |t| ^ m ≤ |t| ^ (k + m) :=
    pow_le_pow_right₀ ht (by omega)
  change |t| ^ m * ‖Complex.Gamma z‖ ≤ _
  calc
    |t| ^ m * ‖Complex.Gamma z‖ ≤
        |t| ^ (k + m) * ‖Complex.Gamma z‖ := by
          gcongr
    _ = (2 : ℝ) ^ (k + m) *
          ((|t| / 2) ^ (k + m) *
            ‖Complex.Gamma z‖) := by
          rw [div_pow]
          field_simp
    _ ≤ (2 : ℝ) ^ (k + m) *
          Real.Gamma
            (a / 2 + ((k + m : ℕ) : ℝ)) := by
          gcongr
theorem norm_complexCos_le_cosh_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  change
    ‖(Complex.exp (z * Complex.I) +
      Complex.exp (-z * Complex.I)) / 2‖ ≤ Real.cosh z.im
  calc
    ‖(Complex.exp (z * Complex.I) +
      Complex.exp (-z * Complex.I)) / 2‖ =
        ‖Complex.exp (z * Complex.I) +
          Complex.exp (-z * Complex.I)‖ / 2 := by
            rw [norm_div]
            norm_num
    _ ≤ (‖Complex.exp (z * Complex.I)‖ +
          ‖Complex.exp (-z * Complex.I)‖) / 2 := by
            gcongr
            exact norm_add_le _ _
    _ = Real.cosh z.im := by
          rw [Complex.norm_exp, Complex.norm_exp,
            Real.cosh_eq]
          simp [Complex.mul_re, add_comm]
def saddleHorizontalShellVariation (ε H : ℝ) : ℝ :=
  (∫ a in shortCutoff ε..shortEndpoint ε,
    |shortShellDensity ε a| * (Real.cosh (a * H) + 1)) +
  (∫ a in shellLocation ε..shellLocation ε + 1,
    |positiveShellDensity ε a| * (Real.cosh (a * H) + 1))
theorem saddleHorizontalShellVariation_mono
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {H K : ℝ} (hH : 0 ≤ H) (hHK : H ≤ K) :
    saddleHorizontalShellVariation ε H ≤
      saddleHorizontalShellVariation ε K := by
  have hK : 0 ≤ K := hH.trans hHK
  have hcosH : Continuous
      (fun a : ℝ => Real.cosh (a * H) + 1) := by
    fun_prop
  have hcosK : Continuous
      (fun a : ℝ => Real.cosh (a * K) + 1) := by
    fun_prop
  have hcos (a : ℝ) :
      Real.cosh (a * H) ≤ Real.cosh (a * K) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_mul, abs_mul, abs_of_nonneg hH,
      abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_left hHK (abs_nonneg a)
  have hshort :
      (∫ a in shortCutoff ε..shortEndpoint ε,
        |shortShellDensity ε a| *
          (Real.cosh (a * H) + 1)) ≤
      (∫ a in shortCutoff ε..shortEndpoint ε,
        |shortShellDensity ε a| *
          (Real.cosh (a * K) + 1)) := by
    apply intervalIntegral.integral_mono_on horder
      ((shortShellDensity_intervalIntegrable hε horder).abs
        |>.mul_continuousOn hcosH.continuousOn)
      ((shortShellDensity_intervalIntegrable hε horder).abs
        |>.mul_continuousOn hcosK.continuousOn)
    intro a _
    gcongr
    exact hcos a
  have hB : shellLocation ε ≤ shellLocation ε + 1 := by
    linarith
  have hp : IntervalIntegrable (positiveShellDensity ε) volume
      (shellLocation ε) (shellLocation ε + 1) :=
    (positiveShellDensity_continuous ε).intervalIntegrable
      (shellLocation ε) (shellLocation ε + 1)
  have hpositive :
      (∫ a in shellLocation ε..shellLocation ε + 1,
        |positiveShellDensity ε a| *
          (Real.cosh (a * H) + 1)) ≤
      (∫ a in shellLocation ε..shellLocation ε + 1,
        |positiveShellDensity ε a| *
          (Real.cosh (a * K) + 1)) := by
    apply intervalIntegral.integral_mono_on hB
      (hp.abs.mul_continuousOn hcosH.continuousOn)
      (hp.abs.mul_continuousOn hcosK.continuousOn)
    intro a _
    gcongr
    exact hcos a
  exact add_le_add hshort hpositive
theorem norm_mellinShellPhase_le_horizontalVariation
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {z : ℂ} {H : ℝ} (hstrip : |z.im| ≤ H) :
    ‖mellinShellPhase ε z‖ ≤
      saddleHorizontalShellVariation ε H := by
  have hH : 0 ≤ H := (abs_nonneg z.im).trans hstrip
  have hcutoff : 0 < shortCutoff ε := by
    unfold shortCutoff
    positivity
  have hlocation : 0 < shellLocation ε := by
    unfold shellLocation
    positivity
  have hcosh : Continuous
      (fun a : ℝ => Real.cosh (a * H) + 1) := by
    fun_prop
  have hcos (a : ℝ) (ha : 0 ≤ a) :
      ‖Complex.cos ((a : ℂ) * z) - 1‖ ≤
        Real.cosh (a * H) + 1 := by
    have him :
        |((a : ℂ) * z).im| ≤ |a * H| := by
      simp only [Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, abs_mul,
        abs_of_nonneg ha, abs_of_nonneg hH]
      exact mul_le_mul_of_nonneg_left hstrip ha
    calc
      ‖Complex.cos ((a : ℂ) * z) - 1‖ ≤
          ‖Complex.cos ((a : ℂ) * z)‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
      _ = ‖Complex.cos ((a : ℂ) * z)‖ + 1 := by
            norm_num
      _ ≤ Real.cosh ((a : ℂ) * z).im + 1 := by
            gcongr
            exact norm_complexCos_le_cosh_im ((a : ℂ) * z)
      _ ≤ Real.cosh (a * H) + 1 := by
            gcongr
            exact Real.cosh_le_cosh.mpr him
  have hshort :
      ‖∫ a in shortCutoff ε..shortEndpoint ε,
          (shortShellDensity ε a : ℂ) *
            (Complex.cos ((a : ℂ) * z) - 1)‖ ≤
        ∫ a in shortCutoff ε..shortEndpoint ε,
          |shortShellDensity ε a| *
            (Real.cosh (a * H) + 1) := by
    apply intervalIntegral.norm_integral_le_of_norm_le horder
    · exact Filter.Eventually.of_forall (fun a ha => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (hcos a (hcutoff.le.trans ha.1.le))
          (abs_nonneg (shortShellDensity ε a)))
    · exact (shortShellDensity_intervalIntegrable
        hε horder).abs.mul_continuousOn hcosh.continuousOn
  have hB : shellLocation ε ≤ shellLocation ε + 1 := by
    linarith
  have hpositive :
      ‖∫ a in shellLocation ε..shellLocation ε + 1,
          (positiveShellDensity ε a : ℂ) *
            (Complex.cos ((a : ℂ) * z) - 1)‖ ≤
        ∫ a in shellLocation ε..shellLocation ε + 1,
          |positiveShellDensity ε a| *
            (Real.cosh (a * H) + 1) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hB
    · exact Filter.Eventually.of_forall (fun a ha => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (hcos a (hlocation.le.trans ha.1.le))
          (abs_nonneg (positiveShellDensity ε a)))
    · exact ((positiveShellDensity_continuous ε).intervalIntegrable
        (shellLocation ε) (shellLocation ε + 1)).abs.mul_continuousOn
          hcosh.continuousOn
  unfold mellinShellPhase saddleHorizontalShellVariation
  exact (norm_add_le _ _).trans (add_le_add hshort hpositive)
theorem norm_saddleShellExponential_horizontal_le
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ) (z : ℂ) :
    ‖Complex.exp ((ℓ : ℂ) * mellinShellPhase ε z)‖ ≤
      Real.exp
        (|ℓ| * saddleHorizontalShellVariation ε |z.im|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (((ℓ : ℂ) * mellinShellPhase ε z)).re ≤
        ‖(ℓ : ℂ) * mellinShellPhase ε z‖ :=
          Complex.re_le_norm _
    _ = |ℓ| * ‖mellinShellPhase ε z‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |ℓ| * saddleHorizontalShellVariation ε |z.im| := by
          gcongr
          exact norm_mellinShellPhase_le_horizontalVariation
            hε horder (le_refl |z.im|)
theorem saddleMellinShellArgument_shiftedLine
    {ℓ : ℝ} (hℓ : 0 < ℓ) (a t : ℝ) :
    Complex.I *
      (((a : ℂ) + (t : ℂ) * Complex.I) -
        (ℓ : ℂ)) / (ℓ : ℂ) =
      ((-t / ℓ : ℝ) : ℂ) +
        Complex.I * (((a - ℓ) / ℓ : ℝ) : ℂ) := by
  have hnonzero : (ℓ : ℂ) ≠ 0 := by
    exact_mod_cast hℓ.ne'
  push_cast
  field_simp [hnonzero]
  ring_nf
  simp [Complex.I_sq]; ring
theorem saddleMellinPiFactor_shiftedLine_norm
    (ℓ a t : ℝ) :
    ‖Complex.exp
      (((ℓ : ℂ) -
          ((a : ℂ) + (t : ℂ) * Complex.I)) *
        (Real.log Real.pi : ℂ) / 2)‖ =
      Real.exp ((ℓ - a) * Real.log Real.pi / 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
theorem norm_saddleShellExponential_shiftedLine_le
    {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (a t : ℝ) :
    ‖Complex.exp
      ((ℓ : ℂ) * mellinShellPhase ε
        (Complex.I *
          (((a : ℂ) + (t : ℂ) * Complex.I) -
            (ℓ : ℂ)) / (ℓ : ℂ)))‖ ≤
      Real.exp
        (ℓ * saddleHorizontalShellVariation ε
          |(a - ℓ) / ℓ|) := by
  calc
    _ ≤ Real.exp
        (|ℓ| * saddleHorizontalShellVariation ε
          |(Complex.I *
            (((a : ℂ) + (t : ℂ) * Complex.I) -
              (ℓ : ℂ)) / (ℓ : ℂ)).im|) :=
      norm_saddleShellExponential_horizontal_le
        hε horder ℓ _
    _ = _ := by
      rw [saddleMellinShellArgument_shiftedLine hℓ a t]
      simp [Complex.mul_im, abs_of_pos hℓ]
theorem saddleMellinShellArgument_shiftedLine_norm_le
    {ℓ : ℝ} (hℓ : 0 < ℓ) (a t : ℝ) :
    ‖Complex.I *
      (((a : ℂ) + (t : ℂ) * Complex.I) -
        (ℓ : ℂ)) / (ℓ : ℂ)‖ ≤
      |t| / ℓ + |(a - ℓ) / ℓ| := by
  rw [saddleMellinShellArgument_shiftedLine hℓ a t]
  calc
    ‖((-t / ℓ : ℝ) : ℂ) +
      Complex.I * (((a - ℓ) / ℓ : ℝ) : ℂ)‖ ≤
        ‖((-t / ℓ : ℝ) : ℂ)‖ +
          ‖Complex.I *
            (((a - ℓ) / ℓ : ℝ) : ℂ)‖ :=
      norm_add_le _ _
    _ = |t| / ℓ + |(a - ℓ) / ℓ| := by
      simp [Complex.norm_real,
        Real.norm_eq_abs, abs_div,
        abs_of_pos hℓ]
      rw [← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
theorem saddleMellinShellArgument_shiftedLine_linear_le
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|) :
    1 + ‖Complex.I *
      (((a : ℂ) + (t : ℂ) * Complex.I) -
        (ℓ : ℂ)) / (ℓ : ℂ)‖ ≤
      (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) * |t| := by
  have hargument :=
    saddleMellinShellArgument_shiftedLine_norm_le
      hℓ a t
  have hoffset := mul_le_mul_of_nonneg_left ht
    (abs_nonneg ((a - ℓ) / ℓ))
  calc
    _ ≤ 1 + (|t| / ℓ + |(a - ℓ) / ℓ|) := by
      gcongr
    _ ≤ |t| + |t| / ℓ +
          |(a - ℓ) / ℓ| * |t| := by
      linarith
    _ = _ := by
      rw [div_eq_mul_inv]
      ring
theorem norm_plusPolynomial_shiftedLine_le
    {ε ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖plusPolynomial ε
      (Complex.I *
        (((a : ℂ) + (t : ℂ) * Complex.I) -
          (ℓ : ℂ)) / (ℓ : ℂ))‖ ≤
      (1 + |beta ε|) *
        (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3 *
          |t| ^ 3 := by
  calc
    _ ≤ (1 + |beta ε|) *
      (1 + ‖Complex.I *
        (((a : ℂ) + (t : ℂ) * Complex.I) -
          (ℓ : ℂ)) / (ℓ : ℂ)‖) ^ 3 :=
      norm_plusPolynomial_le ε _
    _ ≤ (1 + |beta ε|) *
      ((1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) * |t|) ^ 3 := by
      gcongr
      exact saddleMellinShellArgument_shiftedLine_linear_le
        hℓ a ht
    _ = _ := by
      rw [mul_pow]
      ring
theorem norm_minusPolynomial_shiftedLine_le
    {ε ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖minusPolynomial ε
      (Complex.I *
        (((a : ℂ) + (t : ℂ) * Complex.I) -
          (ℓ : ℂ)) / (ℓ : ℂ))‖ ≤
      (1 + |beta ε|) *
        (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3 *
          |t| ^ 3 := by
  calc
    _ ≤ (1 + |beta ε|) *
      (1 + ‖Complex.I *
        (((a : ℂ) + (t : ℂ) * Complex.I) -
          (ℓ : ℂ)) / (ℓ : ℂ)‖) ^ 3 :=
      norm_minusPolynomial_le ε _
    _ ≤ (1 + |beta ε|) *
      ((1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) * |t|) ^ 3 := by
      gcongr
      exact saddleMellinShellArgument_shiftedLine_linear_le
        hℓ a ht
    _ = _ := by
      rw [mul_pow]
      ring
def saddleShiftedLineMajorant
    (ε ℓ a : ℝ) (k m : ℕ) : ℝ :=
  ((1 + |beta ε|) *
      (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3) *
    ((2 : ℝ) ^ (k + (m + 3)) *
      Real.Gamma
        (a / 2 + ((k + (m + 3) : ℕ) : ℝ))) *
    Real.exp ((ℓ - a) * Real.log Real.pi / 2) *
    Real.exp
      (ℓ * saddleHorizontalShellVariation ε
        |(a - ℓ) / ℓ|)
theorem saddleShiftedLineMajorant_nonneg
    {ε ℓ a : ℝ} (hℓ : 0 < ℓ)
    (k m : ℕ) (hshift : 0 < a / 2 + (k : ℝ)) :
    0 ≤ saddleShiftedLineMajorant ε ℓ a k m := by
  have hgammaarg :
      0 < a / 2 + ((k + (m + 3) : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    have hm : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  unfold saddleShiftedLineMajorant
  positivity [Real.Gamma_pos_of_pos hgammaarg]
theorem plusSaddleMellinData_shiftedLine_polynomial_bound
    {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|)
    (k m : ℕ) (hshift : 0 < a / 2 + (k : ℝ)) :
    |t| ^ m *
      ‖plusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      saddleShiftedLineMajorant ε ℓ a k m := by
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  let q : ℂ :=
    Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)
  let C : ℝ :=
    (1 + |beta ε|) *
      (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3
  let G : ℝ :=
    (2 : ℝ) ^ (k + (m + 3)) *
      Real.Gamma
        (a / 2 + ((k + (m + 3) : ℕ) : ℝ))
  have hC : 0 ≤ C := by
    try dsimp [C]
    positivity
  have hgammaarg :
      0 < a / 2 + ((k + (m + 3) : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    have hm : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hG : 0 ≤ G := by
    try dsimp [G]
    positivity [Real.Gamma_pos_of_pos hgammaarg]
  have hgamma :
      |t| ^ (m + 3) *
          ‖Complex.Gamma (z / 2)‖ ≤ G := by
    simpa [z, G] using!
      (saddleGamma_shiftedLine_polynomial_bound
        a ht k (m + 3) hshift)
  have hpoly :
      ‖plusPolynomial ε q‖ ≤ C * |t| ^ 3 := by
    simpa [q, z, C] using!
      (norm_plusPolynomial_shiftedLine_le
        (ε := ε) hℓ a ht)
  have hpi :
      ‖Complex.exp
        (((ℓ : ℂ) - z) *
          (Real.log Real.pi : ℂ) / 2)‖ =
        Real.exp ((ℓ - a) * Real.log Real.pi / 2) := by
    simpa [z] using!
      saddleMellinPiFactor_shiftedLine_norm ℓ a t
  have hshell :
      ‖Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε q)‖ ≤
        Real.exp
          (ℓ * saddleHorizontalShellVariation ε
            |(a - ℓ) / ℓ|) := by
    simpa [q, z] using!
      norm_saddleShellExponential_shiftedLine_le
        hε hℓ horder a t
  change |t| ^ m *
    ‖plusSaddleMellinData ε ℓ z‖ ≤ _
  calc
    |t| ^ m * ‖plusSaddleMellinData ε ℓ z‖ =
        |t| ^ m * ‖Complex.Gamma (z / 2)‖ *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ *
          ‖plusPolynomial ε q‖ := by
      unfold plusSaddleMellinData saddleMellinEnvelope
      try dsimp [q]
      rw [norm_mul, norm_mul, norm_mul]
      ring
    _ ≤ |t| ^ m * ‖Complex.Gamma (z / 2)‖ *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ *
            (C * |t| ^ 3) := by
      gcongr
    _ = C *
          (|t| ^ (m + 3) *
            ‖Complex.Gamma (z / 2)‖) *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ := by
      rw [pow_add]
      ring
    _ ≤ C * G *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ := by
      gcongr
    _ = C * G *
          Real.exp ((ℓ - a) * Real.log Real.pi / 2) *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ := by
      rw [hpi]
    _ ≤ C * G *
          Real.exp ((ℓ - a) * Real.log Real.pi / 2) *
          Real.exp
            (ℓ * saddleHorizontalShellVariation ε
              |(a - ℓ) / ℓ|) := by
      gcongr
    _ = saddleShiftedLineMajorant ε ℓ a k m := by
      rfl
theorem minusSaddleMellinData_shiftedLine_polynomial_bound
    {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|)
    (k m : ℕ) (hshift : 0 < a / 2 + (k : ℝ)) :
    |t| ^ m *
      ‖minusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      saddleShiftedLineMajorant ε ℓ a k m := by
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  let q : ℂ :=
    Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)
  let C : ℝ :=
    (1 + |beta ε|) *
      (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3
  let G : ℝ :=
    (2 : ℝ) ^ (k + (m + 3)) *
      Real.Gamma
        (a / 2 + ((k + (m + 3) : ℕ) : ℝ))
  have hC : 0 ≤ C := by
    try dsimp [C]
    positivity
  have hgammaarg :
      0 < a / 2 + ((k + (m + 3) : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    have hm : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hG : 0 ≤ G := by
    try dsimp [G]
    positivity [Real.Gamma_pos_of_pos hgammaarg]
  have hgamma :
      |t| ^ (m + 3) *
          ‖Complex.Gamma (z / 2)‖ ≤ G := by
    simpa [z, G] using!
      (saddleGamma_shiftedLine_polynomial_bound
        a ht k (m + 3) hshift)
  have hpoly :
      ‖minusPolynomial ε q‖ ≤ C * |t| ^ 3 := by
    simpa [q, z, C] using!
      (norm_minusPolynomial_shiftedLine_le
        (ε := ε) hℓ a ht)
  have hpi :
      ‖Complex.exp
        (((ℓ : ℂ) - z) *
          (Real.log Real.pi : ℂ) / 2)‖ =
        Real.exp ((ℓ - a) * Real.log Real.pi / 2) := by
    simpa [z] using!
      saddleMellinPiFactor_shiftedLine_norm ℓ a t
  have hshell :
      ‖Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε q)‖ ≤
        Real.exp
          (ℓ * saddleHorizontalShellVariation ε
            |(a - ℓ) / ℓ|) := by
    simpa [q, z] using!
      norm_saddleShellExponential_shiftedLine_le
        hε hℓ horder a t
  change |t| ^ m *
    ‖minusSaddleMellinData ε ℓ z‖ ≤ _
  calc
    |t| ^ m * ‖minusSaddleMellinData ε ℓ z‖ =
        |t| ^ m * ‖Complex.Gamma (z / 2)‖ *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ *
          ‖minusPolynomial ε q‖ := by
      unfold minusSaddleMellinData saddleMellinEnvelope
      try dsimp [q]
      rw [norm_mul, norm_mul, norm_mul]
      ring
    _ ≤ |t| ^ m * ‖Complex.Gamma (z / 2)‖ *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ *
            (C * |t| ^ 3) := by
      gcongr
    _ = C *
          (|t| ^ (m + 3) *
            ‖Complex.Gamma (z / 2)‖) *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ := by
      rw [pow_add]
      ring
    _ ≤ C * G *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ := by
      gcongr
    _ = C * G *
          Real.exp ((ℓ - a) * Real.log Real.pi / 2) *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ := by
      rw [hpi]
    _ ≤ C * G *
          Real.exp ((ℓ - a) * Real.log Real.pi / 2) *
          Real.exp
            (ℓ * saddleHorizontalShellVariation ε
              |(a - ℓ) / ℓ|) := by
      gcongr
    _ = saddleShiftedLineMajorant ε ℓ a k m := by
      rfl
def saddleHorizontalStripHeight (ℓ A B : ℝ) : ℝ :=
  max |(A - ℓ) / ℓ| |(B - ℓ) / ℓ|
theorem saddleHorizontalStripHeight_bound
    {ℓ A B x : ℝ} (hℓ : 0 < ℓ)
    (hx : x ∈ Set.Icc A B) :
    |(x - ℓ) / ℓ| ≤ saddleHorizontalStripHeight ℓ A B := by
  have hleft : (A - ℓ) / ℓ ≤ (x - ℓ) / ℓ :=
    (div_le_div_iff_of_pos_right hℓ).2
      (sub_le_sub_right hx.1 ℓ)
  have hright : (x - ℓ) / ℓ ≤ (B - ℓ) / ℓ :=
    (div_le_div_iff_of_pos_right hℓ).2
      (sub_le_sub_right hx.2 ℓ)
  unfold saddleHorizontalStripHeight
  apply (abs_le).2
  constructor
  · calc
      -(max |(A - ℓ) / ℓ| |(B - ℓ) / ℓ|) ≤
          -|(A - ℓ) / ℓ| :=
        neg_le_neg (le_max_left _ _)
      _ ≤ (A - ℓ) / ℓ :=
        neg_abs_le _
      _ ≤ (x - ℓ) / ℓ := hleft
  · calc
      (x - ℓ) / ℓ ≤ (B - ℓ) / ℓ := hright
      _ ≤ |(B - ℓ) / ℓ| := le_abs_self _
      _ ≤ max |(A - ℓ) / ℓ| |(B - ℓ) / ℓ| :=
        le_max_right _ _
def saddleFixedStripMajorant
    (ε ℓ H a : ℝ) (k m : ℕ) : ℝ :=
  ((1 + |beta ε|) *
      (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3) *
    ((2 : ℝ) ^ (k + (m + 3)) *
      Real.Gamma
        (a / 2 + ((k + (m + 3) : ℕ) : ℝ))) *
    Real.exp ((ℓ - a) * Real.log Real.pi / 2) *
    Real.exp
      (ℓ * saddleHorizontalShellVariation ε H)
theorem saddleShiftedLineMajorant_le_fixedStrip
    {ε ℓ a H : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hH : |(a - ℓ) / ℓ| ≤ H)
    (k m : ℕ) (hshift : 0 < a / 2 + (k : ℝ)) :
    saddleShiftedLineMajorant ε ℓ a k m ≤
      saddleFixedStripMajorant ε ℓ H a k m := by
  have hgammaarg :
      0 < a / 2 + ((k + (m + 3) : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    have hm : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hgamma :
      0 ≤ Real.Gamma
        (a / 2 + ((k + (m + 3) : ℕ) : ℝ)) :=
    (Real.Gamma_pos_of_pos hgammaarg).le
  unfold saddleShiftedLineMajorant saddleFixedStripMajorant
  gcongr
  exact saddleHorizontalShellVariation_mono
    hε horder (abs_nonneg _) hH
theorem saddleShiftedGamma_continuousOn
    {A B : ℝ} (k m : ℕ)
    (hshift : 0 < A / 2 + (k : ℝ)) :
    ContinuousOn
      (fun a : ℝ =>
        Real.Gamma
          (a / 2 + ((k + (m + 3) : ℕ) : ℝ)))
      (Set.Icc A B) := by
  have harg : ContinuousOn
      (fun a : ℝ =>
        a / 2 + ((k + (m + 3) : ℕ) : ℝ))
      (Set.Icc A B) := by
    fun_prop
  apply Real.differentiableOn_Gamma_Ioi.continuousOn.comp
    harg
  intro a ha
  change 0 < a / 2 + ((k + (m + 3) : ℕ) : ℝ)
  have ha' : A / 2 ≤ a / 2 := by
    linarith [ha.1]
  rw [Nat.cast_add]
  have hm : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  linarith
theorem saddleFixedStripMajorant_continuousOn
    {A B : ℝ} (ε ℓ H : ℝ) (k m : ℕ)
    (hshift : 0 < A / 2 + (k : ℝ)) :
    ContinuousOn
      (fun a : ℝ => saddleFixedStripMajorant ε ℓ H a k m)
      (Set.Icc A B) := by
  have hpoly : ContinuousOn
      (fun a : ℝ =>
        (1 + |beta ε|) *
          (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3)
      (Set.Icc A B) := by
    fun_prop
  have hgamma : ContinuousOn
      (fun a : ℝ =>
        (2 : ℝ) ^ (k + (m + 3)) *
          Real.Gamma
            (a / 2 + ((k + (m + 3) : ℕ) : ℝ)))
      (Set.Icc A B) :=
    continuousOn_const.mul
      (saddleShiftedGamma_continuousOn k m hshift)
  have hpi : ContinuousOn
      (fun a : ℝ =>
        Real.exp ((ℓ - a) * Real.log Real.pi / 2))
      (Set.Icc A B) := by
    fun_prop
  have hshell : ContinuousOn
      (fun _ : ℝ =>
        Real.exp
          (ℓ * saddleHorizontalShellVariation ε H))
      (Set.Icc A B) := continuousOn_const
  exact ((hpoly.mul hgamma).mul hpi).mul hshell
theorem plusSaddleMellinData_horizontalStrip_polynomial_bound
    {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {A B : ℝ} (hAB : A ≤ B) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| ^ m *
            ‖plusSaddleMellinData ε ℓ
              ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-(A / 2))
  have hshiftA : 0 < A / 2 + (k : ℝ) := by
    linarith
  let H : ℝ := saddleHorizontalStripHeight ℓ A B
  have hcont : ContinuousOn
      (fun a : ℝ => saddleFixedStripMajorant ε ℓ H a k m)
      (Set.Icc A B) :=
    saddleFixedStripMajorant_continuousOn
      ε ℓ H k m hshiftA
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont
  have hAmem : A ∈ Set.Icc A B := ⟨le_rfl, hAB⟩
  have hAnonneg :
      0 ≤ saddleFixedStripMajorant ε ℓ H A k m := by
    have hgammaarg :
        0 < A / 2 + ((k + (m + 3) : ℕ) : ℝ) := by
      rw [Nat.cast_add]
      have hm : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      linarith
    unfold saddleFixedStripMajorant
    positivity [Real.Gamma_pos_of_pos hgammaarg]
  refine ⟨C, hAnonneg.trans
    (hC (Set.mem_image_of_mem _ hAmem)), ?_⟩
  intro a ha t ht
  have hshifta : 0 < a / 2 + (k : ℝ) := by
    linarith [ha.1]
  calc
    |t| ^ m *
        ‖plusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      saddleShiftedLineMajorant ε ℓ a k m :=
        plusSaddleMellinData_shiftedLine_polynomial_bound
          hε hℓ horder a ht k m hshifta
    _ ≤ saddleFixedStripMajorant ε ℓ H a k m :=
      saddleShiftedLineMajorant_le_fixedStrip
        hε hℓ horder
        (saddleHorizontalStripHeight_bound hℓ ha)
        k m hshifta
    _ ≤ C := hC (Set.mem_image_of_mem _ ha)
theorem minusSaddleMellinData_horizontalStrip_polynomial_bound
    {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {A B : ℝ} (hAB : A ≤ B) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| ^ m *
            ‖minusSaddleMellinData ε ℓ
              ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-(A / 2))
  have hshiftA : 0 < A / 2 + (k : ℝ) := by
    linarith
  let H : ℝ := saddleHorizontalStripHeight ℓ A B
  have hcont : ContinuousOn
      (fun a : ℝ => saddleFixedStripMajorant ε ℓ H a k m)
      (Set.Icc A B) :=
    saddleFixedStripMajorant_continuousOn
      ε ℓ H k m hshiftA
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont
  have hAmem : A ∈ Set.Icc A B := ⟨le_rfl, hAB⟩
  have hAnonneg :
      0 ≤ saddleFixedStripMajorant ε ℓ H A k m := by
    have hgammaarg :
        0 < A / 2 + ((k + (m + 3) : ℕ) : ℝ) := by
      rw [Nat.cast_add]
      have hm : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      linarith
    unfold saddleFixedStripMajorant
    positivity [Real.Gamma_pos_of_pos hgammaarg]
  refine ⟨C, hAnonneg.trans
    (hC (Set.mem_image_of_mem _ hAmem)), ?_⟩
  intro a ha t ht
  have hshifta : 0 < a / 2 + (k : ℝ) := by
    linarith [ha.1]
  calc
    |t| ^ m *
        ‖minusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      saddleShiftedLineMajorant ε ℓ a k m :=
        minusSaddleMellinData_shiftedLine_polynomial_bound
          hε hℓ horder a ht k m hshifta
    _ ≤ saddleFixedStripMajorant ε ℓ H a k m :=
      saddleShiftedLineMajorant_le_fixedStrip
        hε hℓ horder
        (saddleHorizontalStripHeight_bound hℓ ha)
        k m hshifta
    _ ≤ C := hC (Set.mem_image_of_mem _ ha)
theorem saddleEnvelope_conj (ε ℓ t : ℝ) :
    starRingEnd ℂ (saddleEnvelope ε ℓ t) =
      saddleEnvelope ε ℓ (-t) := by
  have harg :
      (t : ℂ) / (ℓ : ℂ) = ((t / ℓ : ℝ) : ℂ) := by
    push_cast
    rfl
  have hneg :
      ((-t : ℝ) : ℂ) / (ℓ : ℂ) =
        -((t : ℂ) / (ℓ : ℂ)) := by
    push_cast
    ring
  have hphase :
      starRingEnd ℂ (mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ))) =
        mellinShellPhase ε (((-t : ℝ) : ℂ) / (ℓ : ℂ)) := by
    calc
      starRingEnd ℂ (mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ))) =
          mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ)) := by
            rw [harg, mellinShellPhase_real_conj]
      _ = mellinShellPhase ε (((-t : ℝ) : ℂ) / (ℓ : ℂ)) := by
            rw [hneg, mellinShellPhase_neg]
  unfold saddleEnvelope
  simp only [map_mul, ← Complex.exp_conj, ← Complex.Gamma_conj,
    map_div₀, map_sub, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  rw [hphase]
  push_cast
  congr 2 <;> congr 1 <;> ring
theorem norm_saddleShellExponential_le {ε ℓ : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (t : ℝ) :
    ‖Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε
          ((t : ℂ) / (ℓ : ℂ)))‖ ≤
      Real.exp (2 * |ℓ| * saddleShellTotalVariation ε) := by
  have harg :
      (t : ℂ) / (ℓ : ℂ) = ((t / ℓ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [harg, mellinShellPhase_ofReal, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  apply Real.exp_le_exp.mpr
  calc
    ℓ * realOscillatoryShellPhase ε (t / ℓ)
      ≤ |ℓ * realOscillatoryShellPhase ε (t / ℓ)| :=
          le_abs_self _
    _ = |ℓ| * |realOscillatoryShellPhase ε (t / ℓ)| :=
          abs_mul _ _
    _ ≤ |ℓ| * (2 * saddleShellTotalVariation ε) := by
          gcongr
          exact abs_realOscillatoryShellPhase_le hε horder (t / ℓ)
    _ = 2 * |ℓ| * saddleShellTotalVariation ε := by ring
theorem saddleEnvelope_vertical_polynomial_bound {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (t : ℝ) (k : ℕ) :
    |t| ^ k * ‖saddleEnvelope ε ℓ t‖ ≤
      (2 : ℝ) ^ k * Real.Gamma (ℓ / 2 + k) *
        Real.exp (2 * |ℓ| * saddleShellTotalVariation ε) := by
  let z : ℂ := ((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2
  have hz : 0 < z.re := by
    try dsimp [z]
    simpa using! half_pos hℓ
  have hgamma :
      (|t| / 2) ^ k * ‖Complex.Gamma z‖ ≤
        Real.Gamma (ℓ / 2 + k) := by
    simpa [z, abs_div] using!
      complexGamma_vertical_polynomial_bound hz k
  have hscaled :
      |t| ^ k * ‖Complex.Gamma z‖ ≤
        (2 : ℝ) ^ k * Real.Gamma (ℓ / 2 + k) := by
    calc
      |t| ^ k * ‖Complex.Gamma z‖ =
          (2 : ℝ) ^ k *
            ((|t| / 2) ^ k * ‖Complex.Gamma z‖) := by
              rw [div_pow]
              field_simp
      _ ≤ (2 : ℝ) ^ k * Real.Gamma (ℓ / 2 + k) := by
              gcongr
  have hunit :
      ‖Complex.exp
        (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ) / 2)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  calc
    |t| ^ k * ‖saddleEnvelope ε ℓ t‖ =
        (|t| ^ k * ‖Complex.Gamma z‖) *
          ‖Complex.exp ((ℓ : ℂ) *
            mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ)))‖ := by
            unfold saddleEnvelope
            rw [norm_mul, norm_mul, hunit]
            try dsimp [z]
            ring
    _ ≤ ((2 : ℝ) ^ k * Real.Gamma (ℓ / 2 + k)) *
          Real.exp (2 * |ℓ| * saddleShellTotalVariation ε) := by
            gcongr
            exact norm_saddleShellExponential_le hε horder t
theorem norm_plusPolynomial_scaled_le {ε ℓ t : ℝ}
    (hℓ : 0 < ℓ) (ht : 1 ≤ |t|) :
    ‖plusPolynomial ε ((t : ℂ) / (ℓ : ℂ))‖ ≤
      (1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3 := by
  have hnorm : ‖(t : ℂ) / (ℓ : ℂ)‖ = |t| / ℓ := by
    rw [norm_div]
    simp [abs_of_pos hℓ]
  have hlinear :
      1 + |t| / ℓ ≤ (1 + ℓ⁻¹) * |t| := by
    rw [inv_eq_one_div]
    field_simp [hℓ.ne']
    nlinarith
  calc
    ‖plusPolynomial ε ((t : ℂ) / (ℓ : ℂ))‖
      ≤ (1 + |beta ε|) *
        (1 + ‖(t : ℂ) / (ℓ : ℂ)‖) ^ 3 :=
          norm_plusPolynomial_le ε _
    _ = (1 + |beta ε|) * (1 + |t| / ℓ) ^ 3 := by
          rw [hnorm]
    _ ≤ (1 + |beta ε|) *
        ((1 + ℓ⁻¹) * |t|) ^ 3 := by
          gcongr
    _ = (1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3 := by
          ring
theorem norm_minusPolynomial_scaled_le {ε ℓ t : ℝ}
    (hℓ : 0 < ℓ) (ht : 1 ≤ |t|) :
    ‖minusPolynomial ε ((t : ℂ) / (ℓ : ℂ))‖ ≤
      (1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3 := by
  have hnorm : ‖(t : ℂ) / (ℓ : ℂ)‖ = |t| / ℓ := by
    rw [norm_div]
    simp [abs_of_pos hℓ]
  have hlinear :
      1 + |t| / ℓ ≤ (1 + ℓ⁻¹) * |t| := by
    rw [inv_eq_one_div]
    field_simp [hℓ.ne']
    nlinarith
  calc
    ‖minusPolynomial ε ((t : ℂ) / (ℓ : ℂ))‖
      ≤ (1 + |beta ε|) *
        (1 + ‖(t : ℂ) / (ℓ : ℂ)‖) ^ 3 :=
          norm_minusPolynomial_le ε _
    _ = (1 + |beta ε|) * (1 + |t| / ℓ) ^ 3 := by
          rw [hnorm]
    _ ≤ (1 + |beta ε|) *
        ((1 + ℓ⁻¹) * |t|) ^ 3 := by
          gcongr
    _ = (1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3 := by
          ring
theorem plusSaddleSpectrum_vertical_polynomial_bound {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {t : ℝ} (ht : 1 ≤ |t|) (k : ℕ) :
    |t| ^ k * ‖plusSaddleSpectrum ε ℓ t‖ ≤
      ((1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3) *
        ((2 : ℝ) ^ (k + 3) *
          Real.Gamma (ℓ / 2 + (k + 3)) *
          Real.exp (2 * |ℓ| * saddleShellTotalVariation ε)) := by
  have hpoly := norm_plusPolynomial_scaled_le
    (ε := ε) hℓ ht
  have hgamma := saddleEnvelope_vertical_polynomial_bound
    hε hℓ horder t (k + 3)
  calc
    |t| ^ k * ‖plusSaddleSpectrum ε ℓ t‖ =
        |t| ^ k * ‖saddleEnvelope ε ℓ t‖ *
          ‖plusPolynomial ε ((t : ℂ) / (ℓ : ℂ))‖ := by
            unfold plusSaddleSpectrum
            rw [norm_mul]
            ring
    _ ≤ |t| ^ k * ‖saddleEnvelope ε ℓ t‖ *
          ((1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3) := by
            gcongr
    _ = ((1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3) *
          (|t| ^ (k + 3) * ‖saddleEnvelope ε ℓ t‖) := by
            rw [pow_add]
            ring
    _ ≤ ((1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3) *
        ((2 : ℝ) ^ (k + 3) *
          Real.Gamma (ℓ / 2 + (k + 3)) *
          Real.exp (2 * |ℓ| * saddleShellTotalVariation ε)) := by
            simpa only [Nat.cast_add, Nat.cast_ofNat] using!
              (mul_le_mul_of_nonneg_left hgamma
                (show 0 ≤ (1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3 by
                  positivity))
theorem minusSaddleSpectrum_vertical_polynomial_bound {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {t : ℝ} (ht : 1 ≤ |t|) (k : ℕ) :
    |t| ^ k * ‖minusSaddleSpectrum ε ℓ t‖ ≤
      ((1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3) *
        ((2 : ℝ) ^ (k + 3) *
          Real.Gamma (ℓ / 2 + (k + 3)) *
          Real.exp (2 * |ℓ| * saddleShellTotalVariation ε)) := by
  have hpoly := norm_minusPolynomial_scaled_le
    (ε := ε) hℓ ht
  have hgamma := saddleEnvelope_vertical_polynomial_bound
    hε hℓ horder t (k + 3)
  calc
    |t| ^ k * ‖minusSaddleSpectrum ε ℓ t‖ =
        |t| ^ k * ‖saddleEnvelope ε ℓ t‖ *
          ‖minusPolynomial ε ((t : ℂ) / (ℓ : ℂ))‖ := by
            unfold minusSaddleSpectrum
            rw [norm_mul]
            ring
    _ ≤ |t| ^ k * ‖saddleEnvelope ε ℓ t‖ *
          ((1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3) := by
            gcongr
    _ = ((1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3) *
          (|t| ^ (k + 3) * ‖saddleEnvelope ε ℓ t‖) := by
            rw [pow_add]
            ring
    _ ≤ ((1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3) *
        ((2 : ℝ) ^ (k + 3) *
          Real.Gamma (ℓ / 2 + (k + 3)) *
          Real.exp (2 * |ℓ| * saddleShellTotalVariation ε)) := by
            simpa only [Nat.cast_add, Nat.cast_ofNat] using!
              (mul_le_mul_of_nonneg_left hgamma
                (show 0 ≤ (1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3 by
                  positivity))
theorem integrable_of_continuous_polynomial_decay
    {F : ℝ → ℂ} (hF : Continuous F)
    (hdecay : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 1 ≤ |t| → |t| ^ j * ‖F t‖ ≤ C)
    (k : ℕ) : Integrable (fun t : ℝ => (t : ℂ) ^ k * F t) := by
  have hcompact : IsCompact (Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc
  obtain ⟨M, hM⟩ := hcompact.bddAbove_image hF.norm.continuousOn
  have hzero : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> norm_num
  have hMnonneg : 0 ≤ M :=
    (norm_nonneg (F 0)).trans
      (hM (Set.mem_image_of_mem (fun t : ℝ => ‖F t‖) hzero))
  obtain ⟨C, hC, htail⟩ := hdecay (k + 2)
  have hmajor : Integrable (fun t : ℝ =>
      (2 * (M + C)) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (2 * (M + C))
  have hmoment : Continuous (fun t : ℝ =>
      (t : ℂ) ^ k * F t) := by
    exact ((Complex.continuous_ofReal.comp continuous_id).pow k).mul hF
  apply hmajor.mono' hmoment.aestronglyMeasurable
  filter_upwards [] with t
  have hden : 0 < 1 + t ^ 2 := by positivity
  change ‖(t : ℂ) ^ k * F t‖ ≤
    2 * (M + C) / (1 + t ^ 2)
  apply (le_div_iff₀ hden).2
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  by_cases ht : |t| ≤ (1 : ℝ)
  · have htmem : t ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · linarith [neg_abs_le t]
      · linarith [le_abs_self t]
    have hnorm : ‖F t‖ ≤ M :=
      hM (Set.mem_image_of_mem (fun u : ℝ => ‖F u‖) htmem)
    have hpow : |t| ^ k ≤ 1 :=
      pow_le_one₀ (abs_nonneg t) ht
    have hsquare : t ^ 2 ≤ 1 := by
      have habs : |t| ^ 2 ≤ (1 : ℝ) := by
        nlinarith [mul_nonneg (abs_nonneg t)
          (sub_nonneg.mpr ht)]
      simpa only [sq_abs] using! habs
    have hweighted : |t| ^ k * ‖F t‖ ≤ M := by
      calc
        |t| ^ k * ‖F t‖ ≤ 1 * ‖F t‖ := by
          gcongr
        _ = ‖F t‖ := one_mul _
        _ ≤ M := hnorm
    calc
      (|t| ^ k * ‖F t‖) * (1 + t ^ 2)
        ≤ M * 2 :=
          mul_le_mul hweighted (by linarith)
            (by positivity) hMnonneg
      _ ≤ 2 * (M + C) := by nlinarith
  · have htlarge : 1 ≤ |t| :=
      (lt_of_not_ge ht).le
    have hsquare : (1 : ℝ) ≤ t ^ 2 := by
      have habs : (1 : ℝ) ≤ |t| ^ 2 := by
        nlinarith [mul_nonneg (abs_nonneg t)
          (sub_nonneg.mpr htlarge)]
      simpa only [sq_abs] using! habs
    calc
      (|t| ^ k * ‖F t‖) * (1 + t ^ 2)
        ≤ (|t| ^ k * ‖F t‖) * (2 * t ^ 2) := by
          gcongr
          linarith
      _ = 2 * (|t| ^ (k + 2) * ‖F t‖) := by
          rw [pow_add, sq_abs]
          ring
      _ ≤ 2 * C := by
          gcongr
          exact htail t htlarge
      _ ≤ 2 * (M + C) := by
          nlinarith
theorem saddleShiftedLine_ne_pole
    {a : ℝ}
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (t : ℝ) (n : ℕ) :
    (a : ℂ) + (t : ℂ) * Complex.I ≠
      (-((2 * n : ℕ) : ℂ)) := by
  intro heq
  apply hpole n
  have hre := congrArg Complex.re heq
  simpa using! hre
theorem plusSaddleMellinData_shiftedLine_continuous
    {ε a : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ)) :
    Continuous (fun t : ℝ =>
      plusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hcomplex :
      DifferentiableAt ℂ (plusSaddleMellinData ε ℓ)
        ((a : ℂ) + (t : ℂ) * Complex.I) :=
    plusSaddleMellinData_differentiableAt_of_not_pole
      hε horder ℓ (saddleShiftedLine_ne_pole hpole t)
  have hline : ContinuousAt
      (fun u : ℝ => (a : ℂ) + (u : ℂ) * Complex.I) t := by
    fun_prop
  simpa [Function.comp_def] using!
    hcomplex.continuousAt.comp_of_eq hline (by rfl)
theorem minusSaddleMellinData_shiftedLine_continuous
    {ε a : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ : ℝ)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ)) :
    Continuous (fun t : ℝ =>
      minusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hcomplex :
      DifferentiableAt ℂ (minusSaddleMellinData ε ℓ)
        ((a : ℂ) + (t : ℂ) * Complex.I) :=
    minusSaddleMellinData_differentiableAt_of_not_pole
      hε horder ℓ (saddleShiftedLine_ne_pole hpole t)
  have hline : ContinuousAt
      (fun u : ℝ => (a : ℂ) + (u : ℂ) * Complex.I) t := by
    fun_prop
  simpa [Function.comp_def] using!
    hcomplex.continuousAt.comp_of_eq hline (by rfl)
theorem plusSaddleMellinData_shiftedLine_moment_integrable
    {ε ℓ a : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (j : ℕ) :
    Integrable (fun t : ℝ =>
      (t : ℂ) ^ j * plusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  apply integrable_of_continuous_polynomial_decay
    (plusSaddleMellinData_shiftedLine_continuous
      hε horder ℓ hpole)
  intro m
  obtain ⟨k, hk⟩ := exists_nat_gt (-(a / 2))
  have hshift : 0 < a / 2 + (k : ℝ) := by
    linarith
  refine ⟨saddleShiftedLineMajorant ε ℓ a k m,
    saddleShiftedLineMajorant_nonneg hℓ k m hshift, ?_⟩
  intro t ht
  exact plusSaddleMellinData_shiftedLine_polynomial_bound
    hε hℓ horder a ht k m hshift
theorem minusSaddleMellinData_shiftedLine_moment_integrable
    {ε ℓ a : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (j : ℕ) :
    Integrable (fun t : ℝ =>
      (t : ℂ) ^ j * minusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  apply integrable_of_continuous_polynomial_decay
    (minusSaddleMellinData_shiftedLine_continuous
      hε horder ℓ hpole)
  intro m
  obtain ⟨k, hk⟩ := exists_nat_gt (-(a / 2))
  have hshift : 0 < a / 2 + (k : ℝ) := by
    linarith
  refine ⟨saddleShiftedLineMajorant ε ℓ a k m,
    saddleShiftedLineMajorant_nonneg hℓ k m hshift, ?_⟩
  intro t ht
  exact minusSaddleMellinData_shiftedLine_polynomial_bound
    hε hℓ horder a ht k m hshift
theorem saddleMellinInversePower_shiftedLine_norm
    {r : ℝ} (hr : 0 < r) (a t : ℝ) :
    ‖saddleMellinInversePower r
      ((a : ℂ) + (t : ℂ) * Complex.I)‖ =
      r ^ (-a) := by
  unfold saddleMellinInversePower
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp
theorem saddleMellinInversePower_shiftedLine_continuous
    {r : ℝ} (hr : 0 < r) (a : ℝ) :
    Continuous (fun t : ℝ =>
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  exact (saddleMellinInversePower_differentiable hr).continuous.comp
    (by fun_prop)
theorem plusSaddleMellinData_shiftedLine_weighted_moment_integrable
    {ε ℓ a r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (hr : 0 < r) (j : ℕ) :
    Integrable (fun t : ℝ =>
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        ((t : ℂ) ^ j * plusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I))) := by
  have hmoment :=
    plusSaddleMellinData_shiftedLine_moment_integrable
      hε hℓ horder hpole j
  have hweight :=
    saddleMellinInversePower_shiftedLine_continuous hr a
  apply (hmoment.norm.const_mul (r ^ (-a))).mono'
  · exact hweight.aestronglyMeasurable.mul
      hmoment.aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_mul, saddleMellinInversePower_shiftedLine_norm hr a t]
theorem minusSaddleMellinData_shiftedLine_weighted_moment_integrable
    {ε ℓ a r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (hr : 0 < r) (j : ℕ) :
    Integrable (fun t : ℝ =>
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        ((t : ℂ) ^ j * minusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I))) := by
  have hmoment :=
    minusSaddleMellinData_shiftedLine_moment_integrable
      hε hℓ horder hpole j
  have hweight :=
    saddleMellinInversePower_shiftedLine_continuous hr a
  apply (hmoment.norm.const_mul (r ^ (-a))).mono'
  · exact hweight.aestronglyMeasurable.mul
      hmoment.aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_mul, saddleMellinInversePower_shiftedLine_norm hr a t]
theorem plusSaddleMellinData_shiftedLine_weighted_integrable
    {ε ℓ a r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (hr : 0 < r) :
    Integrable (fun t : ℝ =>
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  simpa using!
    plusSaddleMellinData_shiftedLine_weighted_moment_integrable
      hε hℓ horder hpole hr 0
theorem minusSaddleMellinData_shiftedLine_weighted_integrable
    {ε ℓ a r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (hr : 0 < r) :
    Integrable (fun t : ℝ =>
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  simpa using!
    minusSaddleMellinData_shiftedLine_weighted_moment_integrable
      hε hℓ horder hpole hr 0
theorem saddleGaussianPoleRepresentative_shiftedLine_norm
    (a t : ℝ) (n : ℕ) :
    ‖saddleGaussianPoleRepresentative n
      ((a : ℂ) + (t : ℂ) * Complex.I)‖ =
      Real.exp
        ((a + ((2 * n : ℕ) : ℝ)) ^ 2 - t ^ 2) /
        ‖(a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)‖ := by
  unfold saddleGaussianPoleRepresentative
  rw [norm_div, Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re, Complex.mul_im]
theorem saddleGaussianPoleRepresentative_shiftedLine_continuous
    {a : ℝ} (n : ℕ)
    (ha : a ≠ -((2 * n : ℕ) : ℝ)) :
    Continuous (fun t : ℝ =>
      saddleGaussianPoleRepresentative n
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hline : Continuous
      (fun t : ℝ =>
        (a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)) := by
    fun_prop
  have hnonzero : ∀ t : ℝ,
      (a : ℂ) + (t : ℂ) * Complex.I +
        ((2 * n : ℕ) : ℂ) ≠ 0 := by
    intro t hzero
    apply ha
    have hre := congrArg Complex.re hzero
    norm_num [Complex.mul_re] at hre
    push_cast
    linarith
  unfold saddleGaussianPoleRepresentative
  exact (Complex.continuous_exp.comp (hline.pow 2)).div
    hline hnonzero
theorem saddleGaussianPoleRepresentative_shiftedLine_bound
    {a : ℝ} (n : ℕ)
    (ha : a ≠ -((2 * n : ℕ) : ℝ)) (t : ℝ) :
    ‖saddleGaussianPoleRepresentative n
      ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2) /
          |a + ((2 * n : ℕ) : ℝ)|) *
        Real.exp (-t ^ 2) := by
  have hreal : a + ((2 * n : ℕ) : ℝ) ≠ 0 := by
    intro hzero
    apply ha
    linarith
  have habs : 0 < |a + ((2 * n : ℕ) : ℝ)| :=
    abs_pos.mpr hreal
  have hden :
      |a + ((2 * n : ℕ) : ℝ)| ≤
        ‖(a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)‖ := by
    simpa [Complex.mul_re] using!
      (Complex.abs_re_le_norm
        ((a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)))
  rw [saddleGaussianPoleRepresentative_shiftedLine_norm,
    sub_eq_add_neg, Real.exp_add]
  calc
    Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2) *
        Real.exp (-t ^ 2) /
        ‖(a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)‖ ≤
      Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2) *
        Real.exp (-t ^ 2) /
          |a + ((2 * n : ℕ) : ℝ)| := by
        gcongr
    _ = (Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2) /
          |a + ((2 * n : ℕ) : ℝ)|) *
        Real.exp (-t ^ 2) := by
          ring
theorem saddleGaussianPoleRepresentative_shiftedLine_integrable
    {a : ℝ} (n : ℕ)
    (ha : a ≠ -((2 * n : ℕ) : ℝ)) :
    Integrable (fun t : ℝ =>
      saddleGaussianPoleRepresentative n
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hgaussian : Integrable
      (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simpa using!
      (integrable_exp_neg_mul_sq (b := (1 : ℝ))
        (by norm_num : (0 : ℝ) < 1))
  let C : ℝ :=
    Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2) /
      |a + ((2 * n : ℕ) : ℝ)|
  apply (hgaussian.const_mul C).mono'
  · exact (saddleGaussianPoleRepresentative_shiftedLine_continuous
      n ha).aestronglyMeasurable
  · filter_upwards [] with t
    exact saddleGaussianPoleRepresentative_shiftedLine_bound
      n ha t
theorem saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable
    {a r : ℝ} (n : ℕ)
    (ha : a ≠ -((2 * n : ℕ) : ℝ))
    (hr : 0 < r) :
    Integrable (fun t : ℝ =>
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hrepresentative :=
    saddleGaussianPoleRepresentative_shiftedLine_integrable
      n ha
  have hweight :=
    saddleMellinInversePower_shiftedLine_continuous hr a
  apply (hrepresentative.norm.const_mul (r ^ (-a))).mono'
  · exact hweight.aestronglyMeasurable.mul
      hrepresentative.aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_mul, saddleMellinInversePower_shiftedLine_norm hr a t]
theorem plusSaddleFiniteRapidContourIntegrand_shiftedLine_integrable
    {ε ℓ a r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < a)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (hr : 0 < r) :
    Integrable (fun t : ℝ =>
      plusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hdata :=
    plusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder hpole hr
  have hsum : Integrable (fun t : ℝ =>
      ∑ n ∈ Finset.range (N + 1),
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          (plusSaddlePoleResidue ε ℓ n *
            saddleGaussianPoleRepresentative n
              ((a : ℂ) + (t : ℂ) * Complex.I))) := by
    apply integrable_finsetSum
    intro n _
    have hterm :=
      (saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable
        n (hpole n) hr).const_mul
          (plusSaddlePoleResidue ε ℓ n)
    exact hterm.congr
      (Filter.Eventually.of_forall (fun t => by ring))
  apply (hdata.sub hsum).congr
  filter_upwards [] with t
  have hz :
      (a : ℂ) + (t : ℂ) * Complex.I ∈
        saddleFinitePoleHalfPlane N := by
    change
      -(2 * ((N : ℝ) + 1)) <
        ((a : ℂ) + (t : ℂ) * Complex.I).re
    simpa [Complex.mul_re] using! hhalf
  unfold plusSaddleFiniteRapidContourIntegrand
  rw [plusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
    hε horder ℓ N hz (saddleShiftedLine_ne_pole hpole t)]
  unfold plusSaddleFiniteRapidPoleSubtraction
  rw [mul_sub, Finset.mul_sum]
  rfl
theorem minusSaddleFiniteRapidContourIntegrand_shiftedLine_integrable
    {ε ℓ a r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < a)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (hr : 0 < r) :
    Integrable (fun t : ℝ =>
      minusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hdata :=
    minusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder hpole hr
  have hsum : Integrable (fun t : ℝ =>
      ∑ n ∈ Finset.range (N + 1),
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          (minusSaddlePoleResidue ε ℓ n *
            saddleGaussianPoleRepresentative n
              ((a : ℂ) + (t : ℂ) * Complex.I))) := by
    apply integrable_finsetSum
    intro n _
    have hterm :=
      (saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable
        n (hpole n) hr).const_mul
          (minusSaddlePoleResidue ε ℓ n)
    exact hterm.congr
      (Filter.Eventually.of_forall (fun t => by ring))
  apply (hdata.sub hsum).congr
  filter_upwards [] with t
  have hz :
      (a : ℂ) + (t : ℂ) * Complex.I ∈
        saddleFinitePoleHalfPlane N := by
    change
      -(2 * ((N : ℝ) + 1)) <
        ((a : ℂ) + (t : ℂ) * Complex.I).re
    simpa [Complex.mul_re] using! hhalf
  unfold minusSaddleFiniteRapidContourIntegrand
  rw [minusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
    hε horder ℓ N hz (saddleShiftedLine_ne_pole hpole t)]
  unfold minusSaddleFiniteRapidPoleSubtraction
  rw [mul_sub, Finset.mul_sum]
  rfl
theorem saddleMellinInversePower_horizontalStrip_bounded
    {r A B : ℝ} (hr : 0 < r) (hAB : A ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        ‖saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  have hpower : Continuous
      (fun a : ℝ => r ^ (-a)) :=
    (Real.continuous_const_rpow hr.ne').comp
      (by fun_prop)
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.bddAbove_image hpower.continuousOn
  have hAmem : A ∈ Set.Icc A B := ⟨le_rfl, hAB⟩
  have hnonneg : 0 ≤ C :=
    (Real.rpow_nonneg hr.le (-A)).trans
      (hC (Set.mem_image_of_mem _ hAmem))
  refine ⟨C, hnonneg, ?_⟩
  intro a ha t
  rw [saddleMellinInversePower_shiftedLine_norm hr a t]
  exact hC (Set.mem_image_of_mem _ ha)
theorem plusSaddleMellinData_weighted_horizontalStrip_polynomial_bound
    {ε ℓ r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r)
    {A B : ℝ} (hAB : A ≤ B) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| ^ m *
            ‖saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              plusSaddleMellinData ε ℓ
                ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨R, hR, hweight⟩ :=
    saddleMellinInversePower_horizontalStrip_bounded hr hAB
  obtain ⟨C, hC, hdata⟩ :=
    plusSaddleMellinData_horizontalStrip_polynomial_bound
      hε hℓ horder hAB m
  refine ⟨R * C, mul_nonneg hR hC, ?_⟩
  intro a ha t ht
  calc
    |t| ^ m *
        ‖saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          plusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)‖ =
      ‖saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I)‖ *
        (|t| ^ m *
          ‖plusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)‖) := by
        rw [norm_mul]
        ring
    _ ≤ R * C := by
      gcongr
      · exact hweight a ha t
      · exact hdata a ha t ht
theorem minusSaddleMellinData_weighted_horizontalStrip_polynomial_bound
    {ε ℓ r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r)
    {A B : ℝ} (hAB : A ≤ B) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| ^ m *
            ‖saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              minusSaddleMellinData ε ℓ
                ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨R, hR, hweight⟩ :=
    saddleMellinInversePower_horizontalStrip_bounded hr hAB
  obtain ⟨C, hC, hdata⟩ :=
    minusSaddleMellinData_horizontalStrip_polynomial_bound
      hε hℓ horder hAB m
  refine ⟨R * C, mul_nonneg hR hC, ?_⟩
  intro a ha t ht
  calc
    |t| ^ m *
        ‖saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          minusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)‖ =
      ‖saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I)‖ *
        (|t| ^ m *
          ‖minusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)‖) := by
        rw [norm_mul]
        ring
    _ ≤ R * C := by
      gcongr
      · exact hweight a ha t
      · exact hdata a ha t ht
theorem saddleHorizontalIntegral_tendsto_zero
    {F : ℂ → ℂ} {A B C : ℝ}
    (hAB : A ≤ B)
    (hdecay : ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
      1 ≤ |t| →
        |t| * ‖F ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C)
    (s : ℝ) (hs : |s| = 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          F ((a : ℂ) + ((s * T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
  have hdiv : Tendsto
      (fun T : ℝ => C / T)
      Filter.atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hmajor : Tendsto
      (fun T : ℝ => C / T * |B - A|)
      Filter.atTop (𝓝 0) := by
    simpa using! hdiv.mul_const |B - A|
  apply squeeze_zero_norm' (a := fun T : ℝ =>
    C / T * |B - A|) ?_ hmajor
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro a ha
  rw [uIoc_of_le hAB] at ha
  have ha' : a ∈ Set.Icc A B := ⟨ha.1.le, ha.2⟩
  have habs : |s * T| = T := by
    rw [abs_mul, hs, one_mul, abs_of_nonneg hTpos.le]
  have htail := hdecay a ha' (s * T) (by rw [habs]; exact hT)
  rw [habs] at htail
  apply (le_div_iff₀ hTpos).2
  simpa [mul_comm] using! htail
theorem plusSaddleMellinData_weighted_horizontalIntegral_tendsto_zero
    {ε ℓ r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r)
    {A B : ℝ} (hAB : A ≤ B)
    (s : ℝ) (hs : |s| = 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleMellinInversePower r
            ((a : ℂ) + ((s * T : ℝ) : ℂ) * Complex.I) *
            plusSaddleMellinData ε ℓ
              ((a : ℂ) + ((s * T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    plusSaddleMellinData_weighted_horizontalStrip_polynomial_bound
      hε hℓ horder hr hAB 1
  apply saddleHorizontalIntegral_tendsto_zero
    (F := fun z : ℂ =>
      saddleMellinInversePower r z *
        plusSaddleMellinData ε ℓ z)
    hAB (C := C) ?_ s hs
  simpa using! hbound
theorem minusSaddleMellinData_weighted_horizontalIntegral_tendsto_zero
    {ε ℓ r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r)
    {A B : ℝ} (hAB : A ≤ B)
    (s : ℝ) (hs : |s| = 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleMellinInversePower r
            ((a : ℂ) + ((s * T : ℝ) : ℂ) * Complex.I) *
            minusSaddleMellinData ε ℓ
              ((a : ℂ) + ((s * T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    minusSaddleMellinData_weighted_horizontalStrip_polynomial_bound
      hε hℓ horder hr hAB 1
  apply saddleHorizontalIntegral_tendsto_zero
    (F := fun z : ℂ =>
      saddleMellinInversePower r z *
        minusSaddleMellinData ε ℓ z)
    hAB (C := C) ?_ s hs
  simpa using! hbound
theorem saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound
    {r A B : ℝ} (hr : 0 < r) (hAB : A ≤ B)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| *
            ‖saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  have hpower : Continuous
      (fun a : ℝ => r ^ (-a)) :=
    (Real.continuous_const_rpow hr.ne').comp
      (by fun_prop)
  have hgaussian : Continuous
      (fun a : ℝ =>
        Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2)) := by
    fun_prop
  have hcoefficient : Continuous
      (fun a : ℝ =>
        r ^ (-a) *
          Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2)) :=
    hpower.mul hgaussian
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.bddAbove_image
      hcoefficient.continuousOn
  have hAmem : A ∈ Set.Icc A B := ⟨le_rfl, hAB⟩
  have hnonneg : 0 ≤ C :=
    (show 0 ≤ r ^ (-A) *
      Real.exp ((A + ((2 * n : ℕ) : ℝ)) ^ 2) by
        positivity).trans
          (hC (Set.mem_image_of_mem _ hAmem))
  refine ⟨C, hnonneg, ?_⟩
  intro a ha t ht
  have hden :
      |t| ≤
        ‖(a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)‖ := by
    simpa [Complex.mul_im] using!
      (Complex.abs_im_le_norm
        ((a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)))
  have hdenpos :
      0 < ‖(a : ℂ) + (t : ℂ) * Complex.I +
        ((2 * n : ℕ) : ℂ)‖ :=
    (lt_of_lt_of_le zero_lt_one ht).trans_le hden
  have hfrac :
      |t| /
        ‖(a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)‖ ≤ 1 :=
    (div_le_one hdenpos).2 hden
  have hexp : Real.exp (-t ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (sq_nonneg t))
  rw [norm_mul,
    saddleMellinInversePower_shiftedLine_norm hr a t,
    saddleGaussianPoleRepresentative_shiftedLine_norm,
    sub_eq_add_neg, Real.exp_add]
  calc
    |t| *
        (r ^ (-a) *
          (Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2) *
            Real.exp (-t ^ 2) /
            ‖(a : ℂ) + (t : ℂ) * Complex.I +
              ((2 * n : ℕ) : ℂ)‖)) =
      (r ^ (-a) *
        Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2)) *
        (Real.exp (-t ^ 2) *
          (|t| /
            ‖(a : ℂ) + (t : ℂ) * Complex.I +
              ((2 * n : ℕ) : ℂ)‖)) := by
        ring
    _ ≤ (r ^ (-a) *
        Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2)) * 1 := by
      apply mul_le_mul_of_nonneg_left
        (mul_le_one₀ hexp
          (div_nonneg (abs_nonneg t) (norm_nonneg _)) hfrac)
      positivity
    _ = r ^ (-a) *
        Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2) :=
      mul_one _
    _ ≤ C := hC (Set.mem_image_of_mem _ ha)
theorem saddleFiniteGaussianPoleWeighted_horizontalStrip_bound
    {r A B : ℝ} (hr : 0 < r) (hAB : A ≤ B)
    (c : ℕ → ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| *
            ‖saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              (∑ n ∈ Finset.range (N + 1),
                c n * saddleGaussianPoleRepresentative n
                  ((a : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C := by
  choose G hG hbound using
    (fun n : ℕ =>
      saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound
        hr hAB n)
  let C : ℝ :=
    ∑ n ∈ Finset.range (N + 1), ‖c n‖ * G n
  have hC : 0 ≤ C := by
    unfold C
    exact Finset.sum_nonneg
      (fun n _ => mul_nonneg (norm_nonneg _) (hG n))
  refine ⟨C, hC, ?_⟩
  intro a ha t ht
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  change
    |t| *
      ‖saddleMellinInversePower r z *
        (∑ n ∈ Finset.range (N + 1),
          c n * saddleGaussianPoleRepresentative n z)‖ ≤ C
  calc
    |t| *
        ‖saddleMellinInversePower r z *
          (∑ n ∈ Finset.range (N + 1),
            c n * saddleGaussianPoleRepresentative n z)‖ =
      |t| *
        ‖∑ n ∈ Finset.range (N + 1),
          saddleMellinInversePower r z *
            (c n * saddleGaussianPoleRepresentative n z)‖ := by
        rw [Finset.mul_sum]
    _ ≤ |t| *
        ∑ n ∈ Finset.range (N + 1),
          ‖saddleMellinInversePower r z *
            (c n * saddleGaussianPoleRepresentative n z)‖ := by
        gcongr
        exact norm_sum_le _ _
    _ = ∑ n ∈ Finset.range (N + 1),
          ‖c n‖ *
            (|t| *
              ‖saddleMellinInversePower r z *
                saddleGaussianPoleRepresentative n z‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        rw [norm_mul, norm_mul, norm_mul]
        ring
    _ ≤ ∑ n ∈ Finset.range (N + 1),
          ‖c n‖ * G n := by
        apply Finset.sum_le_sum
        intro n _
        exact mul_le_mul_of_nonneg_left
          (by simpa [z] using! hbound n a ha t ht)
          (norm_nonneg _)
    _ = C := rfl
theorem saddleNonzeroFrequency_ne_pole
    (a : ℝ) {t : ℝ} (ht : t ≠ 0) (n : ℕ) :
    (a : ℂ) + (t : ℂ) * Complex.I ≠
      (-((2 * n : ℕ) : ℂ)) := by
  intro heq
  have him := congrArg Complex.im heq
  norm_num [Complex.mul_im] at him
  exact ht him
theorem plusSaddleFiniteRapidContourIntegrand_horizontalStrip_bound
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| *
            ‖plusSaddleFiniteRapidContourIntegrand ε ℓ N r
              ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨D, hD, hdata⟩ :=
    plusSaddleMellinData_weighted_horizontalStrip_polynomial_bound
      hε hℓ horder hr hAB 1
  obtain ⟨G, hG, hgaussian⟩ :=
    saddleFiniteGaussianPoleWeighted_horizontalStrip_bound
      hr hAB (plusSaddlePoleResidue ε ℓ) N
  refine ⟨D + G, add_nonneg hD hG, ?_⟩
  intro a ha t ht
  have htne : t ≠ 0 := by
    intro hzero
    norm_num [hzero] at ht
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  have hz : z ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < z.re
    try dsimp [z]
    simpa [Complex.mul_re] using! hhalf.trans_le ha.1
  have hpoles : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ)) := by
    intro n
    exact saddleNonzeroFrequency_ne_pole a htne n
  change
    |t| *
      ‖plusSaddleFiniteRapidContourIntegrand ε ℓ N r z‖ ≤
        D + G
  unfold plusSaddleFiniteRapidContourIntegrand
  rw [plusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
    hε horder ℓ N hz hpoles]
  unfold plusSaddleFiniteRapidPoleSubtraction
  rw [mul_sub]
  calc
    |t| *
        ‖saddleMellinInversePower r z *
            plusSaddleMellinData ε ℓ z -
          saddleMellinInversePower r z *
            (∑ n ∈ Finset.range (N + 1),
              plusSaddlePoleResidue ε ℓ n *
                saddleGaussianPoleRepresentative n z)‖ ≤
      |t| *
        (‖saddleMellinInversePower r z *
            plusSaddleMellinData ε ℓ z‖ +
          ‖saddleMellinInversePower r z *
            (∑ n ∈ Finset.range (N + 1),
              plusSaddlePoleResidue ε ℓ n *
                saddleGaussianPoleRepresentative n z)‖) := by
        gcongr
        exact norm_sub_le _ _
    _ = |t| *
          ‖saddleMellinInversePower r z *
            plusSaddleMellinData ε ℓ z‖ +
        |t| *
          ‖saddleMellinInversePower r z *
            (∑ n ∈ Finset.range (N + 1),
              plusSaddlePoleResidue ε ℓ n *
                saddleGaussianPoleRepresentative n z)‖ := by
        ring
    _ ≤ D + G := by
      apply add_le_add
      · simpa [z] using! hdata a ha t ht
      · simpa [z] using! hgaussian a ha t ht
theorem minusSaddleFiniteRapidContourIntegrand_horizontalStrip_bound
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| *
            ‖minusSaddleFiniteRapidContourIntegrand ε ℓ N r
              ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨D, hD, hdata⟩ :=
    minusSaddleMellinData_weighted_horizontalStrip_polynomial_bound
      hε hℓ horder hr hAB 1
  obtain ⟨G, hG, hgaussian⟩ :=
    saddleFiniteGaussianPoleWeighted_horizontalStrip_bound
      hr hAB (minusSaddlePoleResidue ε ℓ) N
  refine ⟨D + G, add_nonneg hD hG, ?_⟩
  intro a ha t ht
  have htne : t ≠ 0 := by
    intro hzero
    norm_num [hzero] at ht
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  have hz : z ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < z.re
    try dsimp [z]
    simpa [Complex.mul_re] using! hhalf.trans_le ha.1
  have hpoles : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ)) := by
    intro n
    exact saddleNonzeroFrequency_ne_pole a htne n
  change
    |t| *
      ‖minusSaddleFiniteRapidContourIntegrand ε ℓ N r z‖ ≤
        D + G
  unfold minusSaddleFiniteRapidContourIntegrand
  rw [minusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
    hε horder ℓ N hz hpoles]
  unfold minusSaddleFiniteRapidPoleSubtraction
  rw [mul_sub]
  calc
    |t| *
        ‖saddleMellinInversePower r z *
            minusSaddleMellinData ε ℓ z -
          saddleMellinInversePower r z *
            (∑ n ∈ Finset.range (N + 1),
              minusSaddlePoleResidue ε ℓ n *
                saddleGaussianPoleRepresentative n z)‖ ≤
      |t| *
        (‖saddleMellinInversePower r z *
            minusSaddleMellinData ε ℓ z‖ +
          ‖saddleMellinInversePower r z *
            (∑ n ∈ Finset.range (N + 1),
              minusSaddlePoleResidue ε ℓ n *
                saddleGaussianPoleRepresentative n z)‖) := by
        gcongr
        exact norm_sub_le _ _
    _ = |t| *
          ‖saddleMellinInversePower r z *
            minusSaddleMellinData ε ℓ z‖ +
        |t| *
          ‖saddleMellinInversePower r z *
            (∑ n ∈ Finset.range (N + 1),
              minusSaddlePoleResidue ε ℓ n *
                saddleGaussianPoleRepresentative n z)‖ := by
        ring
    _ ≤ D + G := by
      apply add_le_add
      · simpa [z] using! hdata a ha t ht
      · simpa [z] using! hgaussian a ha t ht
theorem plusSaddleFiniteRapidContourIntegrand_horizontalIntegral_tendsto_zero
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B)
    (s : ℝ) (hs : |s| = 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          plusSaddleFiniteRapidContourIntegrand ε ℓ N r
            ((a : ℂ) + ((s * T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    plusSaddleFiniteRapidContourIntegrand_horizontalStrip_bound
      hε hℓ horder hr N hhalf hAB
  exact saddleHorizontalIntegral_tendsto_zero
    (F := plusSaddleFiniteRapidContourIntegrand ε ℓ N r)
    hAB hbound s hs
theorem minusSaddleFiniteRapidContourIntegrand_horizontalIntegral_tendsto_zero
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B)
    (s : ℝ) (hs : |s| = 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          minusSaddleFiniteRapidContourIntegrand ε ℓ N r
            ((a : ℂ) + ((s * T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    minusSaddleFiniteRapidContourIntegrand_horizontalStrip_bound
      hε hℓ horder hr N hhalf hAB
  exact saddleHorizontalIntegral_tendsto_zero
    (F := minusSaddleFiniteRapidContourIntegrand ε ℓ N r)
    hAB hbound s hs
def saddleCauchyPolePrimitive (a t : ℝ) : ℂ :=
  (Real.arctan (t / a) : ℂ) -
    ((Real.log (a ^ 2 + t ^ 2) / 2 : ℝ) : ℂ) *
      Complex.I
theorem saddleCauchyPolePrimitive_hasDerivAt
    {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    HasDerivAt (saddleCauchyPolePrimitive a)
      (((a : ℂ) + (t : ℂ) * Complex.I)⁻¹) t := by
  have hden : a ^ 2 + t ^ 2 ≠ 0 := by
    have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    nlinarith [sq_nonneg t]
  have hatan : HasDerivAt
      (fun y : ℝ => Real.arctan (y / a))
      (a / (a ^ 2 + t ^ 2)) t := by
    convert! (Real.hasDerivAt_arctan (t / a)).comp t
      ((hasDerivAt_id t).div_const a) using 1
    field_simp [ha, hden]
  have hquadratic : HasDerivAt
      (fun y : ℝ => a ^ 2 + y ^ 2)
      (2 * t) t := by
    convert! ((hasDerivAt_id t).pow 2).const_add
      (a ^ 2) using 1; simp [id]
  have hlog : HasDerivAt
      (fun y : ℝ => Real.log (a ^ 2 + y ^ 2) / 2)
      (t / (a ^ 2 + t ^ 2)) t := by
    convert! ((Real.hasDerivAt_log hden).comp t
      hquadratic).div_const 2 using 1
    field_simp [hden]
  have hvalue :
      ((a / (a ^ 2 + t ^ 2) : ℝ) : ℂ) -
        ((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) *
          Complex.I =
      ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹ := by
    have hz : (a : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
      intro hz
      apply ha
      have hre := congrArg Complex.re hz
      simpa [Complex.mul_re] using! hre
    have hcden : ((a ^ 2 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hden
    have hcden' : (a : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
      simpa using! hcden
    apply (mul_eq_one_iff_eq_inv₀ hz).mp
    push_cast
    field_simp [hcden', Complex.I_sq]; ring_nf; simp [Complex.I_sq]
  rw [← hvalue]
  exact hatan.ofReal_comp.sub
    (hlog.ofReal_comp.mul_const Complex.I)
theorem saddleCauchyPole_symmetric_intervalIntegral
    {a : ℝ} (ha : a ≠ 0) (T : ℝ) :
    (∫ t in -T..T,
      ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹) =
      ((2 * Real.arctan (T / a) : ℝ) : ℂ) := by
  have hline : Continuous
      (fun t : ℝ => (a : ℂ) + (t : ℂ) * Complex.I) := by
    fun_prop
  have hnonzero : ∀ t : ℝ,
      (a : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t hzero
    apply ha
    have hre := congrArg Complex.re hzero
    simpa [Complex.mul_re] using! hre
  have hint : IntervalIntegrable
      (fun t : ℝ =>
        ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹)
      volume (-T) T :=
    (hline.inv₀ hnonzero).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => saddleCauchyPolePrimitive_hasDerivAt ha t)
      hint]
  unfold saddleCauchyPolePrimitive
  simp [neg_div, Real.arctan_neg, pow_two]; ring
theorem saddleInfiniteRectangle_vertical_integral_eq
    {F : ℂ → ℂ} {A B : ℝ}
    (hA : Integrable
      (fun t : ℝ => F ((A : ℂ) + (t : ℂ) * Complex.I)))
    (hB : Integrable
      (fun t : ℝ => F ((B : ℂ) + (t : ℂ) * Complex.I)))
    (hlower : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0))
    (hupper : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          F ((a : ℂ) + (T : ℂ) * Complex.I))
      Filter.atTop (𝓝 0))
    (hrectangle : ∀ T : ℝ,
      (∫ a in A..B,
        F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
      (∫ a in A..B,
        F ((a : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I *
        (∫ t in -T..T,
          F ((B : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I *
        (∫ t in -T..T,
          F ((A : ℂ) + (t : ℂ) * Complex.I)) = 0) :
    (∫ t : ℝ,
      F ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      F ((A : ℂ) + (t : ℂ) * Complex.I)) := by
  have hright : Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          F ((B : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (𝓝 (∫ t : ℝ,
        F ((B : ℂ) + (t : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral hB
      tendsto_neg_atTop_atBot tendsto_id
  have hleft : Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          F ((A : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (𝓝 (∫ t : ℝ,
        F ((A : ℂ) + (t : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral hA
      tendsto_neg_atTop_atBot tendsto_id
  have hlimit : Tendsto
      (fun T : ℝ =>
        (∫ a in A..B,
          F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
        (∫ a in A..B,
          F ((a : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I *
          (∫ t in -T..T,
            F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I *
          (∫ t in -T..T,
            F ((A : ℂ) + (t : ℂ) * Complex.I)))
      Filter.atTop
      (𝓝 (Complex.I *
        (∫ t : ℝ,
          F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I *
        (∫ t : ℝ,
          F ((A : ℂ) + (t : ℂ) * Complex.I)))) := by
    simpa using!
      (((hlower.sub hupper).add
        (tendsto_const_nhds.mul hright)).sub
          (tendsto_const_nhds.mul hleft))
  have hzero : Tendsto
      (fun T : ℝ =>
        (∫ a in A..B,
          F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
        (∫ a in A..B,
          F ((a : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I *
          (∫ t in -T..T,
            F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I *
          (∫ t in -T..T,
            F ((A : ℂ) + (t : ℂ) * Complex.I)))
      Filter.atTop (𝓝 0) :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (0 : ℂ))
        Filter.atTop (𝓝 0)).congr'
          (Filter.Eventually.of_forall
            (fun T : ℝ => (hrectangle T).symm))
  have hidentity :
      Complex.I *
        ((∫ t : ℝ,
          F ((B : ℂ) + (t : ℂ) * Complex.I)) -
          (∫ t : ℝ,
            F ((A : ℂ) + (t : ℂ) * Complex.I))) = 0 := by
    simpa [mul_sub] using!
      (tendsto_nhds_unique hlimit hzero)
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hidentity).resolve_left
      Complex.I_ne_zero)
theorem plusSaddleFiniteRapidContourIntegrand_vertical_integral_eq
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B)
    (hApole : ∀ n : ℕ, A ≠ -((2 * n : ℕ) : ℝ))
    (hBpole : ∀ n : ℕ, B ≠ -((2 * n : ℕ) : ℝ)) :
    (∫ t : ℝ,
      plusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      plusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((A : ℂ) + (t : ℂ) * Complex.I)) := by
  have hhalfB : -(2 * ((N : ℝ) + 1)) < B :=
    hhalf.trans_le hAB
  have hleft :=
    plusSaddleFiniteRapidContourIntegrand_shiftedLine_integrable
      hε hℓ horder N hhalf hApole hr
  have hright :=
    plusSaddleFiniteRapidContourIntegrand_shiftedLine_integrable
      hε hℓ horder N hhalfB hBpole hr
  have hlower : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          plusSaddleFiniteRapidContourIntegrand ε ℓ N r
            ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
    simpa using!
      plusSaddleFiniteRapidContourIntegrand_horizontalIntegral_tendsto_zero
        hε hℓ horder hr N hhalf hAB
          (-1 : ℝ) (by norm_num)
  have hupper : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          plusSaddleFiniteRapidContourIntegrand ε ℓ N r
            ((a : ℂ) + (T : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
    simpa using!
      plusSaddleFiniteRapidContourIntegrand_horizontalIntegral_tendsto_zero
        hε hℓ horder hr N hhalf hAB
          (1 : ℝ) (by norm_num)
  apply saddleInfiniteRectangle_vertical_integral_eq
    hleft hright hlower hupper
  intro T
  let z : ℂ := (A : ℂ) + ((-T : ℝ) : ℂ) * Complex.I
  let w : ℂ := (B : ℂ) + (T : ℂ) * Complex.I
  have hz : z ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < z.re
    simpa [z, Complex.mul_re] using! hhalf
  have hw : w ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < w.re
    simpa [w, Complex.mul_re] using! hhalfB
  simpa [z, w, Complex.mul_re, Complex.mul_im,
    smul_eq_mul] using!
      plusSaddleFiniteRapidContourIntegrand_boundary_rectangle
        hε horder ℓ N hr z w hz hw
theorem minusSaddleFiniteRapidContourIntegrand_vertical_integral_eq
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B)
    (hApole : ∀ n : ℕ, A ≠ -((2 * n : ℕ) : ℝ))
    (hBpole : ∀ n : ℕ, B ≠ -((2 * n : ℕ) : ℝ)) :
    (∫ t : ℝ,
      minusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      minusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((A : ℂ) + (t : ℂ) * Complex.I)) := by
  have hhalfB : -(2 * ((N : ℝ) + 1)) < B :=
    hhalf.trans_le hAB
  have hleft :=
    minusSaddleFiniteRapidContourIntegrand_shiftedLine_integrable
      hε hℓ horder N hhalf hApole hr
  have hright :=
    minusSaddleFiniteRapidContourIntegrand_shiftedLine_integrable
      hε hℓ horder N hhalfB hBpole hr
  have hlower : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          minusSaddleFiniteRapidContourIntegrand ε ℓ N r
            ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
    simpa using!
      minusSaddleFiniteRapidContourIntegrand_horizontalIntegral_tendsto_zero
        hε hℓ horder hr N hhalf hAB
          (-1 : ℝ) (by norm_num)
  have hupper : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          minusSaddleFiniteRapidContourIntegrand ε ℓ N r
            ((a : ℂ) + (T : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
    simpa using!
      minusSaddleFiniteRapidContourIntegrand_horizontalIntegral_tendsto_zero
        hε hℓ horder hr N hhalf hAB
          (1 : ℝ) (by norm_num)
  apply saddleInfiniteRectangle_vertical_integral_eq
    hleft hright hlower hupper
  intro T
  let z : ℂ := (A : ℂ) + ((-T : ℝ) : ℂ) * Complex.I
  let w : ℂ := (B : ℂ) + (T : ℂ) * Complex.I
  have hz : z ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < z.re
    simpa [z, Complex.mul_re] using! hhalf
  have hw : w ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < w.re
    simpa [w, Complex.mul_re] using! hhalfB
  simpa [z, w, Complex.mul_re, Complex.mul_im,
    smul_eq_mul] using!
      minusSaddleFiniteRapidContourIntegrand_boundary_rectangle
        hε horder ℓ N hr z w hz hw
theorem plusSaddleSpectrum_moment_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (k : ℕ) :
    Integrable (fun t : ℝ =>
      (t : ℂ) ^ k * plusSaddleSpectrum ε ℓ t) := by
  apply integrable_of_continuous_polynomial_decay
    (plusSaddleSpectrum_continuous hε hℓ horder)
  intro j
  refine ⟨((1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3) *
    ((2 : ℝ) ^ (j + 3) *
      Real.Gamma (ℓ / 2 + (j + 3)) *
      Real.exp (2 * |ℓ| * saddleShellTotalVariation ε)), ?_, ?_⟩
  · have hgamma : 0 < Real.Gamma (ℓ / 2 + (j + 3)) :=
      Real.Gamma_pos_of_pos (by positivity)
    positivity
  · intro t ht
    exact plusSaddleSpectrum_vertical_polynomial_bound
      hε hℓ horder ht j
theorem minusSaddleSpectrum_moment_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (k : ℕ) :
    Integrable (fun t : ℝ =>
      (t : ℂ) ^ k * minusSaddleSpectrum ε ℓ t) := by
  apply integrable_of_continuous_polynomial_decay
    (minusSaddleSpectrum_continuous hε hℓ horder)
  intro j
  refine ⟨((1 + |beta ε|) * (1 + ℓ⁻¹) ^ 3) *
    ((2 : ℝ) ^ (j + 3) *
      Real.Gamma (ℓ / 2 + (j + 3)) *
      Real.exp (2 * |ℓ| * saddleShellTotalVariation ε)), ?_, ?_⟩
  · have hgamma : 0 < Real.Gamma (ℓ / 2 + (j + 3)) :=
      Real.Gamma_pos_of_pos (by positivity)
    positivity
  · intro t ht
    exact minusSaddleSpectrum_vertical_polynomial_bound
      hε hℓ horder ht j
theorem plusSaddleSpectrum_norm_moment_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (k : ℕ) :
    Integrable (fun t : ℝ =>
      |t| ^ k * ‖plusSaddleSpectrum ε ℓ t‖) := by
  simpa [norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs] using!
      (plusSaddleSpectrum_moment_integrable
        hε hℓ horder k).norm
theorem minusSaddleSpectrum_norm_moment_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (k : ℕ) :
    Integrable (fun t : ℝ =>
      |t| ^ k * ‖minusSaddleSpectrum ε ℓ t‖) := by
  simpa [norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs] using!
      (minusSaddleSpectrum_moment_integrable
        hε hℓ horder k).norm
def plusSaddleFourierData (ε ℓ y : ℝ) : ℂ :=
  plusSaddleSpectrum ε ℓ (-(2 * Real.pi * y))
def minusSaddleFourierData (ε ℓ y : ℝ) : ℂ :=
  minusSaddleSpectrum ε ℓ (-(2 * Real.pi * y))
theorem integrable_scaled_norm_moment
    {F : ℝ → ℂ} (hF : Continuous F)
    (hmom : ∀ j : ℕ,
      Integrable (fun t : ℝ => |t| ^ j * ‖F t‖))
    {c : ℝ} (hc : c ≠ 0) (hclarge : 1 ≤ |c|) (k : ℕ) :
    Integrable (fun y : ℝ => ‖y‖ ^ k * ‖F (c * y)‖) := by
  have hbase : Integrable (fun y : ℝ =>
      |c * y| ^ k * ‖F (c * y)‖) :=
    (hmom k).comp_mul_left' hc
  have hcomp : Continuous (fun y : ℝ => F (c * y)) :=
    hF.comp (by fun_prop)
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => |y| ^ k * ‖F (c * y)‖) :=
    ((continuous_abs.pow k).mul hcomp.norm).aestronglyMeasurable
  have hresult : Integrable
      (fun y : ℝ => |y| ^ k * ‖F (c * y)‖) := by
    apply hbase.mono' hmeas
    filter_upwards [] with y
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg y) k)
        (norm_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [abs_mul]
    gcongr
    calc
      |y| = 1 * |y| := by ring
      _ ≤ |c| * |y| := by gcongr
  simpa only [Real.norm_eq_abs] using! hresult
theorem plusSaddleFourierData_norm_moment_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (k : ℕ) :
    Integrable (fun y : ℝ =>
      ‖y‖ ^ k * ‖plusSaddleFourierData ε ℓ y‖) := by
  let c : ℝ := -(2 * Real.pi)
  have hc : c ≠ 0 := by
    try dsimp [c]
    exact neg_ne_zero.mpr
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hclarge : 1 ≤ |c| := by
    try dsimp [c]
    rw [abs_neg, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith [Real.pi_gt_three]
  have h := integrable_scaled_norm_moment
    (plusSaddleSpectrum_continuous hε hℓ horder)
    (fun j => plusSaddleSpectrum_norm_moment_integrable
      hε hℓ horder j) hc hclarge k
  simpa [plusSaddleFourierData, c, neg_mul, mul_assoc] using! h
theorem minusSaddleFourierData_norm_moment_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (k : ℕ) :
    Integrable (fun y : ℝ =>
      ‖y‖ ^ k * ‖minusSaddleFourierData ε ℓ y‖) := by
  let c : ℝ := -(2 * Real.pi)
  have hc : c ≠ 0 := by
    try dsimp [c]
    exact neg_ne_zero.mpr
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hclarge : 1 ≤ |c| := by
    try dsimp [c]
    rw [abs_neg, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith [Real.pi_gt_three]
  have h := integrable_scaled_norm_moment
    (minusSaddleSpectrum_continuous hε hℓ horder)
    (fun j => minusSaddleSpectrum_norm_moment_integrable
      hε hℓ horder j) hc hclarge k
  simpa [minusSaddleFourierData, c, neg_mul, mul_assoc] using! h
theorem plusSaddleFourierData_fourier_contDiff {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ContDiff ℝ ∞ (𝓕 (plusSaddleFourierData ε ℓ)) := by
  exact Real.contDiff_fourier (N := ⊤) (fun n _ =>
    plusSaddleFourierData_norm_moment_integrable
      hε hℓ horder n)
theorem minusSaddleFourierData_fourier_contDiff {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ContDiff ℝ ∞ (𝓕 (minusSaddleFourierData ε ℓ)) := by
  exact Real.contDiff_fourier (N := ⊤) (fun n _ =>
    minusSaddleFourierData_norm_moment_integrable
      hε hℓ horder n)
theorem plusSaddleMellinData_fourier_vertical (ε ℓ y : ℝ) :
    plusSaddleMellinData ε ℓ
      ((ℓ : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) =
        plusSaddleFourierData ε ℓ y := by
  have harg :
      ((ℓ : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) =
        ((ℓ : ℂ) - Complex.I *
          ((-(2 * Real.pi * y) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [harg, plusSaddleMellinData_vertical]
  rfl
theorem minusSaddleMellinData_fourier_vertical (ε ℓ y : ℝ) :
    minusSaddleMellinData ε ℓ
      ((ℓ : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) =
        minusSaddleFourierData ε ℓ y := by
  have harg :
      ((ℓ : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) =
        ((ℓ : ℂ) - Complex.I *
          ((-(2 * Real.pi * y) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [harg, minusSaddleMellinData_vertical]
  rfl
theorem plusSaddleProfile_eq_fourier (ε ℓ : ℝ)
    {r : ℝ} (hr : 0 < r) :
    plusSaddleProfile ε ℓ r =
      (r ^ (-ℓ) : ℝ) *
        (𝓕 (plusSaddleFourierData ε ℓ)) (Real.log r) := by
  have hline : (fun y : ℝ =>
      plusSaddleMellinData ε ℓ
        ((ℓ : ℂ) + 2 * (Real.pi : ℂ) * (y : ℂ) * Complex.I)) =
        plusSaddleFourierData ε ℓ := by
    funext y
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using! plusSaddleMellinData_fourier_vertical ε ℓ y
  unfold plusSaddleProfile
  rw [if_neg hr.ne', mellinInv_eq_fourierInv ℓ
    (plusSaddleMellinData ε ℓ) hr, hline,
    Real.fourierInv_eq_fourier_neg]
  simp only [neg_neg, smul_eq_mul]
  have hpow :
      (r : ℂ) ^ (-(ℓ : ℂ)) = ((r ^ (-ℓ) : ℝ) : ℂ) := by
    simpa using! (Complex.ofReal_cpow hr.le (-ℓ)).symm
  rw [hpow]
theorem minusSaddleProfile_eq_fourier (ε ℓ : ℝ)
    {r : ℝ} (hr : 0 < r) :
    minusSaddleProfile ε ℓ r =
      (r ^ (-ℓ) : ℝ) *
        (𝓕 (minusSaddleFourierData ε ℓ)) (Real.log r) := by
  have hline : (fun y : ℝ =>
      minusSaddleMellinData ε ℓ
        ((ℓ : ℂ) + 2 * (Real.pi : ℂ) * (y : ℂ) * Complex.I)) =
        minusSaddleFourierData ε ℓ := by
    funext y
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using! minusSaddleMellinData_fourier_vertical ε ℓ y
  unfold minusSaddleProfile
  rw [if_neg hr.ne', mellinInv_eq_fourierInv ℓ
    (minusSaddleMellinData ε ℓ) hr, hline,
    Real.fourierInv_eq_fourier_neg]
  simp only [neg_neg, smul_eq_mul]
  have hpow :
      (r : ℂ) ^ (-(ℓ : ℂ)) = ((r ^ (-ℓ) : ℝ) : ℂ) := by
    simpa using! (Complex.ofReal_cpow hr.le (-ℓ)).symm
  rw [hpow]
theorem plusSaddleProfile_contDiffOn {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ContDiffOn ℝ ∞ (plusSaddleProfile ε ℓ) (Set.Ioi 0) := by
  have hpow : ContDiffOn ℝ ∞
      (fun r : ℝ => r ^ (-ℓ)) (Set.Ioi 0) :=
    contDiff_id.contDiffOn.rpow_const_of_ne
      (fun r hr => (show 0 < r from hr).ne')
  have hweight : ContDiffOn ℝ ∞
      (fun r : ℝ => ((r ^ (-ℓ) : ℝ) : ℂ)) (Set.Ioi 0) :=
    Complex.ofRealCLM.contDiff.fun_comp_contDiffOn hpow
  have hlog : ContDiffOn ℝ ∞ Real.log (Set.Ioi 0) :=
    contDiff_id.contDiffOn.log
      (fun r hr => (show 0 < r from hr).ne')
  have hfourier : ContDiffOn ℝ ∞
      (fun r : ℝ =>
        (𝓕 (plusSaddleFourierData ε ℓ)) (Real.log r))
      (Set.Ioi 0) :=
    (plusSaddleFourierData_fourier_contDiff hε hℓ horder).fun_comp_contDiffOn hlog
  exact (hweight.mul hfourier).congr
    (fun r hr => (plusSaddleProfile_eq_fourier
      ε ℓ (show 0 < r from hr)))
theorem minusSaddleProfile_contDiffOn {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ContDiffOn ℝ ∞ (minusSaddleProfile ε ℓ) (Set.Ioi 0) := by
  have hpow : ContDiffOn ℝ ∞
      (fun r : ℝ => r ^ (-ℓ)) (Set.Ioi 0) :=
    contDiff_id.contDiffOn.rpow_const_of_ne
      (fun r hr => (show 0 < r from hr).ne')
  have hweight : ContDiffOn ℝ ∞
      (fun r : ℝ => ((r ^ (-ℓ) : ℝ) : ℂ)) (Set.Ioi 0) :=
    Complex.ofRealCLM.contDiff.fun_comp_contDiffOn hpow
  have hlog : ContDiffOn ℝ ∞ Real.log (Set.Ioi 0) :=
    contDiff_id.contDiffOn.log
      (fun r hr => (show 0 < r from hr).ne')
  have hfourier : ContDiffOn ℝ ∞
      (fun r : ℝ =>
        (𝓕 (minusSaddleFourierData ε ℓ)) (Real.log r))
      (Set.Ioi 0) :=
    (minusSaddleFourierData_fourier_contDiff hε hℓ horder).fun_comp_contDiffOn hlog
  exact (hweight.mul hfourier).congr
    (fun r hr => (minusSaddleProfile_eq_fourier
      ε ℓ (show 0 < r from hr)))
theorem plusSaddleFunction_contDiffOn {ε : ℝ}
    (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ContDiffOn ℝ ∞ (plusSaddleFunction ε d)
      ({0}ᶜ : Set (Euclidean d)) := by
  have hdimension : 0 < (d : ℝ) / 2 := by
    exact div_pos (by exact_mod_cast hd) (by norm_num)
  have hnorm : ContDiffOn ℝ ∞
      (fun x : Euclidean d => ‖x‖)
      ({0}ᶜ : Set (Euclidean d)) := by
    apply ContDiffOn.norm ℝ
    · exact contDiff_id.contDiffOn
    · intro x hx
      simpa only [Set.mem_compl_iff,
        Set.mem_singleton_iff] using! hx
  have hmaps : Set.MapsTo
      (fun x : Euclidean d => ‖x‖)
      ({0}ᶜ : Set (Euclidean d)) (Set.Ioi 0) := by
    intro x hx
    apply norm_pos_iff.mpr
    simpa only [Set.mem_compl_iff,
      Set.mem_singleton_iff] using! hx
  simpa only [plusSaddleFunction, Function.comp_apply] using!
    (plusSaddleProfile_contDiffOn
      hε hdimension horder).comp hnorm hmaps
theorem minusSaddleFunction_contDiffOn {ε : ℝ}
    (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ContDiffOn ℝ ∞ (minusSaddleFunction ε d)
      ({0}ᶜ : Set (Euclidean d)) := by
  have hdimension : 0 < (d : ℝ) / 2 := by
    exact div_pos (by exact_mod_cast hd) (by norm_num)
  have hnorm : ContDiffOn ℝ ∞
      (fun x : Euclidean d => ‖x‖)
      ({0}ᶜ : Set (Euclidean d)) := by
    apply ContDiffOn.norm ℝ
    · exact contDiff_id.contDiffOn
    · intro x hx
      simpa only [Set.mem_compl_iff,
        Set.mem_singleton_iff] using! hx
  have hmaps : Set.MapsTo
      (fun x : Euclidean d => ‖x‖)
      ({0}ᶜ : Set (Euclidean d)) (Set.Ioi 0) := by
    intro x hx
    apply norm_pos_iff.mpr
    simpa only [Set.mem_compl_iff,
      Set.mem_singleton_iff] using! hx
  simpa only [minusSaddleFunction, Function.comp_apply] using!
    (minusSaddleProfile_contDiffOn
      hε hdimension horder).comp hnorm hmaps
theorem plusSaddleSpectrum_conj (ε ℓ t : ℝ) :
    starRingEnd ℂ (plusSaddleSpectrum ε ℓ t) =
      plusSaddleSpectrum ε ℓ (-t) := by
  unfold plusSaddleSpectrum
  rw [map_mul, saddleEnvelope_conj, plusPolynomial_conj]
  congr 1
  simp only [map_div₀, Complex.conj_ofReal]
  have hneg :
      ((-t : ℝ) : ℂ) / (ℓ : ℂ) =
        -((t : ℂ) / (ℓ : ℂ)) := by
    push_cast
    ring
  rw [hneg]
  simpa using!
    (minusPolynomial_neg ε (-((t : ℂ) / (ℓ : ℂ))))
theorem minusSaddleSpectrum_conj (ε ℓ t : ℝ) :
    starRingEnd ℂ (minusSaddleSpectrum ε ℓ t) =
      minusSaddleSpectrum ε ℓ (-t) := by
  unfold minusSaddleSpectrum
  rw [map_mul, saddleEnvelope_conj, minusPolynomial_conj]
  congr 1
  simp only [map_div₀, Complex.conj_ofReal]
  have hneg :
      ((-t : ℝ) : ℂ) / (ℓ : ℂ) =
        -((t : ℂ) / (ℓ : ℂ)) := by
    push_cast
    ring
  rw [hneg]
  exact (minusPolynomial_neg ε ((t : ℂ) / (ℓ : ℂ))).symm
theorem mellinInversePower_conj {r : ℝ} (hr : 0 < r)
    (σ t : ℝ) :
    starRingEnd ℂ
      ((r : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) =
        (r : ℂ) ^
          (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)) := by
  have harg : (r : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact Real.pi_ne_zero.symm
  have hpower :=
    (Complex.cpow_conj (r : ℂ)
      (-((σ : ℂ) + (t : ℂ) * Complex.I)) harg).symm
  simpa [map_neg, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I] using! hpower
theorem mellinInv_real_of_hermitian (σ : ℝ) (F : ℂ → ℂ)
    (hF : ∀ t : ℝ,
      starRingEnd ℂ (F ((σ : ℂ) + (t : ℂ) * Complex.I)) =
        F ((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))
    {r : ℝ} (hr : 0 < r) :
    (mellinInv σ F r).im = 0 := by
  let g : ℝ → ℂ := fun t =>
    (r : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
      F ((σ : ℂ) + (t : ℂ) * Complex.I)
  have hsym (t : ℝ) :
      starRingEnd ℂ (g t) = g (-t) := by
    try dsimp [g]
    rw [map_mul, mellinInversePower_conj hr σ t, hF t]
  have hintegral :
      starRingEnd ℂ (∫ t : ℝ, g t) = ∫ t : ℝ, g t := by
    calc
      starRingEnd ℂ (∫ t : ℝ, g t) =
          ∫ t : ℝ, starRingEnd ℂ (g t) :=
            (integral_conj (f := g)).symm
      _ = ∫ t : ℝ, g (-t) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with t
            exact hsym t
      _ = ∫ t : ℝ, g t := by
            rw [integral_neg_eq_self]
  have hrewrite :
      mellinInv σ F r =
        (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, g t := by
    unfold mellinInv
    simp only [g, smul_eq_mul]
  apply Complex.conj_eq_iff_im.mp
  rw [hrewrite]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal,
    hintegral]
theorem plusSaddleMellinData_conj_vertical (ε ℓ t : ℝ) :
    starRingEnd ℂ
      (plusSaddleMellinData ε ℓ
        ((ℓ : ℂ) + (t : ℂ) * Complex.I)) =
      plusSaddleMellinData ε ℓ
        ((ℓ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) := by
  have hleft :
      ((ℓ : ℂ) + (t : ℂ) * Complex.I) =
        ((ℓ : ℂ) - Complex.I * ((-t : ℝ) : ℂ)) := by
    push_cast
    ring
  have hright :
      ((ℓ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) =
        ((ℓ : ℂ) - Complex.I * (t : ℂ)) := by
    push_cast
    ring
  rw [hleft, plusSaddleMellinData_vertical,
    hright, plusSaddleMellinData_vertical]
  simpa using! plusSaddleSpectrum_conj ε ℓ (-t)
theorem minusSaddleMellinData_conj_vertical (ε ℓ t : ℝ) :
    starRingEnd ℂ
      (minusSaddleMellinData ε ℓ
        ((ℓ : ℂ) + (t : ℂ) * Complex.I)) =
      minusSaddleMellinData ε ℓ
        ((ℓ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) := by
  have hleft :
      ((ℓ : ℂ) + (t : ℂ) * Complex.I) =
        ((ℓ : ℂ) - Complex.I * ((-t : ℝ) : ℂ)) := by
    push_cast
    ring
  have hright :
      ((ℓ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) =
        ((ℓ : ℂ) - Complex.I * (t : ℂ)) := by
    push_cast
    ring
  rw [hleft, minusSaddleMellinData_vertical,
    hright, minusSaddleMellinData_vertical]
  simpa using! minusSaddleSpectrum_conj ε ℓ (-t)
theorem plusSaddleProfile_real (ε ℓ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (plusSaddleProfile ε ℓ r).im = 0 := by
  by_cases hzero : r = 0
  · simp [plusSaddleProfile, hzero]
  · have hpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hzero)
    simp only [plusSaddleProfile, if_neg hzero]
    exact mellinInv_real_of_hermitian ℓ
      (plusSaddleMellinData ε ℓ)
      (plusSaddleMellinData_conj_vertical ε ℓ) hpos
theorem minusSaddleProfile_real (ε ℓ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (minusSaddleProfile ε ℓ r).im = 0 := by
  by_cases hzero : r = 0
  · simp [minusSaddleProfile, hzero]
  · have hpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hzero)
    simp only [minusSaddleProfile, if_neg hzero]
    exact mellinInv_real_of_hermitian ℓ
      (minusSaddleMellinData ε ℓ)
      (minusSaddleMellinData_conj_vertical ε ℓ) hpos
theorem plusSaddleFunction_real (ε : ℝ) (d : ℕ)
    (x : Euclidean d) :
    (plusSaddleFunction ε d x).im = 0 := by
  exact plusSaddleProfile_real ε ((d : ℝ) / 2) (norm_nonneg x)
theorem minusSaddleFunction_real (ε : ℝ) (d : ℕ)
    (x : Euclidean d) :
    (minusSaddleFunction ε d x).im = 0 := by
  exact minusSaddleProfile_real ε ((d : ℝ) / 2) (norm_nonneg x)
theorem mellinMultiplier_mul_saddleEnvelope_neg
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    mellinMultiplier ℓ t * saddleEnvelope ε ℓ (-t) =
      saddleEnvelope ε ℓ t := by
  have hgamma := mellinMultiplier_denominator_ne_zero hℓ t
  have harg : ((-t : ℝ) : ℂ) / (ℓ : ℂ) =
      -((t : ℂ) / (ℓ : ℂ)) := by
    push_cast
    ring
  have hgammaarg :
      (((ℓ : ℂ) - Complex.I * ((-t : ℝ) : ℂ)) / 2) =
        (((ℓ : ℂ) + Complex.I * (t : ℂ)) / 2) := by
    push_cast
    ring
  have hphase :
      Complex.exp
          (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ)) *
        Complex.exp
          (Complex.I * ((-t : ℝ) : ℂ) *
            (Real.log Real.pi : ℂ) / 2) =
        Complex.exp
          (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold mellinMultiplier saddleEnvelope
  rw [harg, mellinShellPhase_neg, hgammaarg]
  calc
    _ = (Complex.exp
          (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ)) *
        Complex.exp
          (Complex.I * ((-t : ℝ) : ℂ) *
            (Real.log Real.pi : ℂ) / 2)) *
        Complex.Gamma (((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2) *
        Complex.exp ((ℓ : ℂ) *
          mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ))) := by
      field_simp [hgamma]
    _ = _ := by rw [hphase]
theorem mellinMultiplier_mul_minusSaddleSpectrum_neg
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    mellinMultiplier ℓ t * minusSaddleSpectrum ε ℓ (-t) =
      plusSaddleSpectrum ε ℓ t := by
  have harg : ((-t : ℝ) : ℂ) / (ℓ : ℂ) =
      -((t : ℂ) / (ℓ : ℂ)) := by
    push_cast
    ring
  unfold minusSaddleSpectrum plusSaddleSpectrum
  rw [harg, minusPolynomial_neg]
  rw [← mul_assoc, mellinMultiplier_mul_saddleEnvelope_neg hℓ t]
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Interval Topology
theorem saddleCauchyPole_symmetric_intervalIntegral_tendsto_pos
    {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹)
      Filter.atTop (𝓝 (Real.pi : ℂ)) := by
  have hdiv : Tendsto (fun T : ℝ => T / a)
      Filter.atTop Filter.atTop :=
    (tendsto_div_const_atTop_of_pos ha).2 tendsto_id
  have hatan : Tendsto
      (fun T : ℝ => Real.arctan (T / a))
      Filter.atTop (𝓝 (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin
      Real.tendsto_arctan_atTop).comp hdiv
  have hreal : Tendsto
      (fun T : ℝ => 2 * Real.arctan (T / a))
      Filter.atTop (𝓝 Real.pi) := by
    convert! (tendsto_const_nhds.mul hatan) using 1
    all_goals ring_nf
  have hcomplex : Tendsto
      (fun T : ℝ =>
        ((2 * Real.arctan (T / a) : ℝ) : ℂ))
      Filter.atTop (𝓝 (Real.pi : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  exact hcomplex.congr'
    (Filter.Eventually.of_forall
      (fun T : ℝ =>
        (saddleCauchyPole_symmetric_intervalIntegral
          ha.ne' T).symm))
theorem saddleCauchyPole_symmetric_intervalIntegral_tendsto_neg
    {a : ℝ} (ha : a < 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹)
      Filter.atTop (𝓝 (-(Real.pi : ℂ))) := by
  have hdiv : Tendsto (fun T : ℝ => T / a)
      Filter.atTop Filter.atBot :=
    (tendsto_div_const_atBot_of_neg ha).2 tendsto_id
  have hatan : Tendsto
      (fun T : ℝ => Real.arctan (T / a))
      Filter.atTop (𝓝 (-(Real.pi / 2))) :=
    (tendsto_nhds_of_tendsto_nhdsWithin
      Real.tendsto_arctan_atBot).comp hdiv
  have hreal : Tendsto
      (fun T : ℝ => 2 * Real.arctan (T / a))
      Filter.atTop (𝓝 (-Real.pi)) := by
    convert! (tendsto_const_nhds.mul hatan) using 1
    all_goals ring_nf
  have hcomplex : Tendsto
      (fun T : ℝ =>
        ((2 * Real.arctan (T / a) : ℝ) : ℂ))
      Filter.atTop (𝓝 (-(Real.pi : ℂ))) := by
    simpa only [Function.comp_apply, Complex.ofReal_neg] using!
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        hreal)
  exact hcomplex.congr'
    (Filter.Eventually.of_forall
      (fun T : ℝ =>
        (saddleCauchyPole_symmetric_intervalIntegral
          ha.ne T).symm))
theorem saddleShiftedCauchyPole_symmetric_intervalIntegral_tendsto_pos
    (n : ℕ) {a : ℝ}
    (ha : -((2 * n : ℕ) : ℝ) < a) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          (((a : ℂ) + (t : ℂ) * Complex.I +
            ((2 * n : ℕ) : ℂ))⁻¹))
      Filter.atTop (𝓝 (Real.pi : ℂ)) := by
  have hshift : 0 < a + ((2 * n : ℕ) : ℝ) := by
    linarith
  have hlimit :=
    saddleCauchyPole_symmetric_intervalIntegral_tendsto_pos
      hshift
  apply hlimit.congr'
  filter_upwards [] with T
  apply intervalIntegral.integral_congr
  intro t _
  push_cast
  ring
theorem saddleShiftedCauchyPole_symmetric_intervalIntegral_tendsto_neg
    (n : ℕ) {a : ℝ}
    (ha : a < -((2 * n : ℕ) : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          (((a : ℂ) + (t : ℂ) * Complex.I +
            ((2 * n : ℕ) : ℂ))⁻¹))
      Filter.atTop (𝓝 (-(Real.pi : ℂ))) := by
  have hshift : a + ((2 * n : ℕ) : ℝ) < 0 := by
    linarith
  have hlimit :=
    saddleCauchyPole_symmetric_intervalIntegral_tendsto_neg
      hshift
  apply hlimit.congr'
  filter_upwards [] with T
  apply intervalIntegral.integral_congr
  intro t _
  push_cast
  ring
theorem saddleGaussianPoleRepresentative_eq_inv_add_slope
    (n : ℕ) {z : ℂ}
    (hz : z + ((2 * n : ℕ) : ℂ) ≠ 0) :
    saddleGaussianPoleRepresentative n z =
      (z + ((2 * n : ℕ) : ℂ))⁻¹ +
        saddleGaussianPoleSlope
          (z + ((2 * n : ℕ) : ℂ)) := by
  rw [saddleGaussianPoleSlope_eq_of_ne hz]
  unfold saddleGaussianPoleRepresentative
  field_simp [hz]
  all_goals ring
theorem saddleGaussianPoleShiftedSlope_differentiable
    (n : ℕ) :
    Differentiable ℂ
      (fun z : ℂ =>
        saddleGaussianPoleSlope
          (z + ((2 * n : ℕ) : ℂ))) :=
  saddleGaussianPoleSlope_differentiable.comp
    (by fun_prop)
theorem saddleGaussianPoleShiftedSlope_boundary_rectangle
    (n : ℕ) (A B T : ℝ) :
    (∫ a in A..B,
      saddleGaussianPoleSlope
        ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ))) -
    (∫ a in A..B,
      saddleGaussianPoleSlope
        ((a : ℂ) + (T : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ))) +
    Complex.I *
      (∫ t in -T..T,
        saddleGaussianPoleSlope
          ((B : ℂ) + (t : ℂ) * Complex.I +
            ((2 * n : ℕ) : ℂ))) -
    Complex.I *
      (∫ t in -T..T,
        saddleGaussianPoleSlope
          ((A : ℂ) + (t : ℂ) * Complex.I +
            ((2 * n : ℕ) : ℂ))) = 0 := by
  have hrectangle :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (fun z : ℂ =>
        saddleGaussianPoleSlope
          (z + ((2 * n : ℕ) : ℂ)))
      ((A : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
      ((B : ℂ) + (T : ℂ) * Complex.I)
      (saddleGaussianPoleShiftedSlope_differentiable
        n).differentiableOn
  simpa [Complex.mul_re, Complex.mul_im, smul_eq_mul] using! hrectangle
theorem saddleGaussianPoleShiftedSlope_horizontalIntegral_tendsto_zero
    {A B : ℝ} (hAB : A ≤ B)
    (n : ℕ) (s : ℝ) (hs : |s| = 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleGaussianPoleSlope
            ((a : ℂ) +
              ((s * T : ℝ) : ℂ) * Complex.I +
                ((2 * n : ℕ) : ℂ)))
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC, hgaussian⟩ :=
    saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound
      (r := 1) (by norm_num : (0 : ℝ) < 1) hAB n
  apply saddleHorizontalIntegral_tendsto_zero
    (F := fun z : ℂ =>
      saddleGaussianPoleSlope
        (z + ((2 * n : ℕ) : ℂ)))
    hAB (C := C + 1) ?_ s hs
  intro a ha t ht
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  let q : ℂ := z + ((2 * n : ℕ) : ℂ)
  have hden : |t| ≤ ‖q‖ := by
    try dsimp [q, z]
    simpa [Complex.mul_im] using!
      (Complex.abs_im_le_norm
        ((a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)))
  have hqpos : 0 < ‖q‖ :=
    (lt_of_lt_of_le zero_lt_one ht).trans_le hden
  have hq : q ≠ 0 := norm_pos_iff.mp hqpos
  have hpole : |t| * ‖q⁻¹‖ ≤ 1 := by
    rw [norm_inv, ← div_eq_mul_inv]
    exact (div_le_one hqpos).2 hden
  have hgaussian' :
      |t| * ‖saddleGaussianPoleRepresentative n z‖ ≤ C := by
    simpa [saddleMellinInversePower, z] using!
      hgaussian a ha t ht
  have hslope :
      saddleGaussianPoleSlope q =
        saddleGaussianPoleRepresentative n z - q⁻¹ := by
    have hsplit :=
      saddleGaussianPoleRepresentative_eq_inv_add_slope
        n (z := z)
        (show z + ((2 * n : ℕ) : ℂ) ≠ 0 from hq)
    change saddleGaussianPoleRepresentative n z =
      q⁻¹ + saddleGaussianPoleSlope q at hsplit
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm, q, z] using! hsplit.symm
  change |t| * ‖saddleGaussianPoleSlope q‖ ≤ C + 1
  rw [hslope]
  calc
    |t| *
        ‖saddleGaussianPoleRepresentative n z - q⁻¹‖ ≤
      |t| *
        (‖saddleGaussianPoleRepresentative n z‖ +
          ‖q⁻¹‖) := by
        gcongr
        exact norm_sub_le _ _
    _ = |t| * ‖saddleGaussianPoleRepresentative n z‖ +
      |t| * ‖q⁻¹‖ := by
        ring
    _ ≤ C + 1 := add_le_add hgaussian' hpole
theorem saddleInfiniteRectangle_vertical_limit_eq
    {F : ℂ → ℂ} {A B : ℝ} {u v : ℂ}
    (hleft : Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          F ((A : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop (𝓝 u))
    (hright : Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          F ((B : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop (𝓝 v))
    (hlower : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0))
    (hupper : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          F ((a : ℂ) + (T : ℂ) * Complex.I))
      Filter.atTop (𝓝 0))
    (hrectangle : ∀ T : ℝ,
      (∫ a in A..B,
        F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
      (∫ a in A..B,
        F ((a : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I *
        (∫ t in -T..T,
          F ((B : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I *
        (∫ t in -T..T,
          F ((A : ℂ) + (t : ℂ) * Complex.I)) = 0) :
    v = u := by
  have hlimit : Tendsto
      (fun T : ℝ =>
        (∫ a in A..B,
          F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
        (∫ a in A..B,
          F ((a : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I *
          (∫ t in -T..T,
            F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I *
          (∫ t in -T..T,
            F ((A : ℂ) + (t : ℂ) * Complex.I)))
      Filter.atTop (𝓝 (Complex.I * v - Complex.I * u)) := by
    simpa using!
      (((hlower.sub hupper).add
        (tendsto_const_nhds.mul hright)).sub
          (tendsto_const_nhds.mul hleft))
  have hzero : Tendsto
      (fun T : ℝ =>
        (∫ a in A..B,
          F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
        (∫ a in A..B,
          F ((a : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I *
          (∫ t in -T..T,
            F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I *
          (∫ t in -T..T,
            F ((A : ℂ) + (t : ℂ) * Complex.I)))
      Filter.atTop (𝓝 0) :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (0 : ℂ))
        Filter.atTop (𝓝 0)).congr'
          (Filter.Eventually.of_forall
            (fun T : ℝ => (hrectangle T).symm))
  have hidentity : Complex.I * (v - u) = 0 := by
    simpa [mul_sub] using!
      (tendsto_nhds_unique hlimit hzero)
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hidentity).resolve_left
      Complex.I_ne_zero)
theorem saddleGaussianPoleShiftedSlope_symmetric_intervalIntegral
    (n : ℕ) {a : ℝ}
    (ha : a ≠ -((2 * n : ℕ) : ℝ)) (T : ℝ) :
    (∫ t in -T..T,
      saddleGaussianPoleSlope
        ((a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ))) =
    (∫ t in -T..T,
      saddleGaussianPoleRepresentative n
        ((a : ℂ) + (t : ℂ) * Complex.I)) -
    (∫ t in -T..T,
      (((a : ℂ) + (t : ℂ) * Complex.I +
        ((2 * n : ℕ) : ℂ))⁻¹)) := by
  have hline : Continuous
      (fun t : ℝ =>
        (a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)) := by
    fun_prop
  have hnonzero : ∀ t : ℝ,
      (a : ℂ) + (t : ℂ) * Complex.I +
        ((2 * n : ℕ) : ℂ) ≠ 0 := by
    intro t hzero
    apply ha
    have hre := congrArg Complex.re hzero
    norm_num [Complex.mul_re] at hre
    push_cast
    linarith
  have hgaussian : IntervalIntegrable
      (fun t : ℝ =>
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I))
      volume (-T) T :=
    (saddleGaussianPoleRepresentative_shiftedLine_continuous
      n ha).intervalIntegrable _ _
  have hpole : IntervalIntegrable
      (fun t : ℝ =>
        (((a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ))⁻¹))
      volume (-T) T :=
    (hline.inv₀ hnonzero).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hgaussian hpole]
  apply intervalIntegral.integral_congr
  intro t _
  have hsplit :=
    saddleGaussianPoleRepresentative_eq_inv_add_slope
      n (hnonzero t)
  apply (eq_sub_iff_add_eq).2
  simpa [add_comm] using! hsplit.symm
theorem saddleGaussianPoleShiftedSlope_symmetric_intervalIntegral_tendsto_pos
    (n : ℕ) {a : ℝ}
    (ha : -((2 * n : ℕ) : ℝ) < a) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          saddleGaussianPoleSlope
            ((a : ℂ) + (t : ℂ) * Complex.I +
              ((2 * n : ℕ) : ℂ)))
      Filter.atTop
      (𝓝 ((∫ t : ℝ,
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I)) -
        (Real.pi : ℂ))) := by
  have hane : a ≠ -((2 * n : ℕ) : ℝ) :=
    ne_of_gt ha
  have hgaussian : Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          saddleGaussianPoleRepresentative n
            ((a : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (𝓝 (∫ t : ℝ,
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral
      (saddleGaussianPoleRepresentative_shiftedLine_integrable
        n hane)
      tendsto_neg_atTop_atBot tendsto_id
  have hpole :=
    saddleShiftedCauchyPole_symmetric_intervalIntegral_tendsto_pos
      n ha
  exact (hgaussian.sub hpole).congr'
    (Filter.Eventually.of_forall
      (fun T : ℝ =>
        (saddleGaussianPoleShiftedSlope_symmetric_intervalIntegral
          n hane T).symm))
theorem saddleGaussianPoleShiftedSlope_symmetric_intervalIntegral_tendsto_neg
    (n : ℕ) {a : ℝ}
    (ha : a < -((2 * n : ℕ) : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          saddleGaussianPoleSlope
            ((a : ℂ) + (t : ℂ) * Complex.I +
              ((2 * n : ℕ) : ℂ)))
      Filter.atTop
      (𝓝 ((∫ t : ℝ,
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I)) -
        (-(Real.pi : ℂ)))) := by
  have hane : a ≠ -((2 * n : ℕ) : ℝ) :=
    ne_of_lt ha
  have hgaussian : Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          saddleGaussianPoleRepresentative n
            ((a : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (𝓝 (∫ t : ℝ,
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral
      (saddleGaussianPoleRepresentative_shiftedLine_integrable
        n hane)
      tendsto_neg_atTop_atBot tendsto_id
  have hpole :=
    saddleShiftedCauchyPole_symmetric_intervalIntegral_tendsto_neg
      n ha
  exact (hgaussian.sub hpole).congr'
    (Filter.Eventually.of_forall
      (fun T : ℝ =>
        (saddleGaussianPoleShiftedSlope_symmetric_intervalIntegral
          n hane T).symm))
theorem saddleGaussianPoleRepresentative_vertical_integral_jump
    (n : ℕ) {A B : ℝ}
    (hA : A < -((2 * n : ℕ) : ℝ))
    (hB : -((2 * n : ℕ) : ℝ) < B) :
    (∫ t : ℝ,
      saddleGaussianPoleRepresentative n
        ((B : ℂ) + (t : ℂ) * Complex.I)) -
    (∫ t : ℝ,
      saddleGaussianPoleRepresentative n
        ((A : ℂ) + (t : ℂ) * Complex.I)) =
      ((2 * Real.pi : ℝ) : ℂ) := by
  have hAB : A ≤ B := (hA.trans hB).le
  have hleft :=
    saddleGaussianPoleShiftedSlope_symmetric_intervalIntegral_tendsto_neg
      n hA
  have hright :=
    saddleGaussianPoleShiftedSlope_symmetric_intervalIntegral_tendsto_pos
      n hB
  have hlower : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleGaussianPoleSlope
            ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I +
              ((2 * n : ℕ) : ℂ)))
      Filter.atTop (𝓝 0) := by
    simpa using!
      saddleGaussianPoleShiftedSlope_horizontalIntegral_tendsto_zero
        hAB n (-1) (by norm_num)
  have hupper : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleGaussianPoleSlope
            ((a : ℂ) + (T : ℂ) * Complex.I +
              ((2 * n : ℕ) : ℂ)))
      Filter.atTop (𝓝 0) := by
    simpa using!
      saddleGaussianPoleShiftedSlope_horizontalIntegral_tendsto_zero
        hAB n 1 (by norm_num)
  have hidentity :=
    saddleInfiniteRectangle_vertical_limit_eq
      (F := fun z : ℂ =>
        saddleGaussianPoleSlope
          (z + ((2 * n : ℕ) : ℂ)))
      hleft hright hlower hupper
      (fun T : ℝ =>
        saddleGaussianPoleShiftedSlope_boundary_rectangle
          n A B T)
  push_cast
  linear_combination hidentity
theorem saddleMellinInversePower_negativeEvenPole
    (r : ℝ) (n : ℕ) :
    saddleMellinInversePower r
      (-((2 * n : ℕ) : ℂ)) =
      ((r ^ (2 * n) : ℝ) : ℂ) := by
  unfold saddleMellinInversePower
  rw [neg_neg, Complex.cpow_natCast]
  exact (Complex.ofReal_pow r (2 * n)).symm
def saddleMellinInversePowerPoleSlope
    (r : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  dslope (saddleMellinInversePower r)
    (-((2 * n : ℕ) : ℂ)) z
theorem saddleMellinInversePowerPoleSlope_differentiable
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Differentiable ℂ
      (saddleMellinInversePowerPoleSlope r n) := by
  unfold saddleMellinInversePowerPoleSlope
  exact differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope
      (s := Set.univ)
      (c := -((2 * n : ℕ) : ℂ))
      (show Set.univ ∈ 𝓝 (-((2 * n : ℕ) : ℂ))
        from univ_mem)).mpr
      (saddleMellinInversePower_differentiable
        hr).differentiableOn)
def saddleGaussianPoleWeightedCorrection
    (r : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ((z + ((2 * n : ℕ) : ℂ)) ^ 2) *
    saddleMellinInversePowerPoleSlope r n z
theorem saddleGaussianPoleWeightedCorrection_differentiable
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Differentiable ℂ
      (saddleGaussianPoleWeightedCorrection r n) := by
  unfold saddleGaussianPoleWeightedCorrection
  have hgaussian : Differentiable ℂ
      (fun z : ℂ =>
        Complex.exp ((z + ((2 * n : ℕ) : ℂ)) ^ 2)) := by
    fun_prop
  exact hgaussian.mul
    (saddleMellinInversePowerPoleSlope_differentiable
      hr n)
theorem saddleGaussianPoleWeightedRepresentative_eq_pole_add_correction
    {r : ℝ} (n : ℕ) {z : ℂ}
    (hz : z + ((2 * n : ℕ) : ℂ) ≠ 0) :
    saddleMellinInversePower r z *
        saddleGaussianPoleRepresentative n z =
      saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        saddleGaussianPoleRepresentative n z +
      saddleGaussianPoleWeightedCorrection r n z := by
  let p : ℂ := -((2 * n : ℕ) : ℂ)
  let q : ℂ := z + ((2 * n : ℕ) : ℂ)
  have hslope :=
    sub_smul_dslope (saddleMellinInversePower r) p z
  have hcoordinate : z - p = q := by
    try dsimp [p, q]
    ring
  rw [hcoordinate, smul_eq_mul] at hslope
  have hdiv :
      saddleMellinInversePowerPoleSlope r n z =
        (saddleMellinInversePower r z -
          saddleMellinInversePower r p) / q := by
    apply (eq_div_iff (show q ≠ 0 from hz)).2
    unfold saddleMellinInversePowerPoleSlope
    change dslope (saddleMellinInversePower r) p z * q =
      saddleMellinInversePower r z -
        saddleMellinInversePower r p
    simpa [mul_comm] using! hslope
  unfold saddleGaussianPoleRepresentative
    saddleGaussianPoleWeightedCorrection
  change saddleMellinInversePower r z *
      (Complex.exp (q ^ 2) / q) =
    saddleMellinInversePower r p *
        (Complex.exp (q ^ 2) / q) +
      Complex.exp (q ^ 2) *
        saddleMellinInversePowerPoleSlope r n z
  rw [hdiv]
  field_simp [hz]
  all_goals ring
theorem saddleGaussianPole_shiftedLine_ne_zero
    (n : ℕ) {a : ℝ}
    (ha : a ≠ -((2 * n : ℕ) : ℝ))
    (t : ℝ) :
    (a : ℂ) + (t : ℂ) * Complex.I +
      ((2 * n : ℕ) : ℂ) ≠ 0 := by
  intro hzero
  apply ha
  have hre := congrArg Complex.re hzero
  norm_num [Complex.mul_re] at hre
  push_cast
  linarith
theorem saddleGaussianPoleWeightedCorrection_eq_sub
    {r : ℝ} (n : ℕ) {z : ℂ}
    (hz : z + ((2 * n : ℕ) : ℂ) ≠ 0) :
    saddleGaussianPoleWeightedCorrection r n z =
      saddleMellinInversePower r z *
        saddleGaussianPoleRepresentative n z -
      saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        saddleGaussianPoleRepresentative n z := by
  have hsplit :=
    saddleGaussianPoleWeightedRepresentative_eq_pole_add_correction
      (r := r) n hz
  apply (eq_sub_iff_add_eq).2
  simpa [add_comm] using! hsplit.symm
theorem saddleGaussianPoleWeightedCorrection_shiftedLine_integrable
    {r a : ℝ} (hr : 0 < r)
    (n : ℕ) (ha : a ≠ -((2 * n : ℕ) : ℝ)) :
    Integrable (fun t : ℝ =>
      saddleGaussianPoleWeightedCorrection r n
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hweighted :=
    saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable
      n ha hr
  have hunweighted :=
    saddleGaussianPoleRepresentative_shiftedLine_integrable n ha
  have hconstant :=
    hunweighted.const_mul
      (saddleMellinInversePower r
        (-((2 * n : ℕ) : ℂ)))
  apply (hweighted.sub hconstant).congr
  filter_upwards [] with t
  exact
    (saddleGaussianPoleWeightedCorrection_eq_sub
      n (saddleGaussianPole_shiftedLine_ne_zero
        n ha t)).symm
theorem saddleGaussianPoleWeightedCorrection_horizontalStrip_bound
    {r A B : ℝ} (hr : 0 < r) (hAB : A ≤ B)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| *
            ‖saddleGaussianPoleWeightedCorrection r n
              ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨Cw, hCw, hweighted⟩ :=
    saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound
      hr hAB n
  obtain ⟨Cu, hCu, hunweighted⟩ :=
    saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound
      (r := 1) (by norm_num : (0 : ℝ) < 1) hAB n
  let p : ℂ := -((2 * n : ℕ) : ℂ)
  refine ⟨Cw + ‖saddleMellinInversePower r p‖ * Cu,
    by positivity, ?_⟩
  intro a ha t ht
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  let q : ℂ := z + ((2 * n : ℕ) : ℂ)
  have hden : |t| ≤ ‖q‖ := by
    try dsimp [q, z]
    simpa [Complex.mul_im] using!
      (Complex.abs_im_le_norm
        ((a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)))
  have hqpos : 0 < ‖q‖ :=
    (lt_of_lt_of_le zero_lt_one ht).trans_le hden
  have hq : q ≠ 0 := norm_pos_iff.mp hqpos
  have hweighted' :
      |t| *
        ‖saddleMellinInversePower r z *
          saddleGaussianPoleRepresentative n z‖ ≤ Cw := by
    simpa [z] using! hweighted a ha t ht
  have hunweighted' :
      |t| * ‖saddleGaussianPoleRepresentative n z‖ ≤ Cu := by
    simpa [saddleMellinInversePower, z] using!
      hunweighted a ha t ht
  have hscaled :
      |t| *
        ‖saddleMellinInversePower r p *
          saddleGaussianPoleRepresentative n z‖ ≤
        ‖saddleMellinInversePower r p‖ * Cu := by
    rw [norm_mul]
    calc
      |t| *
          (‖saddleMellinInversePower r p‖ *
            ‖saddleGaussianPoleRepresentative n z‖) =
        ‖saddleMellinInversePower r p‖ *
          (|t| * ‖saddleGaussianPoleRepresentative n z‖) := by
          ring
      _ ≤ ‖saddleMellinInversePower r p‖ * Cu :=
        mul_le_mul_of_nonneg_left hunweighted'
          (norm_nonneg _)
  have hcorrection :=
    saddleGaussianPoleWeightedCorrection_eq_sub
      (r := r) n (z := z)
      (show z + ((2 * n : ℕ) : ℂ) ≠ 0 from hq)
  change |t| * ‖saddleGaussianPoleWeightedCorrection r n z‖ ≤
    Cw + ‖saddleMellinInversePower r p‖ * Cu
  rw [hcorrection]
  change |t| *
      ‖saddleMellinInversePower r z *
        saddleGaussianPoleRepresentative n z -
        saddleMellinInversePower r p *
          saddleGaussianPoleRepresentative n z‖ ≤
    Cw + ‖saddleMellinInversePower r p‖ * Cu
  calc
    |t| *
        ‖saddleMellinInversePower r z *
          saddleGaussianPoleRepresentative n z -
          saddleMellinInversePower r p *
            saddleGaussianPoleRepresentative n z‖ ≤
      |t| *
        (‖saddleMellinInversePower r z *
            saddleGaussianPoleRepresentative n z‖ +
          ‖saddleMellinInversePower r p *
            saddleGaussianPoleRepresentative n z‖) := by
        gcongr
        exact norm_sub_le _ _
    _ = |t| *
          ‖saddleMellinInversePower r z *
            saddleGaussianPoleRepresentative n z‖ +
        |t| *
          ‖saddleMellinInversePower r p *
            saddleGaussianPoleRepresentative n z‖ := by
        ring
    _ ≤ Cw + ‖saddleMellinInversePower r p‖ * Cu :=
      add_le_add hweighted' hscaled
theorem saddleGaussianPoleWeightedCorrection_horizontalIntegral_tendsto_zero
    {r A B : ℝ} (hr : 0 < r) (hAB : A ≤ B)
    (n : ℕ) (s : ℝ) (hs : |s| = 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleGaussianPoleWeightedCorrection r n
            ((a : ℂ) +
              ((s * T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    saddleGaussianPoleWeightedCorrection_horizontalStrip_bound
      hr hAB n
  exact saddleHorizontalIntegral_tendsto_zero
    (F := saddleGaussianPoleWeightedCorrection r n)
    hAB hbound s hs
theorem saddleGaussianPoleWeightedCorrection_boundary_rectangle
    {r : ℝ} (hr : 0 < r)
    (n : ℕ) (A B T : ℝ) :
    (∫ a in A..B,
      saddleGaussianPoleWeightedCorrection r n
        ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
    (∫ a in A..B,
      saddleGaussianPoleWeightedCorrection r n
        ((a : ℂ) + (T : ℂ) * Complex.I)) +
    Complex.I *
      (∫ t in -T..T,
        saddleGaussianPoleWeightedCorrection r n
          ((B : ℂ) + (t : ℂ) * Complex.I)) -
    Complex.I *
      (∫ t in -T..T,
        saddleGaussianPoleWeightedCorrection r n
          ((A : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
  have hrectangle :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (saddleGaussianPoleWeightedCorrection r n)
      ((A : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
      ((B : ℂ) + (T : ℂ) * Complex.I)
      (saddleGaussianPoleWeightedCorrection_differentiable
        hr n).differentiableOn
  simpa [Complex.mul_re, Complex.mul_im, smul_eq_mul] using! hrectangle
theorem saddleGaussianPoleWeightedCorrection_vertical_integral_eq
    {r A B : ℝ} (hr : 0 < r)
    (n : ℕ) (hAB : A ≤ B)
    (hA : A ≠ -((2 * n : ℕ) : ℝ))
    (hB : B ≠ -((2 * n : ℕ) : ℝ)) :
    (∫ t : ℝ,
      saddleGaussianPoleWeightedCorrection r n
        ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      saddleGaussianPoleWeightedCorrection r n
        ((A : ℂ) + (t : ℂ) * Complex.I)) := by
  have hleft :=
    saddleGaussianPoleWeightedCorrection_shiftedLine_integrable
      hr n hA
  have hright :=
    saddleGaussianPoleWeightedCorrection_shiftedLine_integrable
      hr n hB
  have hlower : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleGaussianPoleWeightedCorrection r n
            ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
    simpa using!
      saddleGaussianPoleWeightedCorrection_horizontalIntegral_tendsto_zero
        hr hAB n (-1) (by norm_num)
  have hupper : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleGaussianPoleWeightedCorrection r n
            ((a : ℂ) + (T : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
    simpa using!
      saddleGaussianPoleWeightedCorrection_horizontalIntegral_tendsto_zero
        hr hAB n 1 (by norm_num)
  exact saddleInfiniteRectangle_vertical_integral_eq
    hleft hright hlower hupper
    (fun T : ℝ =>
      saddleGaussianPoleWeightedCorrection_boundary_rectangle
        hr n A B T)
theorem saddleGaussianPoleWeightedRepresentative_shiftedLine_integral_eq
    {r a : ℝ} (hr : 0 < r)
    (n : ℕ) (ha : a ≠ -((2 * n : ℕ) : ℝ)) :
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I)) =
      saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        (∫ t : ℝ,
          saddleGaussianPoleRepresentative n
            ((a : ℂ) + (t : ℂ) * Complex.I)) +
        (∫ t : ℝ,
          saddleGaussianPoleWeightedCorrection r n
            ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hrepresentative :=
    saddleGaussianPoleRepresentative_shiftedLine_integrable n ha
  have hconstant :=
    hrepresentative.const_mul
      (saddleMellinInversePower r
        (-((2 * n : ℕ) : ℂ)))
  have hcorrection :=
    saddleGaussianPoleWeightedCorrection_shiftedLine_integrable
      hr n ha
  calc
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ,
        saddleMellinInversePower r
            (-((2 * n : ℕ) : ℂ)) *
          saddleGaussianPoleRepresentative n
            ((a : ℂ) + (t : ℂ) * Complex.I) +
          saddleGaussianPoleWeightedCorrection r n
            ((a : ℂ) + (t : ℂ) * Complex.I) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with t
          exact
            saddleGaussianPoleWeightedRepresentative_eq_pole_add_correction
              (r := r) n
              (saddleGaussianPole_shiftedLine_ne_zero
                n ha t)
    _ =
      (∫ t : ℝ,
        saddleMellinInversePower r
            (-((2 * n : ℕ) : ℂ)) *
          saddleGaussianPoleRepresentative n
            ((a : ℂ) + (t : ℂ) * Complex.I)) +
      (∫ t : ℝ,
        saddleGaussianPoleWeightedCorrection r n
          ((a : ℂ) + (t : ℂ) * Complex.I)) :=
      integral_add hconstant hcorrection
    _ =
      saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        (∫ t : ℝ,
          saddleGaussianPoleRepresentative n
            ((a : ℂ) + (t : ℂ) * Complex.I)) +
      (∫ t : ℝ,
        saddleGaussianPoleWeightedCorrection r n
          ((a : ℂ) + (t : ℂ) * Complex.I)) := by
        rw [integral_const_mul_of_integrable hrepresentative]
theorem saddleGaussianPoleWeightedRepresentative_vertical_integral_jump
    {r A B : ℝ} (hr : 0 < r)
    (n : ℕ)
    (hA : A < -((2 * n : ℕ) : ℝ))
    (hB : -((2 * n : ℕ) : ℝ) < B) :
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((B : ℂ) + (t : ℂ) * Complex.I) *
        saddleGaussianPoleRepresentative n
          ((B : ℂ) + (t : ℂ) * Complex.I)) -
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((A : ℂ) + (t : ℂ) * Complex.I) *
        saddleGaussianPoleRepresentative n
          ((A : ℂ) + (t : ℂ) * Complex.I)) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((r ^ (2 * n) : ℝ) : ℂ) := by
  have hAB : A ≤ B := (hA.trans hB).le
  have hAne : A ≠ -((2 * n : ℕ) : ℝ) :=
    ne_of_lt hA
  have hBne : B ≠ -((2 * n : ℕ) : ℝ) :=
    ne_of_gt hB
  rw [saddleGaussianPoleWeightedRepresentative_shiftedLine_integral_eq
    hr n hBne,
    saddleGaussianPoleWeightedRepresentative_shiftedLine_integral_eq
      hr n hAne]
  have hcorrection :=
    saddleGaussianPoleWeightedCorrection_vertical_integral_eq
      hr n hAB hAne hBne
  have hgaussian :=
    saddleGaussianPoleRepresentative_vertical_integral_jump
      n hA hB
  calc
    saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        (∫ t : ℝ,
          saddleGaussianPoleRepresentative n
            ((B : ℂ) + (t : ℂ) * Complex.I)) +
        (∫ t : ℝ,
          saddleGaussianPoleWeightedCorrection r n
            ((B : ℂ) + (t : ℂ) * Complex.I)) -
      (saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        (∫ t : ℝ,
          saddleGaussianPoleRepresentative n
            ((A : ℂ) + (t : ℂ) * Complex.I)) +
        (∫ t : ℝ,
          saddleGaussianPoleWeightedCorrection r n
            ((A : ℂ) + (t : ℂ) * Complex.I))) =
      saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        ((∫ t : ℝ,
          saddleGaussianPoleRepresentative n
            ((B : ℂ) + (t : ℂ) * Complex.I)) -
          (∫ t : ℝ,
            saddleGaussianPoleRepresentative n
              ((A : ℂ) + (t : ℂ) * Complex.I))) := by
        rw [hcorrection]
        ring
    _ = saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        ((2 * Real.pi : ℝ) : ℂ) := by
        rw [hgaussian]
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        ((r ^ (2 * n) : ℝ) : ℂ) := by
        rw [saddleMellinInversePower_negativeEvenPole]
        ring
theorem saddleFiniteGaussianPoleWeighted_shiftedLine_integrable
    {r a : ℝ} (hr : 0 < r)
    (c : ℕ → ℂ) (N : ℕ)
    (ha : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ)) :
    Integrable (fun t : ℝ =>
      ∑ n ∈ Finset.range (N + 1),
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          (c n *
            saddleGaussianPoleRepresentative n
              ((a : ℂ) + (t : ℂ) * Complex.I))) := by
  apply integrable_finsetSum
  intro n _
  have hterm :=
    (saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable
      n (ha n) hr).const_mul (c n)
  exact hterm.congr
    (Filter.Eventually.of_forall
      (fun t : ℝ => by ring))
theorem saddleFiniteGaussianPoleWeighted_shiftedLine_integral
    {r a : ℝ} (hr : 0 < r)
    (c : ℕ → ℂ) (N : ℕ)
    (ha : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ)) :
    (∫ t : ℝ,
      ∑ n ∈ Finset.range (N + 1),
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          (c n *
            saddleGaussianPoleRepresentative n
              ((a : ℂ) + (t : ℂ) * Complex.I))) =
      ∑ n ∈ Finset.range (N + 1),
        c n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hterm (n : ℕ) :
      Integrable (fun t : ℝ =>
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          (c n *
            saddleGaussianPoleRepresentative n
              ((a : ℂ) + (t : ℂ) * Complex.I))) := by
    have h :=
      (saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable
        n (ha n) hr).const_mul (c n)
    exact h.congr
      (Filter.Eventually.of_forall
        (fun t : ℝ => by ring))
  rw [MeasureTheory.integral_finsetSum
    (Finset.range (N + 1))
      (fun n _ => hterm n)]
  apply Finset.sum_congr rfl
  intro n _
  have hweighted :=
    saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable
      n (ha n) hr
  calc
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        (c n *
          saddleGaussianPoleRepresentative n
            ((a : ℂ) + (t : ℂ) * Complex.I))) =
      ∫ t : ℝ,
        c n *
          (saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
            saddleGaussianPoleRepresentative n
              ((a : ℂ) + (t : ℂ) * Complex.I)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with t
        ring
    _ = c n *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
            saddleGaussianPoleRepresentative n
              ((a : ℂ) + (t : ℂ) * Complex.I)) :=
      integral_const_mul_of_integrable hweighted
theorem plusSaddleFiniteRapidContourIntegrand_shiftedLine_integral_eq
    {ε ℓ a r : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < a)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ)) :
    (∫ t : ℝ,
      plusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          plusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)) -
      ∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hdata :=
    plusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder hpole hr
  have hsum :=
    saddleFiniteGaussianPoleWeighted_shiftedLine_integrable
      hr (plusSaddlePoleResidue ε ℓ) N hpole
  calc
    (∫ t : ℝ,
      plusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ,
        saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
          plusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I) -
        ∑ n ∈ Finset.range (N + 1),
          saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
            (plusSaddlePoleResidue ε ℓ n *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with t
          have hz :
              (a : ℂ) + (t : ℂ) * Complex.I ∈
                saddleFinitePoleHalfPlane N := by
            change -(2 * ((N : ℝ) + 1)) <
              ((a : ℂ) + (t : ℂ) * Complex.I).re
            simpa [Complex.mul_re] using! hhalf
          unfold plusSaddleFiniteRapidContourIntegrand
          rw [plusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
            hε horder ℓ N hz
              (saddleShiftedLine_ne_pole hpole t)]
          unfold plusSaddleFiniteRapidPoleSubtraction
          rw [mul_sub, Finset.mul_sum]
    _ =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          plusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t : ℝ,
        ∑ n ∈ Finset.range (N + 1),
          saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
            (plusSaddlePoleResidue ε ℓ n *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I))) :=
      MeasureTheory.integral_sub hdata hsum
    _ =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          plusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)) -
      ∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)) := by
        rw [saddleFiniteGaussianPoleWeighted_shiftedLine_integral
          hr (plusSaddlePoleResidue ε ℓ) N hpole]
theorem minusSaddleFiniteRapidContourIntegrand_shiftedLine_integral_eq
    {ε ℓ a r : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < a)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ)) :
    (∫ t : ℝ,
      minusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          minusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)) -
      ∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hdata :=
    minusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder hpole hr
  have hsum :=
    saddleFiniteGaussianPoleWeighted_shiftedLine_integrable
      hr (minusSaddlePoleResidue ε ℓ) N hpole
  calc
    (∫ t : ℝ,
      minusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ,
        saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
          minusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I) -
        ∑ n ∈ Finset.range (N + 1),
          saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
            (minusSaddlePoleResidue ε ℓ n *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with t
          have hz :
              (a : ℂ) + (t : ℂ) * Complex.I ∈
                saddleFinitePoleHalfPlane N := by
            change -(2 * ((N : ℝ) + 1)) <
              ((a : ℂ) + (t : ℂ) * Complex.I).re
            simpa [Complex.mul_re] using! hhalf
          unfold minusSaddleFiniteRapidContourIntegrand
          rw [minusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
            hε horder ℓ N hz
              (saddleShiftedLine_ne_pole hpole t)]
          unfold minusSaddleFiniteRapidPoleSubtraction
          rw [mul_sub, Finset.mul_sum]
    _ =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          minusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t : ℝ,
        ∑ n ∈ Finset.range (N + 1),
          saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
            (minusSaddlePoleResidue ε ℓ n *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I))) :=
      MeasureTheory.integral_sub hdata hsum
    _ =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          minusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)) -
      ∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)) := by
        rw [saddleFiniteGaussianPoleWeighted_shiftedLine_integral
          hr (minusSaddlePoleResidue ε ℓ) N hpole]
theorem saddleFiniteGaussianPoleWeighted_vertical_integral_jump
    {r A B : ℝ} (hr : 0 < r)
    (c : ℕ → ℂ) (N : ℕ)
    (hcross : ∀ n ∈ Finset.range (N + 1),
      A < -((2 * n : ℕ) : ℝ) ∧
        -((2 * n : ℕ) : ℝ) < B) :
    (∑ n ∈ Finset.range (N + 1),
      c n *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((B : ℂ) + (t : ℂ) * Complex.I) *
            saddleGaussianPoleRepresentative n
              ((B : ℂ) + (t : ℂ) * Complex.I))) -
    (∑ n ∈ Finset.range (N + 1),
      c n *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((A : ℂ) + (t : ℂ) * Complex.I) *
            saddleGaussianPoleRepresentative n
              ((A : ℂ) + (t : ℂ) * Complex.I))) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ∑ n ∈ Finset.range (N + 1),
          c n * ((r ^ (2 * n) : ℝ) : ℂ) := by
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ n ∈ Finset.range (N + 1),
      (c n *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((B : ℂ) + (t : ℂ) * Complex.I) *
            saddleGaussianPoleRepresentative n
              ((B : ℂ) + (t : ℂ) * Complex.I)) -
       c n *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((A : ℂ) + (t : ℂ) * Complex.I) *
            saddleGaussianPoleRepresentative n
              ((A : ℂ) + (t : ℂ) * Complex.I)))) =
      ∑ n ∈ Finset.range (N + 1),
        c n *
          ((∫ t : ℝ,
            saddleMellinInversePower r
              ((B : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((B : ℂ) + (t : ℂ) * Complex.I)) -
           (∫ t : ℝ,
            saddleMellinInversePower r
              ((A : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((A : ℂ) + (t : ℂ) * Complex.I))) := by
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ =
      ∑ n ∈ Finset.range (N + 1),
        c n *
          (((2 * Real.pi : ℝ) : ℂ) *
            ((r ^ (2 * n) : ℝ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [saddleGaussianPoleWeightedRepresentative_vertical_integral_jump
          hr n (hcross n hn).1 (hcross n hn).2]
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        ∑ n ∈ Finset.range (N + 1),
          c n * ((r ^ (2 * n) : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
theorem plusSaddleMellinData_vertical_integral_residue_expansion
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B)
    (hApole : ∀ n : ℕ, A ≠ -((2 * n : ℕ) : ℝ))
    (hBpole : ∀ n : ℕ, B ≠ -((2 * n : ℕ) : ℝ))
    (hcross : ∀ n ∈ Finset.range (N + 1),
      A < -((2 * n : ℕ) : ℝ) ∧
        -((2 * n : ℕ) : ℝ) < B) :
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((B : ℂ) + (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((A : ℂ) + (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((A : ℂ) + (t : ℂ) * Complex.I)) +
      ((2 * Real.pi : ℝ) : ℂ) *
        ∑ n ∈ Finset.range (N + 1),
          plusSaddlePoleResidue ε ℓ n *
            ((r ^ (2 * n) : ℝ) : ℂ) := by
  have hhalfB : -(2 * ((N : ℝ) + 1)) < B :=
    hhalf.trans_le hAB
  have hcontour :=
    plusSaddleFiniteRapidContourIntegrand_vertical_integral_eq
      hε hℓ horder hr N hhalf hAB hApole hBpole
  rw [plusSaddleFiniteRapidContourIntegrand_shiftedLine_integral_eq
        hε hℓ horder hr N hhalfB hBpole,
      plusSaddleFiniteRapidContourIntegrand_shiftedLine_integral_eq
        hε hℓ horder hr N hhalf hApole]
    at hcontour
  have hsum :=
    saddleFiniteGaussianPoleWeighted_vertical_integral_jump
      hr (plusSaddlePoleResidue ε ℓ) N hcross
  calc
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((B : ℂ) + (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((B : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((A : ℂ) + (t : ℂ) * Complex.I) *
          plusSaddleMellinData ε ℓ
            ((A : ℂ) + (t : ℂ) * Complex.I)) +
      ((∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((B : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((B : ℂ) + (t : ℂ) * Complex.I))) -
       (∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((A : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((A : ℂ) + (t : ℂ) * Complex.I)))) := by
        linear_combination hcontour
    _ =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((A : ℂ) + (t : ℂ) * Complex.I) *
          plusSaddleMellinData ε ℓ
            ((A : ℂ) + (t : ℂ) * Complex.I)) +
        ((2 * Real.pi : ℝ) : ℂ) *
          ∑ n ∈ Finset.range (N + 1),
            plusSaddlePoleResidue ε ℓ n *
              ((r ^ (2 * n) : ℝ) : ℂ) := by
          rw [hsum]
theorem minusSaddleMellinData_vertical_integral_residue_expansion
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B)
    (hApole : ∀ n : ℕ, A ≠ -((2 * n : ℕ) : ℝ))
    (hBpole : ∀ n : ℕ, B ≠ -((2 * n : ℕ) : ℝ))
    (hcross : ∀ n ∈ Finset.range (N + 1),
      A < -((2 * n : ℕ) : ℝ) ∧
        -((2 * n : ℕ) : ℝ) < B) :
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((B : ℂ) + (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((A : ℂ) + (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((A : ℂ) + (t : ℂ) * Complex.I)) +
      ((2 * Real.pi : ℝ) : ℂ) *
        ∑ n ∈ Finset.range (N + 1),
          minusSaddlePoleResidue ε ℓ n *
            ((r ^ (2 * n) : ℝ) : ℂ) := by
  have hhalfB : -(2 * ((N : ℝ) + 1)) < B :=
    hhalf.trans_le hAB
  have hcontour :=
    minusSaddleFiniteRapidContourIntegrand_vertical_integral_eq
      hε hℓ horder hr N hhalf hAB hApole hBpole
  rw [minusSaddleFiniteRapidContourIntegrand_shiftedLine_integral_eq
        hε hℓ horder hr N hhalfB hBpole,
      minusSaddleFiniteRapidContourIntegrand_shiftedLine_integral_eq
        hε hℓ horder hr N hhalf hApole]
    at hcontour
  have hsum :=
    saddleFiniteGaussianPoleWeighted_vertical_integral_jump
      hr (minusSaddlePoleResidue ε ℓ) N hcross
  calc
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((B : ℂ) + (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((B : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((A : ℂ) + (t : ℂ) * Complex.I) *
          minusSaddleMellinData ε ℓ
            ((A : ℂ) + (t : ℂ) * Complex.I)) +
      ((∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((B : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((B : ℂ) + (t : ℂ) * Complex.I))) -
       (∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((A : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((A : ℂ) + (t : ℂ) * Complex.I)))) := by
        linear_combination hcontour
    _ =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((A : ℂ) + (t : ℂ) * Complex.I) *
          minusSaddleMellinData ε ℓ
            ((A : ℂ) + (t : ℂ) * Complex.I)) +
        ((2 * Real.pi : ℝ) : ℂ) *
          ∑ n ∈ Finset.range (N + 1),
            minusSaddlePoleResidue ε ℓ n *
              ((r ^ (2 * n) : ℝ) : ℂ) := by
          rw [hsum]
def saddleTaylorContour (N : ℕ) : ℝ :=
  -((2 * N + 1 : ℕ) : ℝ)
theorem saddleTaylorContour_mem_halfPlane (N : ℕ) :
    -(2 * ((N : ℝ) + 1)) < saddleTaylorContour N := by
  unfold saddleTaylorContour
  push_cast
  linarith
theorem saddleTaylorContour_ne_pole (N n : ℕ) :
    saddleTaylorContour N ≠ -((2 * n : ℕ) : ℝ) := by
  intro heq
  unfold saddleTaylorContour at heq
  have hcast :
      ((2 * N + 1 : ℕ) : ℝ) =
        ((2 * n : ℕ) : ℝ) :=
    neg_injective heq
  have hnat : 2 * N + 1 = 2 * n := by
    exact_mod_cast hcast
  omega
theorem saddlePositiveContour_ne_pole
    {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    ℓ ≠ -((2 * n : ℕ) : ℝ) := by
  have hnonpos : -((2 * n : ℕ) : ℝ) ≤ 0 := by
    exact neg_nonpos.mpr (Nat.cast_nonneg (2 * n))
  exact ne_of_gt (hnonpos.trans_lt hℓ)
theorem saddleTaylorContour_crosses_poles
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    ∀ n ∈ Finset.range (N + 1),
      saddleTaylorContour N < -((2 * n : ℕ) : ℝ) ∧
        -((2 * n : ℕ) : ℝ) < ℓ := by
  intro n hn
  have hnle : n ≤ N := by
    have hnlt := Finset.mem_range.mp hn
    omega
  constructor
  · unfold saddleTaylorContour
    apply neg_lt_neg
    exact_mod_cast (show 2 * n < 2 * N + 1 by omega)
  · have hnonpos : -((2 * n : ℕ) : ℝ) ≤ 0 := by
      exact neg_nonpos.mpr (Nat.cast_nonneg (2 * n))
    exact hnonpos.trans_lt hℓ
theorem saddleTaylorContour_le_positive
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    saddleTaylorContour N ≤ ℓ := by
  have hnonpos : saddleTaylorContour N ≤ 0 := by
    unfold saddleTaylorContour
    exact neg_nonpos.mpr (Nat.cast_nonneg (2 * N + 1))
  exact hnonpos.trans hℓ.le
theorem plusSaddleProfile_eq_normalized_vertical_integral
    {ε ℓ r : ℝ} (hr : 0 < r) :
    plusSaddleProfile ε ℓ r =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((ℓ : ℂ) + (t : ℂ) * Complex.I) *
            plusSaddleMellinData ε ℓ
              ((ℓ : ℂ) + (t : ℂ) * Complex.I)) := by
  unfold plusSaddleProfile
  rw [if_neg hr.ne']
  unfold mellinInv
  simp only [smul_eq_mul, Complex.real_smul]
  rfl
theorem minusSaddleProfile_eq_normalized_vertical_integral
    {ε ℓ r : ℝ} (hr : 0 < r) :
    minusSaddleProfile ε ℓ r =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((ℓ : ℂ) + (t : ℂ) * Complex.I) *
            minusSaddleMellinData ε ℓ
              ((ℓ : ℂ) + (t : ℂ) * Complex.I)) := by
  unfold minusSaddleProfile
  rw [if_neg hr.ne']
  unfold mellinInv
  simp only [smul_eq_mul, Complex.real_smul]
  rfl
def plusSaddleTaylorRemainder
    (ε ℓ : ℝ) (N : ℕ) (r : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((saddleTaylorContour N : ℂ) +
          (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((saddleTaylorContour N : ℂ) +
            (t : ℂ) * Complex.I))
def minusSaddleTaylorRemainder
    (ε ℓ : ℝ) (N : ℕ) (r : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((saddleTaylorContour N : ℂ) +
          (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((saddleTaylorContour N : ℂ) +
            (t : ℂ) * Complex.I))
theorem plusSaddlePoleResidue_zero
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    plusSaddlePoleResidue ε ℓ 0 =
      (saddleOriginValue ε ℓ : ℂ) := by
  simpa [plusSaddlePoleResidue] using!
    (two_mul_plusSaddleRegularMellinFactor_zero
      (ε := ε) hℓ)
theorem minusSaddlePoleResidue_zero
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    minusSaddlePoleResidue ε ℓ 0 =
      (saddleOriginValue ε ℓ : ℂ) := by
  simpa [minusSaddlePoleResidue] using!
    (two_mul_minusSaddleRegularMellinFactor_zero
      (ε := ε) hℓ)
theorem plusSaddleProfile_eq_residue_sum_add_remainder
    {ε ℓ r : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ) :
    plusSaddleProfile ε ℓ r =
      (∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          ((r ^ (2 * n) : ℝ) : ℂ)) +
      plusSaddleTaylorRemainder ε ℓ N r := by
  have hcontour :=
    plusSaddleMellinData_vertical_integral_residue_expansion
      hε hℓ horder hr N
      (saddleTaylorContour_mem_halfPlane N)
      (saddleTaylorContour_le_positive hℓ N)
      (fun n : ℕ => saddleTaylorContour_ne_pole N n)
      (fun n : ℕ => saddlePositiveContour_ne_pole hℓ n)
      (saddleTaylorContour_crosses_poles hℓ N)
  have hnormal :
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((2 * Real.pi : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [plusSaddleProfile_eq_normalized_vertical_integral hr,
    hcontour]
  unfold plusSaddleTaylorRemainder
  rw [mul_add, ← mul_assoc, hnormal, one_mul]
  ring
theorem minusSaddleProfile_eq_residue_sum_add_remainder
    {ε ℓ r : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ) :
    minusSaddleProfile ε ℓ r =
      (∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n *
          ((r ^ (2 * n) : ℝ) : ℂ)) +
      minusSaddleTaylorRemainder ε ℓ N r := by
  have hcontour :=
    minusSaddleMellinData_vertical_integral_residue_expansion
      hε hℓ horder hr N
      (saddleTaylorContour_mem_halfPlane N)
      (saddleTaylorContour_le_positive hℓ N)
      (fun n : ℕ => saddleTaylorContour_ne_pole N n)
      (fun n : ℕ => saddlePositiveContour_ne_pole hℓ n)
      (saddleTaylorContour_crosses_poles hℓ N)
  have hnormal :
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((2 * Real.pi : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [minusSaddleProfile_eq_normalized_vertical_integral hr,
    hcontour]
  unfold minusSaddleTaylorRemainder
  rw [mul_add, ← mul_assoc, hnormal, one_mul]
  ring
end
noncomputable section
open Filter
open scoped Topology
def wallisProduct (n : ℕ) : ℝ := Real.Wallis.W n
theorem wallisProduct_pos (n : ℕ) : 0 < wallisProduct n :=
  Real.Wallis.W_pos n
theorem tendsto_wallisProduct :
    Tendsto wallisProduct atTop (nhds (Real.pi / 2)) :=
  Real.Wallis.tendsto_W_nhds_pi_div_two
theorem tendsto_log_wallisProduct :
    Tendsto (fun n : ℕ => Real.log (wallisProduct n))
      atTop (nhds (Real.log (Real.pi / 2))) := by
  exact (Real.continuousAt_log (by positivity)).tendsto.comp
    tendsto_wallisProduct
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
def frullaniKernel (a b x : ℝ) : ℝ :=
  (Real.exp (-a * x) - Real.exp (-b * x)) / x
theorem laplaceKernel_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Ioi 0) := by
  exact integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0
theorem integral_laplaceKernel {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0, Real.exp (-a * x)) = a⁻¹ := by
  simpa using! (integral_exp_mul_Ioi (by linarith : -a < 0) 0)
theorem intervalIntegral_laplaceKernel {x : ℝ} (hx : x ≠ 0)
    (a b : ℝ) :
    (∫ s in a..b, Real.exp (-s * x)) = frullaniKernel a b x := by
  have hderiv (s : ℝ) :
      HasDerivAt (fun u : ℝ => -Real.exp (-u * x) / x)
        (Real.exp (-s * x)) s := by
    convert! (((Real.hasDerivAt_exp (-s * x)).comp s
      ((hasDerivAt_id s).neg.mul_const x)).neg.div_const x)
      using 1; field_simp [hx]
  have hint :
      IntervalIntegrable (fun s : ℝ => Real.exp (-s * x))
        volume a b :=
    ((Real.continuous_exp.comp
      (continuous_id.neg.mul continuous_const)).intervalIntegrable a b)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s) hint]
  unfold frullaniKernel
  ring
theorem laplaceParameter_integrable {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    Integrable
      (Function.uncurry (fun s x : ℝ => Real.exp (-s * x)))
      ((volume.restrict (Set.uIoc a b)).prod
        (volume.restrict (Ioi 0))) := by
  have hmeas :
      AEStronglyMeasurable
        (Function.uncurry (fun s x : ℝ => Real.exp (-s * x)))
        ((volume.restrict (Set.uIoc a b)).prod
          (volume.restrict (Ioi 0))) := by
    fun_prop
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    have hspos : 0 < s := by
      rw [Set.uIoc_of_le hab] at hs
      linarith [hs.1]
    exact laplaceKernel_integrable hspos
  · have hnonzero :
        ∀ s ∈ Set.uIcc a b, s ≠ 0 := by
      intro s hs
      rw [Set.uIcc_of_le hab] at hs
      exact ne_of_gt (lt_of_lt_of_le ha hs.1)
    have hcont : ContinuousOn (fun s : ℝ => s⁻¹) (Set.uIcc a b) :=
      continuousOn_id.inv₀ hnonzero
    have hinv :
        Integrable (fun s : ℝ => s⁻¹)
          (volume.restrict (Set.uIoc a b)) :=
      intervalIntegrable_iff.mp hcont.intervalIntegrable
    apply hinv.congr
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    have hspos : 0 < s := by
      rw [Set.uIoc_of_le hab] at hs
      linarith [hs.1]
    symm
    change (∫ y : ℝ in Ioi 0, ‖Real.exp (-s * y)‖) = s⁻¹
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using!
      integral_laplaceKernel hspos
theorem integral_frullaniKernel {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in Ioi 0, frullaniKernel a b x) =
      Real.log (b / a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  calc
    (∫ x : ℝ in Ioi 0, frullaniKernel a b x) =
        ∫ x : ℝ in Ioi 0, ∫ s in a..b, Real.exp (-s * x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (intervalIntegral_laplaceKernel (ne_of_gt hx) a b).symm
    _ = ∫ s in a..b, ∫ x : ℝ in Ioi 0, Real.exp (-s * x) :=
      (intervalIntegral_integral_swap
        (laplaceParameter_integrable ha hab)).symm
    _ = ∫ s in a..b, s⁻¹ := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hspos : 0 < s := by
        rw [Set.uIcc_of_le hab] at hs
        exact lt_of_lt_of_le ha hs.1
      exact integral_laplaceKernel hspos
    _ = Real.log (b / a) :=
      integral_inv_of_pos ha hb
theorem frullaniKernel_integrable {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (frullaniKernel a b) (Ioi 0) := by
  have hprod := (laplaceParameter_integrable ha hab).integral_prod_right
  apply hprod.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change (∫ s in Set.uIoc a b, Real.exp (-s * x)) =
    frullaniKernel a b x
  rw [Set.uIoc_of_le hab, ← intervalIntegral.integral_of_le hab]
  exact intervalIntegral_laplaceKernel (ne_of_gt hx) a b
def wallisPairKernel (n : ℕ) (x : ℝ) : ℝ :=
  frullaniKernel (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2) x -
    frullaniKernel (2 * (n : ℝ) + 2) (2 * (n : ℝ) + 3) x
theorem wallisPairKernel_eq (n : ℕ) (x : ℝ) :
    wallisPairKernel n x =
      Real.exp (-(2 * (n : ℝ) + 1) * x) *
        (1 - Real.exp (-x)) ^ 2 / x := by
  have htwo :
      Real.exp (-(2 * (n : ℝ) + 2) * x) =
        Real.exp (-(2 * (n : ℝ) + 1) * x) * Real.exp (-x) := by
    rw [show -(2 * (n : ℝ) + 2) * x =
      -(2 * (n : ℝ) + 1) * x + -x by ring, Real.exp_add]
  have hthree :
      Real.exp (-(2 * (n : ℝ) + 3) * x) =
        Real.exp (-(2 * (n : ℝ) + 1) * x) *
          Real.exp (-x) ^ 2 := by
    rw [show -(2 * (n : ℝ) + 3) * x =
      (-(2 * (n : ℝ) + 1) * x + -x) + -x by ring,
      Real.exp_add, Real.exp_add]
    ring
  unfold wallisPairKernel frullaniKernel
  rw [htwo, hthree]
  ring
theorem wallisPairKernel_integrable (n : ℕ) :
    IntegrableOn (wallisPairKernel n) (Ioi 0) := by
  unfold wallisPairKernel
  apply Integrable.sub
  · exact frullaniKernel_integrable (by positivity) (by linarith)
  · exact frullaniKernel_integrable (by positivity) (by linarith)
def wallisPairFactor (n : ℕ) : ℝ :=
  ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1)) *
    ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3))
theorem integral_wallisPairKernel (n : ℕ) :
    (∫ x : ℝ in Ioi 0, wallisPairKernel n x) =
      Real.log (wallisPairFactor n) := by
  unfold wallisPairKernel
  rw [integral_sub
    (frullaniKernel_integrable (by positivity) (by linarith))
    (frullaniKernel_integrable (by positivity) (by linarith)),
    integral_frullaniKernel (by positivity) (by linarith),
    integral_frullaniKernel (by positivity) (by linarith)]
  unfold wallisPairFactor
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity)]
  ring
theorem wallisPairFactor_pos (n : ℕ) : 0 < wallisPairFactor n := by
  unfold wallisPairFactor
  positivity
theorem wallisProduct_succ (n : ℕ) :
    wallisProduct (n + 1) =
      wallisProduct n * wallisPairFactor n := by
  simpa [wallisProduct, wallisPairFactor] using! Real.Wallis.W_succ n
def wallisPartialKernel (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, wallisPairKernel k x
theorem wallisPartialKernel_integrable (n : ℕ) :
    IntegrableOn (wallisPartialKernel n) (Ioi 0) := by
  unfold wallisPartialKernel
  exact integrable_finsetSum _ fun k _ => wallisPairKernel_integrable k
theorem integral_wallisPartialKernel (n : ℕ) :
    (∫ x : ℝ in Ioi 0, wallisPartialKernel n x) =
      Real.log (wallisProduct n) := by
  induction n with
  | zero =>
      simp [wallisPartialKernel, wallisProduct, Real.Wallis.W]
  | succ n ih =>
      have hpartial :
          (fun x : ℝ => wallisPartialKernel (n + 1) x) =
            fun x : ℝ =>
              wallisPartialKernel n x + wallisPairKernel n x := by
        funext x
        simp [wallisPartialKernel, Finset.sum_range_succ]
      rw [hpartial, integral_add (wallisPartialKernel_integrable n)
        (wallisPairKernel_integrable n), ih,
        integral_wallisPairKernel, wallisProduct_succ,
        Real.log_mul (wallisProduct_pos n).ne'
          (wallisPairFactor_pos n).ne']
def wallisLaplaceKernel (x : ℝ) : ℝ :=
  Real.exp (-x) * (1 - Real.exp (-x)) /
    (x * (1 + Real.exp (-x)))
theorem wallisPartialKernel_eq (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    wallisPartialKernel n x =
      wallisLaplaceKernel x *
        (1 - Real.exp (-(2 * (n : ℝ)) * x)) := by
  induction n with
  | zero => simp [wallisPartialKernel]
  | succ n ih =>
      rw [show wallisPartialKernel (n + 1) x =
          wallisPartialKernel n x + wallisPairKernel n x by
        simp [wallisPartialKernel, Finset.sum_range_succ],
        ih, wallisPairKernel_eq]
      have htwo :
          Real.exp (-(2 * ((n + 1 : ℕ) : ℝ)) * x) =
            Real.exp (-(2 * (n : ℝ)) * x) *
              Real.exp (-x) ^ 2 := by
        push_cast
        rw [show -(2 * ((n : ℝ) + 1)) * x =
          (-(2 * (n : ℝ)) * x + -x) + -x by ring,
          Real.exp_add, Real.exp_add]
        ring
      have hone :
          Real.exp (-(2 * (n : ℝ) + 1) * x) =
            Real.exp (-(2 * (n : ℝ)) * x) *
              Real.exp (-x) := by
        rw [show -(2 * (n : ℝ) + 1) * x =
          -(2 * (n : ℝ)) * x + -x by ring, Real.exp_add]
      rw [htwo, hone]
      unfold wallisLaplaceKernel
      have hden : 1 + Real.exp (-x) ≠ 0 := by positivity
      field_simp [hx, hden]
      ring
theorem wallisLaplaceKernel_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ wallisLaplaceKernel x := by
  unfold wallisLaplaceKernel
  have hq : Real.exp (-x) ≤ 1 :=
    (Real.exp_le_one_iff).2 (neg_nonpos.mpr hx.le)
  exact div_nonneg
    (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hq))
    (mul_nonneg hx.le (by positivity))
theorem wallisLaplaceKernel_abs_le {x : ℝ} (hx : 0 < x) :
    |wallisLaplaceKernel x| ≤ Real.exp (-x) := by
  rw [abs_of_nonneg (wallisLaplaceKernel_nonneg hx)]
  unfold wallisLaplaceKernel
  have hq : 0 < Real.exp (-x) := Real.exp_pos _
  have hsub : 1 - Real.exp (-x) ≤ x := by
    linarith [Real.add_one_le_exp (-x)]
  have hden : 0 < x * (1 + Real.exp (-x)) := by positivity
  apply (div_le_iff₀ hden).2
  have hmul : 0 ≤ x * Real.exp (-x) :=
    mul_nonneg hx.le hq.le
  nlinarith
theorem wallisLaplaceKernel_integrable :
    IntegrableOn wallisLaplaceKernel (Ioi 0) := by
  have hbound :
      IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    simpa using! laplaceKernel_integrable (a := (1 : ℝ)) zero_lt_one
  refine hbound.mono' ?_ ?_
  · unfold wallisLaplaceKernel
    exact (by fun_prop : Measurable
      (fun x : ℝ => Real.exp (-x) * (1 - Real.exp (-x)) /
        (x * (1 + Real.exp (-x))))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [Real.norm_eq_abs] using! wallisLaplaceKernel_abs_le hx
theorem wallisPartialKernel_abs_le (n : ℕ) {x : ℝ} (hx : 0 < x) :
    |wallisPartialKernel n x| ≤ wallisLaplaceKernel x := by
  rw [wallisPartialKernel_eq n hx.ne']
  have hexp : Real.exp (-(2 * (n : ℝ)) * x) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hfactor : 0 ≤ 1 - Real.exp (-(2 * (n : ℝ)) * x) :=
    sub_nonneg.mpr hexp
  have hfactor_le : 1 - Real.exp (-(2 * (n : ℝ)) * x) ≤ 1 := by
    linarith [Real.exp_pos (-(2 * (n : ℝ)) * x)]
  rw [abs_of_nonneg
    (mul_nonneg (wallisLaplaceKernel_nonneg hx) hfactor)]
  exact mul_le_of_le_one_right (wallisLaplaceKernel_nonneg hx) hfactor_le
theorem tendsto_wallisPartialKernel {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => wallisPartialKernel n x)
      atTop (nhds (wallisLaplaceKernel x)) := by
  have hlinear :
      Tendsto (fun n : ℕ => (2 * x) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have hexp :
      Tendsto (fun n : ℕ =>
        Real.exp (-(2 * (n : ℝ)) * x)) atTop (nhds 0) := by
    convert! Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear using 1
    funext n
    congr 1
    ring
  have hfactor :
      Tendsto (fun n : ℕ =>
        1 - Real.exp (-(2 * (n : ℝ)) * x)) atTop (nhds 1) := by
    simpa using! tendsto_const_nhds.sub hexp
  have hproduct :=
    (tendsto_const_nhds (x := wallisLaplaceKernel x)).mul hfactor
  simpa only [mul_one, wallisPartialKernel_eq _ hx.ne'] using! hproduct
theorem tendsto_integral_wallisPartialKernel :
    Tendsto
      (fun n : ℕ => ∫ x : ℝ in Ioi 0, wallisPartialKernel n x)
      atTop (nhds (∫ x : ℝ in Ioi 0, wallisLaplaceKernel x)) := by
  apply tendsto_integral_of_dominated_convergence
    wallisLaplaceKernel
    (fun n => (wallisPartialKernel_integrable n).aestronglyMeasurable)
    wallisLaplaceKernel_integrable
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa only [Real.norm_eq_abs] using!
      wallisPartialKernel_abs_le n hx
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact tendsto_wallisPartialKernel hx
theorem integral_wallisLaplaceKernel :
    (∫ x : ℝ in Ioi 0, wallisLaplaceKernel x) =
      Real.log (Real.pi / 2) := by
  have hproduct :
      Tendsto
        (fun n : ℕ => ∫ x : ℝ in Ioi 0, wallisPartialKernel n x)
        atTop (nhds (Real.log (Real.pi / 2))) := by
    simpa only [integral_wallisPartialKernel] using!
      tendsto_log_wallisProduct
  exact tendsto_nhds_unique tendsto_integral_wallisPartialKernel
    hproduct
end
noncomputable section
open Filter MeasureTheory
open scoped Topology
theorem tendsto_cubic_gaussian_atTop :
    Tendsto (fun x : ℝ => (x ^ 3 + 1) * Real.exp (-(x ^ 2) / 8))
      atTop (nhds 0) := by
  have hpoly :
      Tendsto (fun x : ℝ => x ^ 3 * Real.exp (-(1 / 8 : ℝ) * x))
        atTop (nhds 0) := by
    simpa [Real.rpow_natCast] using!
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (3 : ℝ) (1 / 8 : ℝ) (by norm_num))
  have hone :
      Tendsto (fun x : ℝ => Real.exp (-(1 / 8 : ℝ) * x))
        atTop (nhds 0) := by
    simpa using!
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (0 : ℝ) (1 / 8 : ℝ) (by norm_num))
  have hlinear :
      Tendsto
        (fun x : ℝ => (x ^ 3 + 1) * Real.exp (-(1 / 8 : ℝ) * x))
        atTop (nhds 0) := by
    convert! hpoly.add hone using 1
    · ext x
      ring
    · norm_num
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hlinear ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpoly : 0 ≤ x ^ 3 + 1 := by positivity
    apply mul_le_mul_of_nonneg_left _ hxpoly
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ x)
      (by linarith : 0 ≤ x - 1)]
def shellRadiusMajorant (ε : ℝ) : ℝ :=
  (shellLocation ε + 1) * shellWeight ε *
    Real.exp ((ε / 4) * (shellLocation ε + 1))
theorem shellRadiusMajorant_inv {x : ℝ} (hx : x ≠ 0) :
    shellRadiusMajorant x⁻¹ =
      ((x ^ 3 + 1) * Real.exp (-(x ^ 2) / 8)) *
        Real.exp (x⁻¹ / 4) := by
  unfold shellRadiusMajorant shellWeight shellLocation
  simp only [inv_inv]
  simp only [mul_assoc]
  congr 1
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring
theorem tendsto_shellRadiusMajorant :
    Tendsto shellRadiusMajorant (𝓝[>] (0 : ℝ)) (nhds 0) := by
  apply tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop
  have hsmall :
      Tendsto (fun x : ℝ => x⁻¹ / 4) atTop (nhds 0) := by
    convert! tendsto_inv_atTop_zero.div_const (4 : ℝ) using 1; norm_num
  have hexp :
      Tendsto (fun x : ℝ => Real.exp (x⁻¹ / 4)) atTop (nhds 1) := by
    simpa using! hsmall.rexp
  have hproduct := tendsto_cubic_gaussian_atTop.mul hexp
  have hzero :
      Tendsto
        (fun x : ℝ =>
          ((x ^ 3 + 1) * Real.exp (-(x ^ 2) / 8)) *
            Real.exp (x⁻¹ / 4))
        atTop (nhds 0) := by
    simpa using! hproduct
  refine hzero.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  exact (shellRadiusMajorant_inv hx).symm
theorem tendsto_positiveShellRadiusContribution :
    Tendsto positiveShellRadiusContribution
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ)))
    tendsto_shellRadiusMajorant ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (positiveShellRadiusContribution_bounds hε).1
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (positiveShellRadiusContribution_bounds hε).2
theorem sinh_le_mul_cosh {a : ℝ} (ha : 0 ≤ a) :
    Real.sinh a ≤ a * Real.cosh a := by
  let f : ℝ → ℝ := fun x => x * Real.cosh x - Real.sinh x
  have hderiv (x : ℝ) :
      HasDerivAt f (x * Real.sinh x) x := by
    try dsimp [f]
    convert! ((hasDerivAt_id x).mul
      (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x) using 1;
      simp [id]
  have hdiff : Differentiable ℝ f :=
    fun x => (hderiv x).differentiableAt
  have hmono : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
      hdiff.continuous.continuousOn hdiff.differentiableOn
    intro x hx
    rw [interior_Ici] at hx
    rw [(hderiv x).deriv]
    exact mul_nonneg hx.le (Real.sinh_nonneg_iff.mpr hx.le)
  have h := hmono (show (0 : ℝ) ∈ Set.Ici 0 by simp)
    (show a ∈ Set.Ici 0 from ha) ha
  try dsimp [f] at h
  norm_num at h
  linarith
def shortShellRadiusIntegrand (ε a : ℝ) : ℝ :=
  shortShellDensity ε a * a * Real.sinh ((1 + ε / 4) * a)
def wallisRadiusIntegrand (a : ℝ) : ℝ :=
  -(Real.exp (-2 * a) * Real.tanh a / (2 * a))
theorem tendsto_shortShellRadiusIntegrand {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => shortShellRadiusIntegrand ε a)
      (𝓝[>] (0 : ℝ)) (nhds (wallisRadiusIntegrand a)) := by
  have hc : Continuous (fun ε : ℝ => shortShellRadiusIntegrand ε a) := by
    unfold shortShellRadiusIntegrand shortShellDensity shortMargin
    fun_prop
  have ht :
      Tendsto (fun ε : ℝ => shortShellRadiusIntegrand ε a)
        (𝓝[>] (0 : ℝ)) (nhds (shortShellRadiusIntegrand 0 a)) :=
    (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hvalue : shortShellRadiusIntegrand 0 a =
      wallisRadiusIntegrand a := by
    unfold shortShellRadiusIntegrand shortShellDensity shortMargin
      wallisRadiusIntegrand
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [ha.ne', (Real.cosh_pos a).ne']
    ring_nf
  simpa [hvalue] using! ht
theorem shortMargin_abs_le_exp {ε a : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 ≤ a) :
    |shortMargin ε a| ≤ 11 * Real.exp a := by
  have hterm : 0 ≤ 10 * ε * (1 + a) := by positivity
  calc
    |shortMargin ε a| = |1 - 10 * ε * (1 + a)| := rfl
    _ ≤ |(1 : ℝ)| + |10 * ε * (1 + a)| := abs_sub _ _
    _ = 1 + 10 * ε * (1 + a) := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1),
        abs_of_nonneg hterm]
    _ ≤ 11 * (1 + a) := by
      nlinarith [mul_le_mul_of_nonneg_right hε1
        (show 0 ≤ 1 + a by linarith)]
    _ ≤ 11 * Real.exp a := by
      gcongr
      nlinarith [Real.add_one_le_exp a]
theorem shortShellHyperbolicRatio_le {ε a : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 ≤ a) :
    Real.sinh ((1 + ε / 4) * a) / Real.cosh a ≤
      (5 / 4 : ℝ) * a * Real.exp (a / 4) := by
  have hδ : 0 ≤ ε / 4 := by positivity
  have harg : 0 ≤ (1 + ε / 4) * a := by positivity
  calc
    Real.sinh ((1 + ε / 4) * a) / Real.cosh a
        ≤ ((1 + ε / 4) * a) *
          (Real.cosh ((1 + ε / 4) * a) / Real.cosh a) := by
          rw [← mul_div_assoc]
          exact (div_le_div_iff_of_pos_right (Real.cosh_pos a)).2
            (sinh_le_mul_cosh harg)
    _ ≤ ((5 / 4 : ℝ) * a) * Real.exp ((ε / 4) * a) := by
          gcongr
          · nlinarith
          · exact cosh_ratio_upper ha hδ
    _ ≤ ((5 / 4 : ℝ) * a) * Real.exp (a / 4) := by
          gcongr
          nlinarith [mul_le_mul_of_nonneg_right hε1 ha]
theorem shortShellRadiusIntegrand_eq_ratio {ε a : ℝ} (ha : a ≠ 0) :
    shortShellRadiusIntegrand ε a =
      -(shortMargin ε a * Real.exp (-2 * a) *
        (Real.sinh ((1 + ε / 4) * a) / Real.cosh a) /
          (2 * a)) := by
  unfold shortShellRadiusIntegrand shortShellDensity
  field_simp [ha, (Real.cosh_pos a).ne']
theorem shortShellRadiusIntegrand_abs_le {ε a : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 < a) :
    |shortShellRadiusIntegrand ε a| ≤
      7 * Real.exp (-(3 / 4 : ℝ) * a) := by
  have harg : 0 ≤ (1 + ε / 4) * a := by positivity
  have hratio0 :
      0 ≤ Real.sinh ((1 + ε / 4) * a) / Real.cosh a :=
    div_nonneg (Real.sinh_nonneg_iff.mpr harg)
      (Real.cosh_pos a).le
  rw [shortShellRadiusIntegrand_eq_ratio ha.ne', abs_neg,
    abs_div, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos (-2 * a)), abs_of_nonneg hratio0,
    abs_of_pos (by positivity : 0 < (2 : ℝ) * a)]
  calc
    |shortMargin ε a| * Real.exp (-2 * a) *
        (Real.sinh ((1 + ε / 4) * a) / Real.cosh a) / (2 * a)
      ≤ (11 * Real.exp a) * Real.exp (-2 * a) *
          ((5 / 4 : ℝ) * a * Real.exp (a / 4)) / (2 * a) := by
            gcongr
            · exact shortMargin_abs_le_exp hε0 hε1 ha.le
            · exact shortShellHyperbolicRatio_le hε0 hε1 ha.le
    _ = (55 / 8 : ℝ) * Real.exp (-(3 / 4 : ℝ) * a) := by
          rw [show -(3 / 4 : ℝ) * a =
            (a + -2 * a) + a / 4 by ring,
            Real.exp_add, Real.exp_add]
          field_simp [ha.ne']
          ring
    _ ≤ 7 * Real.exp (-(3 / 4 : ℝ) * a) :=
          mul_le_mul_of_nonneg_right (by norm_num)
            (Real.exp_pos _).le
def shortShellRadiusMajorant (a : ℝ) : ℝ :=
  7 * Real.exp (-(3 / 4 : ℝ) * a)
theorem shortShellRadiusMajorant_integrable :
    IntegrableOn shortShellRadiusMajorant (Set.Ioi (0 : ℝ)) := by
  change Integrable
    (fun a : ℝ => 7 * Real.exp (-(3 / 4 : ℝ) * a))
    (volume.restrict (Set.Ioi (0 : ℝ)))
  simpa only [neg_div] using!
    (integrableOn_exp_mul_Ioi (a := (-3 / 4 : ℝ))
      (by norm_num) 0).const_mul 7
theorem shortShellRadiusIntegrand_measurable (ε : ℝ) :
    Measurable (shortShellRadiusIntegrand ε) := by
  have hn : Measurable (fun a : ℝ =>
      shortMargin ε a * Real.exp (-2 * a)) := by
    unfold shortMargin
    fun_prop
  have hd : Measurable (fun a : ℝ =>
      2 * a ^ 2 * Real.cosh a) := by
    fun_prop
  have hs : Measurable (fun a : ℝ =>
      Real.sinh ((1 + ε / 4) * a)) := by
    fun_prop
  exact ((hn.div hd).neg.mul measurable_id).mul hs
theorem tendsto_shortCutoff :
    Tendsto shortCutoff (𝓝[>] (0 : ℝ)) (nhds 0) := by
  have ht : Tendsto (fun ε : ℝ => ε)
      (𝓝[>] (0 : ℝ)) (nhds 0) :=
    tendsto_id.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa [shortCutoff] using! ht.pow 3
theorem tendsto_shortEndpoint :
    Tendsto shortEndpoint (𝓝[>] (0 : ℝ)) atTop := by
  have ht : Tendsto (fun ε : ℝ => Real.log ε⁻¹)
      (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  change Tendsto (fun ε : ℝ => 10 * Real.log (1 / ε))
    (𝓝[>] (0 : ℝ)) atTop
  simpa only [one_div] using!
    ht.const_mul_atTop (by norm_num : (0 : ℝ) < 10)
def shortShellRadiusContribution (ε : ℝ) : ℝ :=
  ∫ a in shortCutoff ε..shortEndpoint ε,
    shortShellRadiusIntegrand ε a
def supportedShortShellRadiusIntegrand (ε a : ℝ) : ℝ :=
  (Set.Ioc (shortCutoff ε) (shortEndpoint ε)).indicator
    (shortShellRadiusIntegrand ε) a
theorem supportedShortShellRadiusIntegrand_measurable (ε : ℝ) :
    Measurable (supportedShortShellRadiusIntegrand ε) := by
  exact (shortShellRadiusIntegrand_measurable ε).indicator
    measurableSet_Ioc
theorem tendsto_supportedShortShellRadiusIntegrand {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => supportedShortShellRadiusIntegrand ε a)
      (𝓝[>] (0 : ℝ)) (nhds (wallisRadiusIntegrand a)) := by
  refine (tendsto_shortShellRadiusIntegrand ha).congr' ?_
  filter_upwards
    [tendsto_shortCutoff.eventually (Iio_mem_nhds ha),
      tendsto_shortEndpoint.eventually_ge_atTop a]
    with ε hlower hupper
  have hmem : a ∈ Set.Ioc (shortCutoff ε) (shortEndpoint ε) :=
    ⟨hlower, hupper⟩
  simp [supportedShortShellRadiusIntegrand, Set.indicator_of_mem hmem]
theorem tendsto_supportedShortShellRadiusIntegral :
    Tendsto
      (fun ε : ℝ => ∫ a in Set.Ioi (0 : ℝ),
        supportedShortShellRadiusIntegrand ε a)
      (𝓝[>] (0 : ℝ))
      (nhds (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    shortShellRadiusMajorant
  · exact Eventually.of_forall fun ε =>
      (supportedShortShellRadiusIntegrand_measurable ε).aestronglyMeasurable
  · filter_upwards
      [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds
          (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with ε hε hsmall
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    by_cases hmem : a ∈ Set.Ioc (shortCutoff ε) (shortEndpoint ε)
    · rw [show supportedShortShellRadiusIntegrand ε a =
        shortShellRadiusIntegrand ε a by
          exact Set.indicator_of_mem hmem (shortShellRadiusIntegrand ε)]
      rw [Real.norm_eq_abs]
      exact shortShellRadiusIntegrand_abs_le hε.le hsmall.le ha
    · rw [show supportedShortShellRadiusIntegrand ε a = 0 by
        exact Set.indicator_of_notMem hmem (shortShellRadiusIntegrand ε),
        norm_zero]
      unfold shortShellRadiusMajorant
      positivity
  · exact shortShellRadiusMajorant_integrable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact tendsto_supportedShortShellRadiusIntegrand ha
theorem shortShellRadiusContribution_eq_supported {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    shortShellRadiusContribution ε =
      ∫ a in Set.Ioi (0 : ℝ),
        supportedShortShellRadiusIntegrand ε a := by
  have hcutoff : 0 ≤ shortCutoff ε := by
    unfold shortCutoff
    positivity
  have hsubset :
      Set.Ioc (shortCutoff ε) (shortEndpoint ε) ⊆
        Set.Ioi (0 : ℝ) := by
    intro a ha
    exact lt_of_le_of_lt hcutoff ha.1
  unfold shortShellRadiusContribution supportedShortShellRadiusIntegrand
  rw [intervalIntegral.integral_of_le horder,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset hsubset]
theorem tendsto_shortShellRadiusContribution :
    Tendsto shortShellRadiusContribution
      (𝓝[>] (0 : ℝ))
      (nhds (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a)) := by
  refine tendsto_supportedShortShellRadiusIntegral.congr' ?_
  filter_upwards
    [self_mem_nhdsWithin,
      tendsto_shortCutoff.eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      tendsto_shortEndpoint.eventually_ge_atTop (1 : ℝ)]
    with ε hε hcutoff hendpoint
  have horder : shortCutoff ε ≤ shortEndpoint ε :=
    hcutoff.le.trans hendpoint
  exact (shortShellRadiusContribution_eq_supported hε horder).symm
theorem wallisRadiusIntegrand_eq_laplace (a : ℝ) :
    wallisRadiusIntegrand a = -wallisLaplaceKernel (2 * a) := by
  by_cases ha : a = 0
  · simp [wallisRadiusIntegrand, wallisLaplaceKernel, ha]
  · have hexp :
        Real.exp (-2 * a) = Real.exp (-a) / Real.exp a := by
        rw [← Real.exp_sub]
        congr 1
        ring
    have hplus : Real.exp a + Real.exp (-a) ≠ 0 := by
      positivity
    have hratio : 1 + Real.exp (-a) / Real.exp a ≠ 0 := by
      positivity
    unfold wallisRadiusIntegrand wallisLaplaceKernel
    rw [Real.tanh_eq a]
    simp only [show -(2 * a) = -2 * a by ring]
    rw [hexp]
    field_simp [ha, (Real.exp_pos a).ne', hplus, hratio]
theorem integral_wallisRadiusIntegrand :
    (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a) =
      -(1 / 2 : ℝ) * Real.log (Real.pi / 2) := by
  have hscale :
      (∫ a in Set.Ioi (0 : ℝ), wallisLaplaceKernel (2 * a)) =
        (2 : ℝ)⁻¹ * Real.log (Real.pi / 2) := by
    simpa [smul_eq_mul, integral_wallisLaplaceKernel] using!
      (integral_comp_mul_left_Ioi wallisLaplaceKernel 0
        (by norm_num : (0 : ℝ) < 2))
  calc
    (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a) =
        ∫ a in Set.Ioi (0 : ℝ), -wallisLaplaceKernel (2 * a) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro a _
          exact wallisRadiusIntegrand_eq_laplace a
    _ = -(∫ a in Set.Ioi (0 : ℝ), wallisLaplaceKernel (2 * a)) := by
          rw [integral_neg]
    _ = -(1 / 2 : ℝ) * Real.log (Real.pi / 2) := by
          rw [hscale]
          ring
def limitingSaddleRadius (ε : ℝ) : ℝ :=
  Real.sqrt ((2 + ε / 4) / (4 * Real.pi)) *
    Real.exp (shortShellRadiusContribution ε +
      positiveShellRadiusContribution ε)
theorem tendsto_limitingSaddleRadius_wallisIntegral :
    Tendsto limitingSaddleRadius (𝓝[>] (0 : ℝ))
      (nhds (Real.sqrt (1 / (2 * Real.pi)) *
        Real.exp (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a))) := by
  have hε : Tendsto (fun ε : ℝ => ε)
      (𝓝[>] (0 : ℝ)) (nhds 0) :=
    tendsto_id.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hnum : Tendsto (fun ε : ℝ => 2 + ε / 4)
      (𝓝[>] (0 : ℝ)) (nhds (2 : ℝ)) := by
    simpa using! (tendsto_const_nhds (x := (2 : ℝ))).add
      (hε.div_const 4)
  have hratio : Tendsto
      (fun ε : ℝ => (2 + ε / 4) / (4 * Real.pi))
      (𝓝[>] (0 : ℝ)) (nhds (1 / (2 * Real.pi))) := by
    have hvalue : (2 : ℝ) / (4 * Real.pi) =
        1 / (2 * Real.pi) := by
      field_simp [Real.pi_ne_zero]
      norm_num
    simpa only [hvalue] using! hnum.div_const (4 * Real.pi)
  have hfactor : Tendsto
      (fun ε : ℝ => Real.sqrt ((2 + ε / 4) / (4 * Real.pi)))
      (𝓝[>] (0 : ℝ)) (nhds (Real.sqrt (1 / (2 * Real.pi)))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  have hshell : Tendsto
      (fun ε : ℝ => shortShellRadiusContribution ε +
        positiveShellRadiusContribution ε)
      (𝓝[>] (0 : ℝ))
      (nhds (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a)) := by
    simpa using! tendsto_shortShellRadiusContribution.add
      tendsto_positiveShellRadiusContribution
  exact hfactor.mul hshell.rexp
theorem saddleRadius_wallis_constant :
    Real.sqrt (1 / (2 * Real.pi)) *
      Real.exp (-(1 / 2 : ℝ) * Real.log (Real.pi / 2)) =
        criticalRadius := by
  have hhalfpi : 0 < Real.pi / 2 := by positivity
  have hexpsq :
      (Real.exp (-(1 / 2 : ℝ) * Real.log (Real.pi / 2))) ^ 2 =
        (Real.pi / 2)⁻¹ := by
    calc
      (Real.exp (-(1 / 2 : ℝ) * Real.log (Real.pi / 2))) ^ 2 =
          Real.exp
            (-(1 / 2 : ℝ) * Real.log (Real.pi / 2) +
              -(1 / 2 : ℝ) * Real.log (Real.pi / 2)) := by
            rw [Real.exp_add]
            ring
      _ = Real.exp (-Real.log (Real.pi / 2)) := by
            congr 1
            ring
      _ = (Real.pi / 2)⁻¹ := by
            rw [Real.exp_neg, Real.exp_log hhalfpi]
  have hsquare :
      (Real.sqrt (1 / (2 * Real.pi)) *
        Real.exp (-(1 / 2 : ℝ) * Real.log (Real.pi / 2))) ^ 2 =
          (Real.pi⁻¹) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hexpsq]
    field_simp [Real.pi_ne_zero]
  have hleft : 0 ≤
      Real.sqrt (1 / (2 * Real.pi)) *
        Real.exp (-(1 / 2 : ℝ) * Real.log (Real.pi / 2)) := by
    positivity
  have hright : 0 ≤ Real.pi⁻¹ := (inv_pos.mpr Real.pi_pos).le
  unfold criticalRadius
  nlinarith
theorem tendsto_limitingSaddleRadius :
    Tendsto limitingSaddleRadius (𝓝[>] (0 : ℝ))
      (nhds criticalRadius) := by
  have h := tendsto_limitingSaddleRadius_wallisIntegral
  rw [integral_wallisRadiusIntegrand] at h
  simpa only [saddleRadius_wallis_constant] using! h
end
noncomputable section
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal
def radialL1Mass {d : ℕ} (g : TestFunction d) : ℝ :=
  ∫ x : Euclidean d, ‖g x‖
theorem integrable_scaled_exp_change_Ioi {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (f : ℝ → E) :
    IntegrableOn f (Ioi 0) ↔
      Integrable (fun v : ℝ =>
        (R * Real.exp v) • f (R * Real.exp v)) := by
  let F : ℝ → ℝ := fun v => R * Real.exp v
  have himage : F '' (Set.univ : Set ℝ) = Ioi 0 := by
    ext r
    constructor
    · rintro ⟨v, _, rfl⟩
      exact mul_pos hR (Real.exp_pos v)
    · intro hr
      refine ⟨Real.log (r / R), Set.mem_univ _, ?_⟩
      try dsimp [F]
      rw [Real.exp_log (div_pos hr hR)]
      field_simp
  have hderiv :
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivWithinAt F (R * Real.exp x) Set.univ x := by
    intro x _
    exact ((Real.hasDerivAt_exp x).const_mul R).hasDerivWithinAt
  have hinj : Set.InjOn F (Set.univ : Set ℝ) := by
    intro x _ y _ hxy
    exact Real.exp_injective (mul_left_cancel₀ hR.ne' hxy)
  simpa [himage, F, abs_of_pos (mul_pos hR (Real.exp_pos _))] using!
      (integrableOn_image_iff_integrableOn_abs_deriv_smul
        (f := F) (f' := fun x => R * Real.exp x)
        MeasurableSet.univ hderiv hinj f)
def normalizedRadialLogProfile {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (R v : ℝ) : ℝ :=
  radialSurfaceArea d / radialL1Mass g *
    (R * Real.exp v) ^ d *
    (radialProfile hd g (R * Real.exp v)).re
end
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
def radialLineIsometry {d : ℕ} (hd : 0 < d) :
    ℝ →ₗᵢ[ℝ] Euclidean d :=
  LinearIsometry.toSpanSingleton ℝ (Euclidean d)
    (norm_radialUnitDirection hd)
def radialSchwartzProfile {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (radialLineIsometry hd).toContinuousLinearMap.hasTemperateGrowth
    (radialLineIsometry hd).isometry.antilipschitz f
@[simp] theorem radialSchwartzProfile_apply {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (r : ℝ) :
    radialSchwartzProfile hd f r = radialProfile hd f r := by
  rfl
def radialMellinStrip {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (z : ℂ) : ℂ :=
  mellin (radialProfile hd f)
    ((d : ℂ) / 2 - Complex.I * z)
def normalizedRadialMellinStrip {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (R : ℝ) (z : ℂ) : ℂ :=
  (radialSurfaceArea d / radialL1Mass f : ℝ) *
    Complex.exp
      (((d : ℂ) / 2 + Complex.I * z) *
        (Real.log R : ℂ)) *
      radialMellinStrip hd f z
theorem integrable_fourier_of_integrable_two_derivatives
    (g : ℝ → ℂ) (hg : Integrable g)
    (hgdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g))
    (hg'diff : Differentiable ℝ (deriv g))
    (hg'' : Integrable (deriv (deriv g))) :
    Integrable (𝓕 g : ℝ → ℂ) := by
  let A : ℝ := ∫ v : ℝ, ‖g v‖
  let D : ℝ := ∫ v : ℝ, ‖deriv (deriv g) v‖
  let p : ℝ := 2 * Real.pi
  have hp : 0 < p := by
    try dsimp [p]
    positivity
  have hA : 0 ≤ A := by
    try dsimp [A]
    exact integral_nonneg (fun v => norm_nonneg _)
  have hD : 0 ≤ D := by
    try dsimp [D]
    exact integral_nonneg (fun v => norm_nonneg _)
  have hcont : Continuous (𝓕 g : ℝ → ℂ) := by
    exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg
  have hzero (t : ℝ) :
      ‖(𝓕 g : ℝ → ℂ) t‖ ≤ A := by
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) g t
  have hident (t : ℝ) :
      (𝓕 (deriv (deriv g)) : ℝ → ℂ) t =
        (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2 *
          (𝓕 g : ℝ → ℂ) t := by
    rw [congrFun
      (Real.fourier_deriv hg' hg'diff hg'') t,
      congrFun (Real.fourier_deriv hg hgdiff hg') t]
    simp only [smul_eq_mul]
    ring
  have hcoef (t : ℝ) :
      ‖(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2‖ =
        p ^ 2 * t ^ 2 := by
    try dsimp [p]
    simp [norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [mul_pow, sq_abs]
  have hsecond (t : ℝ) :
      p ^ 2 * t ^ 2 * ‖(𝓕 g : ℝ → ℂ) t‖ ≤ D := by
    calc
      p ^ 2 * t ^ 2 * ‖(𝓕 g : ℝ → ℂ) t‖ =
        ‖(𝓕 (deriv (deriv g)) : ℝ → ℂ) t‖ := by
        rw [hident, norm_mul, hcoef]
      _ ≤ D :=
        VectorFourier.norm_fourierIntegral_le_integral_norm
          Real.fourierChar volume (innerₗ ℝ)
          (deriv (deriv g)) t
  have hquadratic (t : ℝ) :
      t ^ 2 * ‖(𝓕 g : ℝ → ℂ) t‖ ≤ D / p ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hp)).2
    nlinarith [hsecond t]
  have hmajor : Integrable
      (fun t : ℝ => (A + D / p ^ 2) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (A + D / p ^ 2)
  apply hmajor.mono' hcont.aestronglyMeasurable
  filter_upwards [] with t
  have hden : 0 < 1 + t ^ 2 := by positivity
  have hconstant : 0 ≤ A + D / p ^ 2 := by positivity
  change ‖(𝓕 g : ℝ → ℂ) t‖ ≤
    (A + D / p ^ 2) / (1 + t ^ 2)
  apply (le_div_iff₀ hden).2
  nlinarith [hzero t, hquadratic t,
    norm_nonneg ((𝓕 g : ℝ → ℂ) t)]
theorem schwartzRealLine_mellinConvergent_of_re_pos
    (g : 𝓢(ℝ, ℂ)) (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (g : ℝ → ℂ) s := by
  have hlocal : LocallyIntegrableOn
      (g : ℝ → ℂ) (Ioi (0 : ℝ)) :=
    g.continuous.locallyIntegrable.locallyIntegrableOn _
  have htop :
      (g : ℝ → ℂ) =O[atTop]
        (fun r : ℝ => r ^ (-(s.re + 1))) := by
    have h :=
      (g.isBigO_cocompact_rpow (-(s.re + 1))).mono
        atTop_le_cocompact
    refine h.congr' (Eventually.of_forall (fun _ => rfl)) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    simp [Real.norm_eq_abs, abs_of_pos hr]
  obtain ⟨C, _hC, hdecay⟩ := g.decay 0 0
  have hbounded (r : ℝ) : ‖g r‖ ≤ C := by
    simpa using! hdecay r
  have hzero :
      (g : ℝ → ℂ) =O[𝓝[>] (0 : ℝ)]
        (fun r : ℝ => r ^ (-(0 : ℝ))) := by
    apply IsBigO.of_bound C
    filter_upwards [] with r
    simpa using! hbounded r
  exact mellinConvergent_of_isBigO_rpow
    (a := s.re + 1) (b := (0 : ℝ)) hlocal htop
    (by linarith) hzero hs
def schwartzExponentialTilt
    (g : 𝓢(ℝ, ℂ)) (κ R v : ℝ) : ℂ :=
  (Real.exp (κ * v) : ℂ) * g (R * Real.exp v)
theorem schwartzExponentialTilt_integrable
    (g : 𝓢(ℝ, ℂ)) {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) :
    Integrable (schwartzExponentialTilt g κ R) := by
  have hconv : MellinConvergent
      (g : ℝ → ℂ) (κ : ℂ) := by
    apply schwartzRealLine_mellinConvergent_of_re_pos
    simpa using! hκ
  have hscaled : MellinConvergent
      (fun r : ℝ => g (R * r)) (κ : ℂ) :=
    (MellinConvergent.comp_mul_left hR).mpr hconv
  have hchange : Integrable (fun v : ℝ =>
      (1 * Real.exp v) •
        (((1 * Real.exp v : ℝ) : ℂ) ^
          ((κ : ℂ) - 1) •
            g (R * (1 * Real.exp v)))) := by
    apply (integrable_scaled_exp_change_Ioi
      (R := (1 : ℝ)) (by norm_num)
      (fun r : ℝ =>
        (r : ℂ) ^ ((κ : ℂ) - 1) • g (R * r))).mp
    exact hscaled
  have hpower (v : ℝ) :
      (Real.exp v : ℂ) *
        (Real.exp v : ℂ) ^ ((κ : ℂ) - 1) =
          (Real.exp (κ * v) : ℂ) := by
    have hbase : (Real.exp v : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero v)
    calc
      (Real.exp v : ℂ) *
          (Real.exp v : ℂ) ^ ((κ : ℂ) - 1) =
        (Real.exp v : ℂ) ^ (1 : ℂ) *
          (Real.exp v : ℂ) ^ ((κ : ℂ) - 1) := by
        rw [Complex.cpow_one]
      _ = (Real.exp v : ℂ) ^
          ((1 : ℂ) + ((κ : ℂ) - 1)) := by
        rw [Complex.cpow_add _ _ hbase]
      _ = (Real.exp v : ℂ) ^ (κ : ℂ) := by
        congr 1
        ring
      _ = (Real.exp (κ * v) : ℂ) := by
        rw [Complex.cpow_def_of_ne_zero hbase,
          ← Complex.ofReal_log (Real.exp_pos v).le,
          Real.log_exp, Complex.ofReal_exp]
        congr 1
        push_cast
        ring
  apply hchange.congr
  filter_upwards [] with v
  simp only [one_mul, smul_eq_mul, Complex.real_smul,
    schwartzExponentialTilt]
  rw [← mul_assoc, hpower]
theorem schwartzExponentialTilt_differentiable
    (g : 𝓢(ℝ, ℂ)) (κ R : ℝ) :
    Differentiable ℝ (schwartzExponentialTilt g κ R) := by
  unfold schwartzExponentialTilt
  have hexpreal :
      Differentiable ℝ (fun v : ℝ => Real.exp (κ * v)) := by
    fun_prop
  have hexp :
      Differentiable ℝ (fun v : ℝ =>
        (Real.exp (κ * v) : ℂ)) :=
    Complex.ofRealCLM.differentiable.comp hexpreal
  have hg : Differentiable ℝ (g : ℝ → ℂ) :=
    (g.smooth 1).differentiable (by norm_num)
  have hradius :
      Differentiable ℝ (fun v : ℝ => R * Real.exp v) := by
    fun_prop
  exact hexp.mul (hg.comp hradius)
theorem schwartzExponentialTilt_deriv
    (g : 𝓢(ℝ, ℂ)) (κ R v : ℝ) :
    deriv (schwartzExponentialTilt g κ R) v =
      (κ : ℂ) * schwartzExponentialTilt g κ R v +
        (R : ℂ) *
          schwartzExponentialTilt
            ((SchwartzMap.derivCLM ℂ ℂ) g)
            (κ + 1) R v := by
  have hlinear :
      HasDerivAt (fun u : ℝ => κ * u) κ v := by
    simpa using! (hasDerivAt_id v).const_mul κ
  have hexpreal :
      HasDerivAt (fun u : ℝ => Real.exp (κ * u))
        (κ * Real.exp (κ * v)) v := by
    convert! (Real.hasDerivAt_exp (κ * v)).comp v hlinear
      using 1; simp [mul_comm]
  have hexp :
      HasDerivAt (fun u : ℝ =>
        (Real.exp (κ * u) : ℂ))
        ((κ * Real.exp (κ * v) : ℝ) : ℂ) v :=
    hexpreal.ofReal_comp
  have hradius :
      HasDerivAt (fun u : ℝ => R * Real.exp u)
        (R * Real.exp v) v :=
    (Real.hasDerivAt_exp v).const_mul R
  have hprofile :
      HasDerivAt (fun u : ℝ => g (R * Real.exp u))
        ((R * Real.exp v) •
          deriv (g : ℝ → ℂ) (R * Real.exp v)) v := by
    simpa [Function.comp_def] using!
      (g.hasDerivAt (R * Real.exp v)).scomp v hradius
  have hder := (hexp.mul hprofile).deriv
  change deriv
      ((fun u : ℝ => (Real.exp (κ * u) : ℂ)) *
        (fun u : ℝ => g (R * Real.exp u))) v = _
  rw [hder]
  have hexpadd :
      Real.exp ((κ + 1) * v) =
        Real.exp (κ * v) * Real.exp v := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp [schwartzExponentialTilt, SchwartzMap.derivCLM_apply,
    Complex.real_smul, hexpadd]
  ring
theorem schwartzExponentialTilt_deriv_integrable
    (g : 𝓢(ℝ, ℂ)) {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) :
    Integrable (deriv (schwartzExponentialTilt g κ R)) := by
  let g' : 𝓢(ℝ, ℂ) :=
    (SchwartzMap.derivCLM ℂ ℂ) g
  have hzero := schwartzExponentialTilt_integrable g hκ hR
  have hone := schwartzExponentialTilt_integrable
    g' (show 0 < κ + 1 by linarith) hR
  have hsum :=
    (hzero.const_mul (κ : ℂ)).add
      (hone.const_mul (R : ℂ))
  apply hsum.congr
  filter_upwards [] with v
  exact (schwartzExponentialTilt_deriv g κ R v).symm
theorem schwartzExponentialTilt_deriv_deriv
    (g : 𝓢(ℝ, ℂ)) (κ R v : ℝ) :
    deriv (deriv (schwartzExponentialTilt g κ R)) v =
      (κ : ℂ) * deriv (schwartzExponentialTilt g κ R) v +
        (R : ℂ) * deriv
          (schwartzExponentialTilt
            ((SchwartzMap.derivCLM ℂ ℂ) g)
            (κ + 1) R) v := by
  let g' : 𝓢(ℝ, ℂ) :=
    (SchwartzMap.derivCLM ℂ ℂ) g
  have hderivfun :
      deriv (schwartzExponentialTilt g κ R) =
        (fun u : ℝ =>
          (κ : ℂ) * schwartzExponentialTilt g κ R u +
            (R : ℂ) *
              schwartzExponentialTilt g' (κ + 1) R u) := by
    funext u
    exact schwartzExponentialTilt_deriv g κ R u
  conv_lhs => rw [hderivfun]
  have hfirst :
      Differentiable ℝ
        (fun u : ℝ =>
          (κ : ℂ) * schwartzExponentialTilt g κ R u) :=
    (schwartzExponentialTilt_differentiable g κ R).const_mul
      (κ : ℂ)
  have hsecond :
      Differentiable ℝ
        (fun u : ℝ =>
          (R : ℂ) *
            schwartzExponentialTilt g' (κ + 1) R u) :=
    (schwartzExponentialTilt_differentiable
      g' (κ + 1) R).const_mul (R : ℂ)
  change deriv
      ((fun u : ℝ =>
        (κ : ℂ) * schwartzExponentialTilt g κ R u) +
        (fun u : ℝ =>
          (R : ℂ) *
            schwartzExponentialTilt g' (κ + 1) R u)) v = _
  rw [deriv_add hfirst.differentiableAt
    hsecond.differentiableAt,
    deriv_const_mul_field (κ : ℂ),
    deriv_const_mul_field (R : ℂ)]
theorem schwartzExponentialTilt_deriv_deriv_integrable
    (g : 𝓢(ℝ, ℂ)) {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) :
    Integrable (deriv (deriv (schwartzExponentialTilt g κ R))) := by
  let g' : 𝓢(ℝ, ℂ) :=
    (SchwartzMap.derivCLM ℂ ℂ) g
  have hzero :=
    schwartzExponentialTilt_deriv_integrable g hκ hR
  have hone :=
    schwartzExponentialTilt_deriv_integrable
      g' (show 0 < κ + 1 by linarith) hR
  have hsum :=
    (hzero.const_mul (κ : ℂ)).add
      (hone.const_mul (R : ℂ))
  apply hsum.congr
  filter_upwards [] with v
  exact (schwartzExponentialTilt_deriv_deriv g κ R v).symm
theorem schwartzExponentialTilt_deriv_differentiable
    (g : 𝓢(ℝ, ℂ)) (κ R : ℝ) :
    Differentiable ℝ
      (deriv (schwartzExponentialTilt g κ R)) := by
  let g' : 𝓢(ℝ, ℂ) :=
    (SchwartzMap.derivCLM ℂ ℂ) g
  have hderivfun :
      deriv (schwartzExponentialTilt g κ R) =
        (fun u : ℝ =>
          (κ : ℂ) * schwartzExponentialTilt g κ R u +
            (R : ℂ) *
              schwartzExponentialTilt g' (κ + 1) R u) := by
    funext u
    exact schwartzExponentialTilt_deriv g κ R u
  rw [hderivfun]
  exact
    ((schwartzExponentialTilt_differentiable
      g κ R).const_mul (κ : ℂ)).add
      ((schwartzExponentialTilt_differentiable
        g' (κ + 1) R).const_mul (R : ℂ))
theorem schwartzExponentialTilt_fourier_integrable
    (g : 𝓢(ℝ, ℂ)) {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) :
    Integrable (𝓕 (schwartzExponentialTilt g κ R) : ℝ → ℂ) :=
  integrable_fourier_of_integrable_two_derivatives
    (schwartzExponentialTilt g κ R)
    (schwartzExponentialTilt_integrable g hκ hR)
    (schwartzExponentialTilt_differentiable g κ R)
    (schwartzExponentialTilt_deriv_integrable g hκ hR)
    (schwartzExponentialTilt_deriv_differentiable g κ R)
    (schwartzExponentialTilt_deriv_deriv_integrable g hκ hR)
end
noncomputable section
def stripAngle (σ : ℝ) : ℝ :=
  Real.pi * (1 + σ) / 2
def stripPoissonKernel (σ T : ℝ) : ℝ :=
  Real.sin (stripAngle σ) /
    (4 * (Real.cosh (Real.pi * T / 2) - Real.cos (stripAngle σ)))
def stripBottomMass (σ : ℝ) : ℝ :=
  (1 - σ) / 2
end
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
def stripPoissonPrimitive (σ T : ℝ) : ℝ :=
  Real.arctan
      ((Real.exp (Real.pi * T / 2) - Real.cos (stripAngle σ)) /
        Real.sin (stripAngle σ)) / Real.pi
def stripComplexPoissonKernel (σ T : ℝ) : ℂ :=
  Complex.I *
      ((Complex.exp
          (((Real.pi * T / 2 : ℝ) : ℂ) +
            Complex.I * ((stripAngle σ : ℝ) : ℂ)) + 1) /
        (Complex.exp
          (((Real.pi * T / 2 : ℝ) : ℂ) +
            Complex.I * ((stripAngle σ : ℝ) : ℂ)) - 1)) /
    4
def stripSchwarzExponential (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  Complex.exp
    (((Real.pi : ℂ) *
      (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
        (2 * (ℓ : ℂ)))
def stripHolomorphicPoissonKernel (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  (Complex.I *
      ((Complex.exp
          (((Real.pi : ℂ) *
            (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
              (2 * (ℓ : ℂ))) + 1) /
        (Complex.exp
          (((Real.pi : ℂ) *
            (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
              (2 * (ℓ : ℂ))) - 1)) /
    4) / (ℓ : ℂ)
def stripRegularizedHolomorphicPoissonKernel
    (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  stripHolomorphicPoissonKernel ℓ z y +
    (if 0 ≤ y then Complex.I else -Complex.I) /
      ((4 * ℓ : ℝ) : ℂ)
def stripRegularizedHolomorphicPoissonKernelDeriv
    (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  -(Complex.I * (Real.pi : ℂ) *
      stripSchwarzExponential ℓ z y) /
    (4 * (ℓ : ℂ) ^ 2 *
      (stripSchwarzExponential ℓ z y - 1) ^ 2)
end
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
def profileNegativePart (φ : ℝ → ℝ) (v : ℝ) : ℝ :=
  max (-φ v) 0
def lowerGammaBoundaryLog (ℓ R y : ℝ) : ℝ :=
  ℓ * Real.log (Real.pi * R ^ 2) +
    Real.log ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ -
    Real.log ‖Complex.Gamma ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖
def lowerStripPoissonMajorant (ℓ R σ s : ℝ) : ℝ :=
  ∫ T : ℝ,
    stripPoissonKernel σ T *
      lowerGammaBoundaryLog ℓ R (s - ℓ * T)
def lowerCoth (x : ℝ) : ℝ :=
  Real.cosh x / Real.sinh x
def lowerGammaScaledPositivePart
    (d : ℕ) (c Y : ℝ) : ℝ :=
  max
    (lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y)) 0
def lowerRiemannLog (T x : ℝ) : ℝ :=
  Real.log (Real.sqrt (x ^ 2 + T ^ 2 / 4))
def lowerEndpointPhase (T : ℝ) : ℝ :=
  -Real.pi * |T| / 4 - (1 / 2 : ℝ) * Real.log (1 + T ^ 2 / 4) +
    |T| / 2 * Real.arctan (|T| / 2)
def lowerRiemannLogPrimitive (T x : ℝ) : ℝ :=
  x / 2 * Real.log (x ^ 2 + T ^ 2 / 4) - x +
    (|T| / 2) * Real.arctan (x / (|T| / 2))
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
def complexFrullaniSegment (z w : ℂ) (s : ℝ) : ℂ :=
  z + (s : ℂ) * (w - z)
def complexFrullaniKernel (z w : ℂ) (x : ℝ) : ℂ :=
  (Complex.exp (-z * (x : ℂ)) -
    Complex.exp (-w * (x : ℂ))) / (x : ℂ)
def complexWallisPhaseKernel (z : ℂ) (x : ℝ) : ℂ :=
  ((1 - Complex.exp (-(x : ℂ))) *
      Complex.exp (-z * (x : ℂ)) -
    (x : ℂ) * Complex.exp (-(x : ℂ))) /
      (x : ℂ) ^ 2
end
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
def stripNormalizedPoissonKernel (σ T : ℝ) : ℝ :=
  stripPoissonKernel σ T / stripBottomMass σ
def stripNormalizedPoissonExtension (σ T : ℝ) : ℝ :=
  (Real.pi / 4) *
    Real.sinc (Real.pi * (1 - σ) / 2) /
      (Real.cosh (Real.pi * T / 2) +
        Real.cos (Real.pi * (1 - σ) / 2))
def limitingStripPoissonDensity (T : ℝ) : ℝ :=
  Real.pi /
    (4 * (Real.cosh (Real.pi * T / 2) + 1))
def stripPoissonExponentialMajorant (T : ℝ) : ℝ :=
  (Real.pi / 2) *
    Real.exp (-(Real.pi / 2) * |T|)
def poissonLogistic (u : ℝ) : ℝ :=
  Real.exp (Real.pi * u) /
    (1 + Real.exp (Real.pi * u))
def poissonLogisticDensity (u : ℝ) : ℝ :=
  Real.pi * Real.exp (Real.pi * u) /
    (1 + Real.exp (Real.pi * u)) ^ 2
def lowerPoissonEndpointExpectation (σ : ℝ) : ℝ :=
  ∫ T : ℝ,
    stripNormalizedPoissonKernel σ T * lowerEndpointPhase T
def limitingPoissonEndpointExpectation : ℝ :=
  ∫ T : ℝ,
    limitingStripPoissonDensity T * lowerEndpointPhase T
def lowerWallisPhaseKernel (u t : ℝ) : ℝ :=
  ((1 - Real.exp (-t)) * Real.cos (u * t) -
    t * Real.exp (-t)) / t ^ 2
def lowerWallisRegularizedPhaseKernel (a u t : ℝ) : ℝ :=
  ((1 - Real.exp (-t)) * Real.exp (-a * t) *
      Real.cos (u * t) - t * Real.exp (-t)) / t ^ 2
def lowerWallisRegularizedPhaseMajorant (u t : ℝ) : ℝ :=
  if t ≤ 1 then |u| + 2 else 1 / t ^ 2 + Real.exp (-t)
def lowerWallisComplexLogPhase (z : ℂ) : ℝ :=
  (1 + z * Complex.log z -
    (z + 1) * Complex.log (z + 1)).re
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
def upperNegativeHalfGammaArgument (N : ℕ) (s : ℝ) : ℂ :=
  -((N : ℂ) + (1 / 2 : ℂ)) -
    Complex.I * ((s / 2 : ℝ) : ℂ)
def upperShellShortCoefficient (ε : ℝ) : ℝ :=
  shortEndpoint ε + (shortCutoff ε)⁻¹
def upperShellMarginRatio (ε : ℝ) : ℝ :=
  5000 * upperShellShortCoefficient ε *
      Real.exp ((ε / 2) * shortEndpoint ε) /
    (shellWeight ε *
      Real.exp ((ε / 2) * shellLocation ε))
def upperShortShellDamping (ε ℓ δ T : ℝ) : ℝ :=
  ℓ * ∫ a in shortCutoff ε..shortEndpoint ε,
    (-shortShellDensity ε a) *
      Real.cosh ((1 + δ) * a) *
        (1 - Real.cos (a * T))
theorem eventually_upper_shortCutoff_le_shortEndpoint :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      shortCutoff ε ≤ shortEndpoint ε := by
  have hlower := tendsto_shortCutoff.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hupper := tendsto_shortEndpoint.eventually_ge_atTop
    (1 : ℝ)
  filter_upwards [hlower, hupper] with ε hl hu
  linarith
def upperPositiveShellVariance (ε δ : ℝ) : ℝ :=
  ∫ a in shellLocation ε..shellLocation ε + 1,
    positiveShellDensity ε a * a ^ 2 *
      Real.cosh ((1 + δ) * a)
def upperShortShellVariance (ε δ : ℝ) : ℝ :=
  ∫ a in shortCutoff ε..shortEndpoint ε,
    (-shortShellDensity ε a) * a ^ 2 *
      Real.cosh ((1 + δ) * a)
def upperNetShellVariance (ε δ : ℝ) : ℝ :=
  upperPositiveShellVariance ε δ -
    upperShortShellVariance ε δ
def upperPositiveShellThirdMoment (ε δ : ℝ) : ℝ :=
  ∫ a in shellLocation ε..shellLocation ε + 1,
    positiveShellDensity ε a * a ^ 3 *
      Real.cosh ((1 + δ) * a)
def upperShortShellThirdMoment (ε δ : ℝ) : ℝ :=
  ∫ a in shortCutoff ε..shortEndpoint ε,
    (-shortShellDensity ε a) * a ^ 3 *
      Real.cosh ((1 + δ) * a)
def upperNetShellThirdMoment (ε δ : ℝ) : ℝ :=
  upperPositiveShellThirdMoment ε δ +
    upperShortShellThirdMoment ε δ
def upperGammaMeasureDensity (ℓ η a : ℝ) : ℝ :=
  Real.exp (-η * a) /
    (a * (1 - Real.exp (-(2 * a / ℓ))))
def upperGammaVariance (ℓ η : ℝ) : ℝ :=
  ℓ⁻¹ * ∫ a : ℝ in Set.Ioi 0,
    a ^ 2 * upperGammaMeasureDensity ℓ η a
def upperGammaThirdMoment (ℓ η : ℝ) : ℝ :=
  ℓ⁻¹ * ∫ a : ℝ in Set.Ioi 0,
    a ^ 3 * upperGammaMeasureDensity ℓ η a
def saddleShellDerivativeOne (ε : ℝ) : ℝ :=
  (∫ a in shortCutoff ε..shortEndpoint ε,
    shortShellDensity ε a * a * Real.sinh a) +
  (∫ a in shellLocation ε..shellLocation ε + 1,
    positiveShellDensity ε a * a * Real.sinh a)
def saddleSmallRadiusVariable (ε r : ℝ) : ℝ :=
  Real.pi * Real.exp (2 * saddleShellDerivativeOne ε) * r ^ 2
def plusSaddleSmallRadiusCoefficient
    (ε ℓ : ℝ) (n : ℕ) : ℝ :=
  Real.exp
      (ℓ *
        (realHyperbolicShellPhase ε
          (1 + 2 * (n : ℝ) / ℓ) -
            realHyperbolicShellPhase ε 1) -
        2 * (n : ℝ) * saddleShellDerivativeOne ε) *
    ((beta ε - (2 * (n : ℝ) / ℓ) *
        (2 + 2 * (n : ℝ) / ℓ) ^ 2) /
      beta ε)
def upperGammaDampingIntegrand (ℓ η T a : ℝ) : ℝ :=
  (1 - Real.cos (a * T)) *
    upperGammaMeasureDensity ℓ η a
def upperGammaDamping (ℓ η T : ℝ) : ℝ :=
  ∫ a : ℝ in Ioi 0,
    upperGammaDampingIntegrand ℓ η T a
def upperSaddleDamping (ε ℓ δ T : ℝ) : ℝ :=
  upperGammaDamping ℓ (2 + δ) T +
    positiveShellDamping ε ℓ δ T -
      upperShortShellDamping ε ℓ δ T
def upperSaddleVariance (ε ℓ δ : ℝ) : ℝ :=
  upperGammaVariance ℓ (2 + δ) +
    upperNetShellVariance ε δ
def upperSaddleThirdMoment (ε ℓ δ : ℝ) : ℝ :=
  upperGammaThirdMoment ℓ (2 + δ) +
    upperNetShellThirdMoment ε δ
def upperSaddleShellThirdCoefficient (ε : ℝ) : ℝ :=
  shellLocation ε + 1 + shortEndpoint ε / 100
def upperFirstBranchSaddleDamping
    (ε ℓ u T : ℝ) : ℝ :=
  upperGammaDamping ℓ (1 + u) T +
    positiveShellDamping ε ℓ (u - 1) T -
      upperShortShellDamping ε ℓ (u - 1) T
end
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology
def radialCriticalLogProfile {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (u : ℝ) : ℂ :=
  Real.exp (-((d : ℝ) / 2) * u) •
    radialProfile hd f (Real.exp (-u))
theorem radialCriticalLogProfile_eq_reflected_tilt {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (u : ℝ) :
    radialCriticalLogProfile hd f u =
      schwartzExponentialTilt (radialSchwartzProfile hd f)
        ((d : ℝ) / 2) 1 (-u) := by
  simp [radialCriticalLogProfile, schwartzExponentialTilt,
    radialSchwartzProfile_apply, mul_neg]
theorem radialCriticalLogProfile_integrable {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) :
    Integrable (radialCriticalLogProfile hd f) := by
  have hdimension : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast hd) (by norm_num)
  have h := (schwartzExponentialTilt_integrable
    (radialSchwartzProfile hd f) hdimension
    (show (0 : ℝ) < 1 by norm_num)).comp_neg
  apply h.congr
  filter_upwards [] with u
  exact (radialCriticalLogProfile_eq_reflected_tilt hd f u).symm
theorem radialCriticalLogProfile_continuous {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) :
    Continuous (radialCriticalLogProfile hd f) := by
  unfold radialCriticalLogProfile
  exact (by fun_prop :
    Continuous (fun u : ℝ => Real.exp (-((d : ℝ) / 2) * u))).smul
      ((radialProfile_continuous hd f).comp
        (by fun_prop : Continuous (fun u : ℝ => Real.exp (-u))))
theorem radialCriticalLogProfile_fourier_integrable {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) :
    Integrable (𝓕 (radialCriticalLogProfile hd f) : ℝ → ℂ) := by
  have hdimension : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast hd) (by norm_num)
  let G : ℝ → ℂ :=
    schwartzExponentialTilt (radialSchwartzProfile hd f)
      ((d : ℝ) / 2) 1
  have hG : Integrable (𝓕 G : ℝ → ℂ) :=
    schwartzExponentialTilt_fourier_integrable
      (radialSchwartzProfile hd f) hdimension
      (show (0 : ℝ) < 1 by norm_num)
  have hneg := hG.comp_neg
  apply hneg.congr
  filter_upwards [] with u
  have hprofile :
      radialCriticalLogProfile hd f =
        (fun v : ℝ => G (-v)) := by
    funext v
    exact radialCriticalLogProfile_eq_reflected_tilt hd f v
  rw [hprofile]
  simpa [Function.comp_def, G] using!
    (Real.fourier_comp_linearIsometry
      (LinearIsometryEquiv.neg ℝ) G u).symm
theorem radialMellinFrequency_eq_criticalLogFourier {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (t : ℝ) :
    radialMellinFrequency hd f t =
      (𝓕 (radialCriticalLogProfile hd f) : ℝ → ℂ)
        (-t / (2 * Real.pi)) := by
  exact radialMellinFrequency_eq_fourier hd f t
theorem plusSaddleFourierData_continuous {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Continuous (plusSaddleFourierData ε ℓ) := by
  unfold plusSaddleFourierData
  exact (plusSaddleSpectrum_continuous hε hℓ horder).comp
    (by fun_prop)
theorem minusSaddleFourierData_continuous {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Continuous (minusSaddleFourierData ε ℓ) := by
  unfold minusSaddleFourierData
  exact (minusSaddleSpectrum_continuous hε hℓ horder).comp
    (by fun_prop)
theorem plusSaddleFourierData_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Integrable (plusSaddleFourierData ε ℓ) := by
  have hnorm : Integrable
      (fun y : ℝ => ‖plusSaddleFourierData ε ℓ y‖) := by
    simpa using!
      plusSaddleFourierData_norm_moment_integrable hε hℓ horder 0
  exact (integrable_norm_iff
    (plusSaddleFourierData_continuous
      hε hℓ horder).aestronglyMeasurable).mp hnorm
theorem minusSaddleFourierData_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Integrable (minusSaddleFourierData ε ℓ) := by
  have hnorm : Integrable
      (fun y : ℝ => ‖minusSaddleFourierData ε ℓ y‖) := by
    simpa using!
      minusSaddleFourierData_norm_moment_integrable hε hℓ horder 0
  exact (integrable_norm_iff
    (minusSaddleFourierData_continuous
      hε hℓ horder).aestronglyMeasurable).mp hnorm
theorem radialProfile_eq_plusSaddleProfile_of_source
    {ε : ℝ} {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = plusSaddleFunction ε d x)
    {r : ℝ} (hr : 0 ≤ r) :
    radialProfile hd f r = plusSaddleProfile ε ((d : ℝ) / 2) r := by
  unfold radialProfile
  rw [hf]
  simp [plusSaddleFunction, norm_smul,
    norm_radialUnitDirection hd, abs_of_nonneg hr]
theorem radialProfile_eq_minusSaddleProfile_of_source
    {ε : ℝ} {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = minusSaddleFunction ε d x)
    {r : ℝ} (hr : 0 ≤ r) :
    radialProfile hd f r = minusSaddleProfile ε ((d : ℝ) / 2) r := by
  unfold radialProfile
  rw [hf]
  simp [minusSaddleFunction, norm_smul,
    norm_radialUnitDirection hd, abs_of_nonneg hr]
theorem exp_neg_rpow_neg_half_dimension {d : ℕ} (u : ℝ) :
    (Real.exp (-u)) ^ (-((d : ℝ) / 2)) =
      Real.exp (((d : ℝ) / 2) * u) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos (-u)), Real.log_exp]
  congr 1
  ring
theorem plusSaddleCriticalLogProfile_eq_fourierInv
    {ε : ℝ} {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = plusSaddleFunction ε d x) :
    radialCriticalLogProfile hd f =
      (𝓕⁻ (plusSaddleFourierData ε ((d : ℝ) / 2)) : ℝ → ℂ) := by
  funext u
  unfold radialCriticalLogProfile
  rw [radialProfile_eq_plusSaddleProfile_of_source
    hd f hf (Real.exp_pos (-u)).le]
  rw [plusSaddleProfile_eq_fourier ε ((d : ℝ) / 2)
    (Real.exp_pos (-u))]
  rw [exp_neg_rpow_neg_half_dimension,
    Real.log_exp, Real.fourierInv_eq_fourier_neg]
  simp only [Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  simp
theorem minusSaddleCriticalLogProfile_eq_fourierInv
    {ε : ℝ} {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = minusSaddleFunction ε d x) :
    radialCriticalLogProfile hd f =
      (𝓕⁻ (minusSaddleFourierData ε ((d : ℝ) / 2)) : ℝ → ℂ) := by
  funext u
  unfold radialCriticalLogProfile
  rw [radialProfile_eq_minusSaddleProfile_of_source
    hd f hf (Real.exp_pos (-u)).le]
  rw [minusSaddleProfile_eq_fourier ε ((d : ℝ) / 2)
    (Real.exp_pos (-u))]
  rw [exp_neg_rpow_neg_half_dimension,
    Real.log_exp, Real.fourierInv_eq_fourier_neg]
  simp only [Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  simp
theorem plusSaddleFourierData_fourier_integrable_of_source
    {ε : ℝ} {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = plusSaddleFunction ε d x) :
    Integrable
      (𝓕 (plusSaddleFourierData ε ((d : ℝ) / 2)) : ℝ → ℂ) := by
  have hlog := (radialCriticalLogProfile_integrable hd f).comp_neg
  apply hlog.congr
  filter_upwards [] with u
  have h := congrFun
    (plusSaddleCriticalLogProfile_eq_fourierInv hd f hf) (-u)
  simpa [Real.fourierInv_eq_fourier_neg] using! h
theorem minusSaddleFourierData_fourier_integrable_of_source
    {ε : ℝ} {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = minusSaddleFunction ε d x) :
    Integrable
      (𝓕 (minusSaddleFourierData ε ((d : ℝ) / 2)) : ℝ → ℂ) := by
  have hlog := (radialCriticalLogProfile_integrable hd f).comp_neg
  apply hlog.congr
  filter_upwards [] with u
  have h := congrFun
    (minusSaddleCriticalLogProfile_eq_fourierInv hd f hf) (-u)
  simpa [Real.fourierInv_eq_fourier_neg] using! h
theorem plusSaddle_radialMellinFrequency_of_source
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = plusSaddleFunction ε d x)
    (t : ℝ) :
    radialMellinFrequency hd f t =
      plusSaddleSpectrum ε ((d : ℝ) / 2) t := by
  have hdimension : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast hd) (by norm_num)
  have hdata := plusSaddleFourierData_integrable
    hε hdimension horder
  have hfourier := plusSaddleFourierData_fourier_integrable_of_source
    hd f hf
  have hcontinuous := plusSaddleFourierData_continuous
    hε hdimension horder
  rw [radialMellinFrequency_eq_criticalLogFourier,
    plusSaddleCriticalLogProfile_eq_fourierInv hd f hf]
  rw [hdata.fourier_fourierInv_eq hfourier
    hcontinuous.continuousAt]
  unfold plusSaddleFourierData
  congr 1
  field_simp [Real.pi_ne_zero]
theorem minusSaddle_radialMellinFrequency_of_source
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = minusSaddleFunction ε d x)
    (t : ℝ) :
    radialMellinFrequency hd f t =
      minusSaddleSpectrum ε ((d : ℝ) / 2) t := by
  have hdimension : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast hd) (by norm_num)
  have hdata := minusSaddleFourierData_integrable
    hε hdimension horder
  have hfourier := minusSaddleFourierData_fourier_integrable_of_source
    hd f hf
  have hcontinuous := minusSaddleFourierData_continuous
    hε hdimension horder
  rw [radialMellinFrequency_eq_criticalLogFourier,
    minusSaddleCriticalLogProfile_eq_fourierInv hd f hf]
  rw [hdata.fourier_fourierInv_eq hfourier
    hcontinuous.continuousAt]
  unfold minusSaddleFourierData
  congr 1
  field_simp [Real.pi_ne_zero]
theorem radialMellinFrequency_injective {d : ℕ}
    (hd : 0 < d) {f g : TestFunction d}
    (hf : IsRadial f) (hg : IsRadial g)
    (hfrequency : ∀ t : ℝ,
      radialMellinFrequency hd f t =
        radialMellinFrequency hd g t) :
    f = g := by
  have hfourier :
      (𝓕 (radialCriticalLogProfile hd f) : ℝ → ℂ) =
        (𝓕 (radialCriticalLogProfile hd g) : ℝ → ℂ) := by
    funext ξ
    have h := hfrequency (-(2 * Real.pi * ξ))
    rw [radialMellinFrequency_eq_criticalLogFourier,
      radialMellinFrequency_eq_criticalLogFourier] at h
    convert! h using 1 <;> field_simp [Real.pi_ne_zero]
  have hlog : radialCriticalLogProfile hd f =
      radialCriticalLogProfile hd g := by
    funext u
    calc
      radialCriticalLogProfile hd f u =
          (𝓕⁻ (𝓕 (radialCriticalLogProfile hd f) : ℝ → ℂ) :
            ℝ → ℂ) u :=
        ((radialCriticalLogProfile_integrable hd f).fourierInv_fourier_eq
          (radialCriticalLogProfile_fourier_integrable hd f)
          (radialCriticalLogProfile_continuous hd f).continuousAt).symm
      _ = (𝓕⁻ (𝓕 (radialCriticalLogProfile hd g) : ℝ → ℂ) :
            ℝ → ℂ) u := by rw [hfourier]
      _ = radialCriticalLogProfile hd g u :=
        (radialCriticalLogProfile_integrable hd g).fourierInv_fourier_eq
          (radialCriticalLogProfile_fourier_integrable hd g)
          (radialCriticalLogProfile_continuous hd g).continuousAt
  have hpositive (r : ℝ) (hr : 0 < r) :
      radialProfile hd f r = radialProfile hd g r := by
    have h := congrFun hlog (-Real.log r)
    simp only [radialCriticalLogProfile, neg_neg,
      Real.exp_log hr, Complex.real_smul] at h
    apply mul_left_cancel₀
      (Complex.ofReal_ne_zero.mpr
        (Real.exp_ne_zero (-((d : ℝ) / 2) * -Real.log r)))
    exact h
  have heventually :
      radialProfile hd f =ᶠ[𝓝[>] (0 : ℝ)]
        radialProfile hd g := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hpositive r hr
  have hleft :
      Tendsto (radialProfile hd f)
        (𝓝[>] (0 : ℝ)) (𝓝 (radialProfile hd f 0)) :=
    (radialProfile_continuous hd f).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hright :
      Tendsto (radialProfile hd f)
        (𝓝[>] (0 : ℝ)) (𝓝 (radialProfile hd g 0)) :=
    ((radialProfile_continuous hd g).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr' heventually.symm
  have hzero : radialProfile hd f 0 = radialProfile hd g 0 :=
    tendsto_nhds_unique hleft hright
  apply SchwartzMap.ext
  intro x
  by_cases hx : x = 0
  · subst x
    simpa using! hzero
  · have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    calc
      f x = radialProfile hd f ‖x‖ :=
        (radialProfile_norm hd f hf x).symm
      _ = radialProfile hd g ‖x‖ := hpositive ‖x‖ hr
      _ = g x := radialProfile_norm hd g hg x
theorem plusSaddle_radial_of_source {ε : ℝ} {d : ℕ}
    (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = plusSaddleFunction ε d x) :
    IsRadial f := by
  intro x y hxy
  rw [hf x, hf y]
  exact plusSaddleFunction_radial ε d x y hxy
theorem minusSaddle_radial_of_source {ε : ℝ} {d : ℕ}
    (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = minusSaddleFunction ε d x) :
    IsRadial f := by
  intro x y hxy
  rw [hf x, hf y]
  exact minusSaddleFunction_radial ε d x y hxy
theorem plusSaddle_real_of_source {ε : ℝ} {d : ℕ}
    (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = plusSaddleFunction ε d x) :
    IsRealValued f := by
  intro x
  rw [hf x]
  exact plusSaddleFunction_real ε d x
theorem minusSaddle_real_of_source {ε : ℝ} {d : ℕ}
    (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = minusSaddleFunction ε d x) :
    IsRealValued f := by
  intro x
  rw [hf x]
  exact minusSaddleFunction_real ε d x
theorem saddleSource_fourier_minus_eq_plus
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x) :
    (𝓕 fminus : TestFunction d) = fplus := by
  have hdimension : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast hd) (by norm_num)
  have hrminus : IsRadial fminus :=
    minusSaddle_radial_of_source fminus hminus
  have hrplus : IsRadial fplus :=
    plusSaddle_radial_of_source fplus hplus
  apply radialMellinFrequency_injective hd
    (gaussianMellin_fourier_radial hrminus) hrplus
  intro t
  calc
    radialMellinFrequency hd
        (𝓕 fminus : TestFunction d) t =
      mellinMultiplier ((d : ℝ) / 2) t *
        radialMellinFrequency hd fminus (-t) :=
      radialMellinMultiplier hd fminus hrminus t
    _ = mellinMultiplier ((d : ℝ) / 2) t *
        minusSaddleSpectrum ε ((d : ℝ) / 2) (-t) := by
      rw [minusSaddle_radialMellinFrequency_of_source
        hε hd horder fminus hminus]
    _ = plusSaddleSpectrum ε ((d : ℝ) / 2) t :=
      mellinMultiplier_mul_minusSaddleSpectrum_neg hdimension t
    _ = radialMellinFrequency hd fplus t :=
      (plusSaddle_radialMellinFrequency_of_source
        hε hd horder fplus hplus t).symm
theorem saddleSource_zero_pos
    {ε : ℝ} (hε : 0 < ε) {d : ℕ}
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x) :
    0 < (fminus (0 : Euclidean d)).re ∧
      0 < (fplus (0 : Euclidean d)).re := by
  rw [hminus, hplus]
  exact (saddleFunction_zero_pos hε d).symm
theorem saddleSource_zero_eq {ε : ℝ} {d : ℕ}
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x) :
    fminus (0 : Euclidean d) = fplus (0 : Euclidean d) := by
  rw [hminus, hplus, minusSaddleFunction_zero,
    plusSaddleFunction_zero]
def saddleSourceAdmissible
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {R : ℝ} (hR : 0 < R)
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x)
    (hplusnonneg : ∀ x : Euclidean d,
      0 ≤ (plusSaddleFunction ε d x).re)
    (hminusoutside : ∀ x : Euclidean d,
      R ≤ ‖x‖ → (minusSaddleFunction ε d x).re ≤ 0) :
    Admissible d := by
  have hfourier : (𝓕 fminus : TestFunction d) = fplus :=
    saddleSource_fourier_minus_eq_plus
      hε hd horder fminus fplus hminus hplus
  have hrealplus : IsRealValued fplus :=
    plusSaddle_real_of_source fplus hplus
  have hnonneg (ξ : Euclidean d) : 0 ≤ (fplus ξ).re := by
    rw [hplus ξ]
    exact hplusnonneg ξ
  have hzero : 0 < (fplus (0 : Euclidean d)).re :=
    (saddleSource_zero_pos hε fminus fplus hminus hplus).2
  refine
    { function := dilate fminus R hR
      real := (minusSaddle_real_of_source fminus hminus).dilate R hR
      radial := (minusSaddle_radial_of_source fminus hminus).dilate R hR
      fourier_real := ?_
      fourier_nonneg := ?_
      fourier_zero_pos := ?_
      outside_nonpos := ?_ }
  · intro ξ
    rw [fourier_dilate_apply, hfourier, Complex.smul_im,
      hrealplus (R⁻¹ • ξ)]
    simp
  · intro ξ
    rw [fourier_dilate_apply, hfourier, Complex.smul_re]
    simpa [smul_eq_mul] using!
      mul_nonneg
        (inv_nonneg.mpr (pow_nonneg hR.le d))
        (hnonneg (R⁻¹ • ξ))
  · rw [fourier_dilate_zero, hfourier, Complex.smul_re]
    simpa [smul_eq_mul] using!
      mul_pos (inv_pos.mpr (pow_pos hR d)) hzero
  · intro x hx
    change (fminus (R • x)).re ≤ 0
    rw [hminus]
    apply hminusoutside
    have hscaled := mul_le_mul_of_nonneg_left hx hR.le
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hR] using! hscaled
@[simp] theorem saddleSourceAdmissible_function
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {R : ℝ} (hR : 0 < R)
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x)
    (hplusnonneg : ∀ x : Euclidean d,
      0 ≤ (plusSaddleFunction ε d x).re)
    (hminusoutside : ∀ x : Euclidean d,
      R ≤ ‖x‖ → (minusSaddleFunction ε d x).re ≤ 0) :
    (saddleSourceAdmissible hε hd horder hR
      fminus fplus hminus hplus hplusnonneg
      hminusoutside).function = dilate fminus R hR := by
  rfl
theorem saddleSourceAdmissible_quotient
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {R : ℝ} (hR : 0 < R)
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x)
    (hplusnonneg : ∀ x : Euclidean d,
      0 ≤ (plusSaddleFunction ε d x).re)
    (hminusoutside : ∀ x : Euclidean d,
      R ≤ ‖x‖ → (minusSaddleFunction ε d x).re ≤ 0) :
    quotient (saddleSourceAdmissible hε hd horder hR
      fminus fplus hminus hplus hplusnonneg
      hminusoutside) = R ^ d := by
  have hfourier : (𝓕 fminus : TestFunction d) = fplus :=
    saddleSource_fourier_minus_eq_plus
      hε hd horder fminus fplus hminus hplus
  have hzero : 0 < (fplus (0 : Euclidean d)).re :=
    (saddleSource_zero_pos hε fminus fplus hminus hplus).2
  have hpow : R ^ d ≠ 0 := pow_ne_zero d hR.ne'
  unfold quotient
  rw [saddleSourceAdmissible_function
    hε hd horder hR fminus fplus hminus hplus
    hplusnonneg hminusoutside]
  rw [dilate_zero]
  change (fminus (0 : Euclidean d)).re /
    ((𝓕 (dilate fminus R hR) : TestFunction d)
      (0 : Euclidean d)).re = R ^ d
  rw [fourier_dilate_zero, hfourier,
    saddleSource_zero_eq fminus fplus hminus hplus,
    Complex.smul_re]
  simp only [smul_eq_mul]
  field_simp [hpow, hzero.ne']
theorem saddleSourceAdmissible_normalizedCost
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {R : ℝ} (hR : 0 < R)
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x)
    (hplusnonneg : ∀ x : Euclidean d,
      0 ≤ (plusSaddleFunction ε d x).re)
    (hminusoutside : ∀ x : Euclidean d,
      R ≤ ‖x‖ → (minusSaddleFunction ε d x).re ≤ 0) :
    normalizedCost (saddleSourceAdmissible hε hd horder hR
      fminus fplus hminus hplus hplusnonneg
      hminusoutside) = R / Real.sqrt (d : ℝ) := by
  calc
    normalizedCost (saddleSourceAdmissible hε hd horder hR
        fminus fplus hminus hplus hplusnonneg
        hminusoutside) =
      (R ^ d : ℝ) ^ ((d : ℝ)⁻¹) /
        Real.sqrt (d : ℝ) := by
      unfold normalizedCost
      rw [saddleSourceAdmissible_quotient
        hε hd horder hR fminus fplus hminus hplus
        hplusnonneg hminusoutside]
    _ = R / Real.sqrt (d : ℝ) := by
      congr 1
      rw [← Real.rpow_natCast_mul hR.le]
      rw [mul_inv_cancel₀ (by exact_mod_cast hd.ne'),
        Real.rpow_one]
def saddleDigamma (x : ℝ) : ℝ :=
  deriv (Real.log ∘ Real.Gamma) x
def saddleLogRadius (ε : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  -(Real.log Real.pi) / 2 +
    saddleDigamma (((d : ℝ) / 2) * (1 + u) / 2) / 2 +
    (∫ a in shortCutoff ε..shortEndpoint ε,
      shortShellDensity ε a * a * Real.sinh (u * a)) +
    (∫ a in shellLocation ε..shellLocation ε + 1,
      positiveShellDensity ε a * a * Real.sinh (u * a))
def saddleSourceRadius (ε : ℝ) (d : ℕ) : ℝ :=
  Real.exp (saddleLogRadius ε d (1 + ε / 4))
theorem saddleSourceRadius_pos (ε : ℝ) (d : ℕ) :
    0 < saddleSourceRadius ε d := by
  exact Real.exp_pos _
theorem saddleLogGamma_add_one {x : ℝ} (hx : 0 < x) :
    (Real.log ∘ Real.Gamma) (x + 1) =
      (Real.log ∘ Real.Gamma) x + Real.log x := by
  simp only [Function.comp_apply, Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  ring
theorem saddleLogGamma_differentiableAt {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (Real.log ∘ Real.Gamma) x := by
  exact (Real.differentiableAt_Gamma
    (fun n => ne_of_gt (by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith))).log (Real.Gamma_pos_of_pos hx).ne'
theorem saddleDigamma_bounds {x : ℝ} (hx : 1 < x) :
    Real.log (x - 1) ≤ saddleDigamma x ∧
      saddleDigamma x ≤ Real.log x := by
  have hxpositive : 0 < x := by linarith
  have hxprevious : 0 < x - 1 := by linarith
  have hnext : 0 < x + 1 := by linarith
  have hdiff := saddleLogGamma_differentiableAt hxpositive
  constructor
  · have hconv := Real.convexOn_log_Gamma.slope_le_deriv
      (show x - 1 ∈ Ioi (0 : ℝ) from hxprevious)
      (show x ∈ Ioi (0 : ℝ) from hxpositive)
      (show x - 1 < x by linarith) hdiff
    have hrec := saddleLogGamma_add_one hxprevious
    have hshift : (x - 1) + 1 = x := by ring
    rw [hshift] at hrec
    unfold saddleDigamma
    rw [slope_def_field] at hconv
    have hden : x - (x - 1) = (1 : ℝ) := by ring
    rw [hden, div_one, hrec] at hconv
    simpa using! hconv
  · have hconv := Real.convexOn_log_Gamma.deriv_le_slope
      (show x ∈ Ioi (0 : ℝ) from hxpositive)
      (show x + 1 ∈ Ioi (0 : ℝ) from hnext)
      (show x < x + 1 by linarith) hdiff
    have hrec := saddleLogGamma_add_one hxpositive
    unfold saddleDigamma
    rw [slope_def_field] at hconv
    have hden : (x + 1) - x = (1 : ℝ) := by ring
    rw [hden, div_one, hrec] at hconv
    simpa using! hconv
theorem tendsto_saddleDigamma_sub_log :
    Tendsto (fun x : ℝ => saddleDigamma x - Real.log x)
      atTop (𝓝 (0 : ℝ)) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹)
      atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have hargument : Tendsto (fun x : ℝ => 1 - x⁻¹)
      atTop (𝓝 (1 : ℝ)) := by
    simpa using! (tendsto_const_nhds.sub hinv)
  have hlog : Tendsto (fun x : ℝ =>
      Real.log (1 - x⁻¹)) atTop (𝓝 (0 : ℝ)) := by
    convert! (Real.continuousAt_log
      (show (1 : ℝ) ≠ 0 by norm_num)).tendsto.comp
        hargument using 1
    all_goals simp
  have hlower : Tendsto (fun x : ℝ =>
      Real.log (x - 1) - Real.log x)
      atTop (𝓝 (0 : ℝ)) := by
    refine hlog.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hxzero : x ≠ 0 := by linarith
    have hxprevious : x - 1 ≠ 0 := by linarith
    rw [← Real.log_div hxprevious hxzero]
    congr 1
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower (tendsto_const_nhds (x := (0 : ℝ))) ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact sub_le_sub_right (saddleDigamma_bounds hx).1 _
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact sub_nonpos.mpr (saddleDigamma_bounds hx).2
theorem saddle_exp_half_log_eq_sqrt {x : ℝ} (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [← Real.log_sqrt hx.le,
    Real.exp_log (Real.sqrt_pos.2 hx)]
def saddleCriticalGammaArgument (ε : ℝ) (d : ℕ) : ℝ :=
  ((d : ℝ) / 2) * (2 + ε / 4) / 2
theorem saddleCriticalGammaArgument_pos {ε : ℝ}
    (hε : 0 < ε) {d : ℕ} (hd : 0 < d) :
    0 < saddleCriticalGammaArgument ε d := by
  unfold saddleCriticalGammaArgument
  positivity
theorem tendsto_saddleCriticalGammaArgument_atTop
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (saddleCriticalGammaArgument ε)
      atTop atTop := by
  have hc : 0 < (2 + ε / 4) / 4 := by positivity
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hc
  refine h.congr' ?_
  filter_upwards [] with d
  unfold saddleCriticalGammaArgument
  ring
theorem saddleLogRadius_critical_eq (ε : ℝ) (d : ℕ) :
    saddleLogRadius ε d (1 + ε / 4) =
      -(Real.log Real.pi) / 2 +
        saddleDigamma (saddleCriticalGammaArgument ε d) / 2 +
        shortShellRadiusContribution ε +
        positiveShellRadiusContribution ε := by
  unfold saddleLogRadius saddleCriticalGammaArgument
    shortShellRadiusContribution shortShellRadiusIntegrand
    positiveShellRadiusContribution
  congr 2
  ring_nf
theorem saddleSourceRadius_div_sqrt_eq
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d) :
    saddleSourceRadius ε d / Real.sqrt (d : ℝ) =
      Real.exp ((saddleDigamma (saddleCriticalGammaArgument ε d) -
          Real.log (saddleCriticalGammaArgument ε d)) / 2) *
        limitingSaddleRadius ε := by
  let a : ℝ := 2 + ε / 4
  let m : ℝ := saddleCriticalGammaArgument ε d
  let S : ℝ := shortShellRadiusContribution ε +
    positiveShellRadiusContribution ε
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hm : 0 < m := saddleCriticalGammaArgument_pos hε hd
  have hquotient : 0 < a / (4 * Real.pi) := by positivity
  have hmformula : m = (d : ℝ) * a / 4 := by
    try dsimp [m, a, saddleCriticalGammaArgument]
    ring
  have hlogm : Real.log m =
      Real.log (d : ℝ) + Real.log a - Real.log (4 : ℝ) := by
    rw [hmformula,
      Real.log_div (mul_ne_zero hdreal.ne' ha.ne')
        (by norm_num : (4 : ℝ) ≠ 0),
      Real.log_mul hdreal.ne' ha.ne']
  have hlogquotient :
      Real.log (a / (4 * Real.pi)) =
        Real.log a - Real.log (4 : ℝ) - Real.log Real.pi := by
    rw [Real.log_div ha.ne'
      (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0)
        Real.pi_ne_zero),
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        Real.pi_ne_zero]
    ring
  have hv : saddleLogRadius ε d (1 + ε / 4) =
      -(Real.log Real.pi) / 2 +
        saddleDigamma m / 2 + S := by
    rw [saddleLogRadius_critical_eq]
    try dsimp [m, S]
    ring
  calc
    saddleSourceRadius ε d / Real.sqrt (d : ℝ) =
      Real.exp
        (-(Real.log Real.pi) / 2 +
          saddleDigamma m / 2 + S -
          Real.log (d : ℝ) / 2) := by
      unfold saddleSourceRadius
      rw [hv, ← saddle_exp_half_log_eq_sqrt hdreal,
        ← Real.exp_sub]
    _ = Real.exp
        ((saddleDigamma m - Real.log m) / 2 +
          Real.log (a / (4 * Real.pi)) / 2 + S) := by
      congr 1
      rw [hlogm, hlogquotient]
      ring
    _ = Real.exp ((saddleDigamma m - Real.log m) / 2) *
          Real.sqrt (a / (4 * Real.pi)) * Real.exp S := by
      rw [Real.exp_add, Real.exp_add,
        saddle_exp_half_log_eq_sqrt hquotient]
    _ = Real.exp
          ((saddleDigamma (saddleCriticalGammaArgument ε d) -
            Real.log (saddleCriticalGammaArgument ε d)) / 2) *
          limitingSaddleRadius ε := by
      unfold limitingSaddleRadius
      try dsimp [m, a, S]
      ring
theorem tendsto_saddleSourceRadius_normalized
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun d : ℕ =>
        saddleSourceRadius ε d / Real.sqrt (d : ℝ))
      atTop (𝓝 (limitingSaddleRadius ε)) := by
  have hargument := tendsto_saddleDigamma_sub_log.comp
    (tendsto_saddleCriticalGammaArgument_atTop hε)
  have hhalf : Tendsto
      (fun d : ℕ =>
        (saddleDigamma (saddleCriticalGammaArgument ε d) -
          Real.log (saddleCriticalGammaArgument ε d)) / 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using! hargument.div_const (2 : ℝ)
  have hcorrection : Tendsto
      (fun d : ℕ =>
        Real.exp
          ((saddleDigamma (saddleCriticalGammaArgument ε d) -
            Real.log (saddleCriticalGammaArgument ε d)) / 2))
      atTop (𝓝 (1 : ℝ)) := by
    simpa using! hhalf.rexp
  have htarget : Tendsto
      (fun d : ℕ =>
        Real.exp
          ((saddleDigamma (saddleCriticalGammaArgument ε d) -
            Real.log (saddleCriticalGammaArgument ε d)) / 2) *
          limitingSaddleRadius ε)
      atTop (𝓝 (limitingSaddleRadius ε)) := by
    simpa using! hcorrection.mul_const (limitingSaddleRadius ε)
  refine htarget.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  exact (saddleSourceRadius_div_sqrt_eq hε hd).symm
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
def saddleSourceMellinContour (ℓ u T : ℝ) : ℂ :=
  ((ℓ * (1 + u) : ℝ) : ℂ) -
    Complex.I * ((ℓ * T : ℝ) : ℂ)
def saddleSourceShellDerivative (ε u : ℝ) : ℝ :=
  (∫ a in shortCutoff ε..shortEndpoint ε,
    shortShellDensity ε a * a * Real.sinh (u * a)) +
  (∫ a in shellLocation ε..shellLocation ε + 1,
    positiveShellDensity ε a * a * Real.sinh (u * a))
def saddleSmallRadiusStarOrdinate (ε : ℝ) (d : ℕ) : ℝ :=
  let _sourceParameter : ℝ := ε
  show ℝ from
    -1 + Real.log ((d : ℝ) / 2) /
      (4 * ((d : ℝ) / 2))
def saddleSmallRadiusStar (ε : ℝ) (d : ℕ) : ℝ :=
  Real.exp
    (saddleLogRadius ε d
      (saddleSmallRadiusStarOrdinate ε d))
def saddleSmallResidueTruncation (ℓ : ℝ) : ℕ :=
  Nat.ceil (20 * Real.log ℓ)
def saddleSmallResidueTailMajorant (C ℓ : ℝ) : ℝ :=
  Real.exp (3 * C - (77 / 8 : ℝ) * Real.log ℓ)
def saddleSmallResidueCoefficientMajorant
    (K C ℓ : ℝ) : ℝ :=
  K *
    Real.exp
      (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) *
    (2 * (Real.log ℓ / 8 + C) +
      (Real.log ℓ / 8 + C) ^ 2) *
    Real.exp
      (2 * C - (3 / 4 : ℝ) * Real.log ℓ)
def saddleSmallResidueRelativeErrorMajorant
    (K C ℓ : ℝ) : ℝ :=
  saddleSmallResidueCoefficientMajorant K C ℓ +
    2 * saddleSmallResidueTailMajorant C ℓ
end
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
def saddleNegativeRelativeGammaTailMajorant
    (C K Kε ℓ : ℝ) : ℝ :=
  (2 * Kε / Real.Gamma (3 / 2 : ℝ)) *
    (1 + (Real.log ℓ / 8 + C)) *
      saddleSmallResidueTailMajorant C ℓ *
        Real.exp
          (K *
            (2 * (saddleSmallResidueTruncation ℓ : ℝ) + 1) ^ 2 /
              ℓ)
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
def upperCosLaplaceKernel (c T a : ℝ) : ℝ :=
  (1 - Real.cos (a * T)) * Real.exp (-c * a) / a
def upperGammaTruncatedDampingIntegrand
    (ℓ η T : ℝ) (n : ℕ) (a : ℝ) : ℝ :=
  upperCosLaplaceKernel η T a *
    ∑ k ∈ Finset.range (n + 1),
      Real.exp (-(2 * a / ℓ)) ^ k
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
def saddleNegativeContourOrdinate (ℓ : ℝ) (N : ℕ) : ℝ :=
  1 + (2 * (N : ℝ) + 1) / ℓ
def saddleNegativeGammaRate (ℓ : ℝ) (N : ℕ) : ℝ :=
  (2 * (N : ℝ) + 3) / ℓ
def saddleNegativeFrequencyMajorant (ε s : ℝ) : ℝ :=
  (1 + |s|) ^ 3 * Real.exp (-ε * Real.pi * |s|)
def saddleNegativeMellinMajorantCoefficient
    (ε ℓ : ℝ) (N : ℕ) : ℝ :=
  27 * (1 + |beta ε|) *
    Real.exp (2 * ε * Real.log 2) *
    (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
    Real.exp
      ((ℓ - saddleTaylorContour N) *
        Real.log Real.pi / 2) *
    Real.exp
      (ℓ * realHyperbolicShellPhase ε
        (saddleNegativeContourOrdinate ℓ N))
def saddleNegativeFrequencyMass (ε : ℝ) : ℝ :=
  ∫ s : ℝ, saddleNegativeFrequencyMajorant ε s
def saddleNegativeContourPhaseError
    (ε ℓ : ℝ) (N : ℕ) : ℝ :=
  ℓ *
      (realHyperbolicShellPhase ε
        (saddleNegativeContourOrdinate ℓ N) -
          realHyperbolicShellPhase ε 1) -
    (((2 * N + 1 : ℕ) : ℝ) *
      saddleShellDerivativeOne ε)
def saddleNegativeRelativeCoefficient (ε : ℝ) : ℝ :=
  27 * (1 + |beta ε|) *
    Real.exp (2 * ε * Real.log 2) *
      saddleNegativeFrequencyMass ε / (4 * beta ε)
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
theorem saddleRealCpow_hasDerivAt_zero
    {z : ℂ} (hz : 1 < z.re) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ z)
      (0 : ℂ) (0 : ℝ) := by
  have hz0 : z ≠ 0 := by
    intro heq
    subst z
    norm_num at hz
  have hsub : 0 < (z - 1).re := by
    simpa using! sub_pos.mpr hz
  have hsub0 : z - 1 ≠ 0 := by
    intro heq
    have := congrArg Complex.re heq
    simpa using! (ne_of_gt hsub) this
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have htend :
      Tendsto (fun t : ℝ => (t : ℂ) ^ (z - 1))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hcontinuous :=
      Complex.continuousAt_ofReal_cpow_const
        (0 : ℝ) (z - 1) (Or.inl hsub)
    simpa [Complex.zero_cpow hsub0] using!
      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  apply htend.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by
    simpa using! ht
  have htc : (t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ht0
  simp [hz0, Complex.real_smul, Complex.cpow_sub z 1 htc,
    div_eq_mul_inv, mul_comm]
theorem saddleRealCpow_hasDerivAt
    {z : ℂ} (hz : 1 < z.re) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ z)
      (z * (x : ℂ) ^ (z - 1)) x := by
  have hz0 : z ≠ 0 := by
    intro heq
    subst z
    norm_num at hz
  by_cases hx : x = 0
  · subst x
    have hsub : z - 1 ≠ 0 := by
      intro heq
      have hre := congrArg Complex.re heq
      norm_num at hre
      linarith
    simpa [Complex.zero_cpow hsub] using!
      saddleRealCpow_hasDerivAt_zero hz
  · exact hasDerivAt_ofReal_cpow_const hx hz0
def saddlePositiveCpow (z : ℂ) (x : ℝ) : ℂ :=
  ((max x 0 : ℝ) : ℂ) ^ z
theorem saddlePositiveCpow_continuous
    {z : ℂ} (hz : 0 < z.re) :
    Continuous (saddlePositiveCpow z) := by
  unfold saddlePositiveCpow
  exact (Complex.continuous_ofReal_cpow_const hz).comp
    (continuous_id.max continuous_const)
theorem saddlePositiveCpow_hasDerivAt_zero
    {z : ℂ} (hz : 1 < z.re) :
    HasDerivAt (saddlePositiveCpow z)
      (0 : ℂ) (0 : ℝ) := by
  have hz0 : z ≠ 0 := by
    intro heq
    subst z
    norm_num at hz
  have hsub : 0 < (z - 1).re := by
    change 0 < z.re - 1
    linarith
  have hsub0 : z - 1 ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    norm_num at hre
    linarith
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have htend :
      Tendsto (saddlePositiveCpow (z - 1))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hcontinuous :=
      (saddlePositiveCpow_continuous hsub).continuousAt
        (x := (0 : ℝ))
    simpa [saddlePositiveCpow,
      Complex.zero_cpow hsub0] using!
        hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  apply htend.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by
    simpa using! ht
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · have hmax : max t 0 = 0 := max_eq_right hneg.le
    simp [saddlePositiveCpow, hmax,
      Complex.zero_cpow hz0, Complex.zero_cpow hsub0]
  · have hmax : max t 0 = t := max_eq_left hpos.le
    have htc : (t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr ht0
    simp [saddlePositiveCpow, hmax, hz0,
      Complex.real_smul, Complex.cpow_sub z 1 htc,
      div_eq_mul_inv, mul_comm]
theorem saddlePositiveCpow_hasDerivAt
    {z : ℂ} (hz : 1 < z.re) (x : ℝ) :
    HasDerivAt (saddlePositiveCpow z)
      (z * saddlePositiveCpow (z - 1) x) x := by
  have hz0 : z ≠ 0 := by
    intro heq
    subst z
    norm_num at hz
  have hsub0 : z - 1 ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    norm_num at hre
    linarith
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have hevent :
        saddlePositiveCpow z =ᶠ[𝓝 x]
          (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds hneg] with y hy
      change y < 0 at hy
      simp [saddlePositiveCpow, max_eq_right hy.le,
        Complex.zero_cpow hz0]
    have hvalue : saddlePositiveCpow (z - 1) x = 0 := by
      simp [saddlePositiveCpow, max_eq_right hneg.le,
        Complex.zero_cpow hsub0]
    simpa [hvalue] using!
      (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq
        hevent
  · subst x
    simp [saddlePositiveCpow, Complex.zero_cpow hsub0,
      saddlePositiveCpow_hasDerivAt_zero hz]
  · have hevent :
        saddlePositiveCpow z =ᶠ[𝓝 x]
          (fun y : ℝ => (y : ℂ) ^ z) := by
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      change 0 < y at hy
      simp [saddlePositiveCpow, max_eq_left hy.le]
    have hvalue :
        saddlePositiveCpow (z - 1) x =
          (x : ℂ) ^ (z - 1) := by
      simp [saddlePositiveCpow, max_eq_left hpos.le]
    rw [hvalue]
    exact (saddleRealCpow_hasDerivAt hz x).congr_of_eventuallyEq
      hevent
def saddleContourExponent (a t : ℝ) : ℂ :=
  -(((a : ℂ) + (t : ℂ) * Complex.I) / 2)
@[simp] theorem saddleContourExponent_re (a t : ℝ) :
    (saddleContourExponent a t).re = -a / 2 := by
  simp [saddleContourExponent, Complex.mul_re]
  ring
def saddleContourExponentPolynomial (a : ℝ) : Polynomial ℂ :=
  Polynomial.C (-(a : ℂ) / 2) -
    Polynomial.C (Complex.I / 2) * Polynomial.X
theorem saddleContourExponentPolynomial_eval (a t : ℝ) :
    (saddleContourExponentPolynomial a).eval (t : ℂ) =
      saddleContourExponent a t := by
  simp [saddleContourExponentPolynomial,
    saddleContourExponent]
  ring
def saddleContourFallingPolynomial (a : ℝ) (j : ℕ) :
    Polynomial ℂ :=
  ∏ i ∈ Finset.range j,
    (saddleContourExponentPolynomial a -
      Polynomial.C (i : ℂ))
theorem saddleContourFallingPolynomial_eval_succ
    (a t : ℝ) (j : ℕ) :
    (saddleContourFallingPolynomial a (j + 1)).eval
        (t : ℂ) =
      (saddleContourFallingPolynomial a j).eval
          (t : ℂ) *
        (saddleContourExponent a t - (j : ℂ)) := by
  simp [saddleContourFallingPolynomial,
    Finset.prod_range_succ,
    saddleContourExponentPolynomial_eval]
theorem saddlePolynomialWeightedData_integrable
    {D : ℝ → ℂ}
    (hD : ∀ j : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ j * D t))
    (P : Polynomial ℂ) :
    Integrable (fun t : ℝ =>
      P.eval (t : ℂ) * D t) := by
  have hsum :
      Integrable (fun t : ℝ =>
        ∑ j ∈ Finset.range (P.natDegree + 1),
          P.coeff j * ((t : ℂ) ^ j * D t)) := by
    apply integrable_finsetSum
    intro j _
    exact (hD j).const_mul (P.coeff j)
  exact hsum.congr
    (Filter.Eventually.of_forall (fun t : ℝ => by
      change
        (∑ j ∈ Finset.range (P.natDegree + 1),
          P.coeff j * ((t : ℂ) ^ j * D t)) =
            P.eval (t : ℂ) * D t
      rw [Polynomial.eval_eq_sum_range]
      simp_rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring))
def saddlePositiveContourMoment
    (a : ℝ) (j : ℕ) (D : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ t : ℝ,
    saddlePositiveCpow
        (saddleContourExponent a t - (j : ℂ)) u *
      ((saddleContourFallingPolynomial a j).eval
        (t : ℂ) * D t)
@[simp] theorem saddleContourExponent_sub_nat_re
    (a t : ℝ) (j : ℕ) :
    (saddleContourExponent a t - (j : ℂ)).re =
      -a / 2 - (j : ℝ) := by
  simp [saddleContourExponent_re]
theorem saddlePositiveCpow_norm_le_one
    {z : ℂ} (hz : 0 < z.re)
    {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖saddlePositiveCpow z u‖ ≤ 1 := by
  have hbase : 0 ≤ max u 0 := le_max_right _ _
  have hbaseone : max u 0 ≤ 1 :=
    max_le hu.2.le (by norm_num)
  unfold saddlePositiveCpow
  rw [Complex.norm_cpow_eq_rpow_re_of_nonneg
    hbase (ne_of_gt hz)]
  exact Real.rpow_le_one hbase hbaseone hz.le
theorem saddlePositiveContourPower_frequency_continuous
    {a : ℝ} (j : ℕ)
    (ha : (j : ℝ) < -a / 2) (u : ℝ) :
    Continuous (fun t : ℝ =>
      saddlePositiveCpow
        (saddleContourExponent a t - (j : ℂ)) u) := by
  have hfrequency :
      Continuous (fun t : ℝ =>
        saddleContourExponent a t - (j : ℂ)) := by
    unfold saddleContourExponent
    fun_prop
  unfold saddlePositiveCpow
  apply hfrequency.const_cpow
  right
  intro t
  apply ne_of_apply_ne Complex.re
  have hpositive :
      0 < (saddleContourExponent a t - (j : ℂ)).re := by
    rw [saddleContourExponent_sub_nat_re]
    linarith
  simpa using! hpositive.ne'
theorem saddlePositiveContourMoment_hasDerivAt
    {D : ℝ → ℂ}
    (hD : ∀ k : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ k * D t))
    {a : ℝ} (j : ℕ)
    (ha : (j : ℝ) + 1 < -a / 2)
    {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (saddlePositiveContourMoment a j D)
      (saddlePositiveContourMoment a (j + 1) D u) u := by
  let W : ℕ → ℝ → ℂ :=
    fun k t =>
      (saddleContourFallingPolynomial a k).eval
          (t : ℂ) * D t
  have hW (k : ℕ) : Integrable (W k) := by
    try dsimp [W]
    exact saddlePolynomialWeightedData_integrable hD
      (saddleContourFallingPolynomial a k)
  have hjpos : (j : ℝ) < -a / 2 := by
    linarith
  have hsuccpos : ((j + 1 : ℕ) : ℝ) < -a / 2 := by
    push_cast
    linarith
  have hkernel (k : ℕ) (hk : (k : ℝ) < -a / 2)
      (v : ℝ) :
      AEStronglyMeasurable
        (fun t : ℝ =>
          saddlePositiveCpow
              (saddleContourExponent a t - (k : ℂ)) v *
            W k t) :=
    (saddlePositiveContourPower_frequency_continuous
      k hk v).aestronglyMeasurable.mul
        (hW k).aestronglyMeasurable
  have hpoint (v : ℝ)
      (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
      Integrable
        (fun t : ℝ =>
          saddlePositiveCpow
              (saddleContourExponent a t - (j : ℂ)) v *
            W j t) := by
    apply (hW j).norm.mono'
      (hkernel j hjpos v)
    filter_upwards [] with t
    rw [norm_mul]
    calc
      ‖saddlePositiveCpow
            (saddleContourExponent a t - (j : ℂ)) v‖ *
          ‖W j t‖ ≤ 1 * ‖W j t‖ := by
        gcongr
        apply saddlePositiveCpow_norm_le_one
        · rw [saddleContourExponent_sub_nat_re]
          linarith
        · exact hv
      _ = ‖W j t‖ := one_mul _
  have hdiff (t v : ℝ)
      (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
      HasDerivAt
        (fun x : ℝ =>
          saddlePositiveCpow
              (saddleContourExponent a t - (j : ℂ)) x *
            W j t)
        (saddlePositiveCpow
            (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) v *
          W (j + 1) t) v := by
    have hreal :
        1 < (saddleContourExponent a t - (j : ℂ)).re := by
      rw [saddleContourExponent_sub_nat_re]
      linarith
    have hderiv :=
      (saddlePositiveCpow_hasDerivAt hreal v).mul_const
        (W j t)
    have harg :
        saddleContourExponent a t - ((j + 1 : ℕ) : ℂ) =
          saddleContourExponent a t - (j : ℂ) - 1 := by
      push_cast
      ring
    have hfall :
        W (j + 1) t =
          W j t * (saddleContourExponent a t - (j : ℂ)) := by
      try dsimp [W]
      rw [saddleContourFallingPolynomial_eval_succ]
      ring
    rw [harg, hfall]
    convert! hderiv using 1
    all_goals ring
  have hresult :=
    _root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume)
      (F := fun (v : ℝ) (t : ℝ) =>
        saddlePositiveCpow
            (saddleContourExponent a t - (j : ℂ)) v *
          W j t)
      (F' := fun (v : ℝ) (t : ℝ) =>
        saddlePositiveCpow
            (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) v *
          W (j + 1) t)
      (bound := fun t : ℝ => ‖W (j + 1) t‖)
      (isOpen_Ioo.mem_nhds hu)
      (Filter.Eventually.of_forall
        (fun v => hkernel j hjpos v))
      (hpoint u hu)
      (hkernel (j + 1) hsuccpos u)
      (Filter.Eventually.of_forall (fun t => by
        intro v hv
        rw [norm_mul]
        calc
          ‖saddlePositiveCpow
                (saddleContourExponent a t -
                  ((j + 1 : ℕ) : ℂ)) v‖ *
              ‖W (j + 1) t‖ ≤
            1 * ‖W (j + 1) t‖ := by
              gcongr
              apply saddlePositiveCpow_norm_le_one
              · rw [saddleContourExponent_sub_nat_re]
                exact sub_pos.mpr hsuccpos
              · exact hv
          _ = ‖W (j + 1) t‖ := one_mul _))
      ((hW (j + 1)).norm)
      (Filter.Eventually.of_forall (fun t => by
        intro v hv
        exact hdiff t v hv))
  change
    HasDerivAt
      (fun v : ℝ =>
        ∫ t : ℝ,
          saddlePositiveCpow
              (saddleContourExponent a t - (j : ℂ)) v *
            W j t)
      (∫ t : ℝ,
        saddlePositiveCpow
            (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) u *
          W (j + 1) t) u
  exact hresult.2
theorem saddlePositiveContourMoment_contDiffOn
    {D : ℝ → ℂ}
    (hD : ∀ k : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ k * D t))
    {a : ℝ} (n j : ℕ)
    (ha : (n : ℝ) + (j : ℝ) + 1 < -a / 2) :
    ContDiffOn ℝ n
      (saddlePositiveContourMoment a j D)
      (Set.Ioo (-1 : ℝ) 1) := by
  induction n generalizing j with
  | zero =>
      change ContDiffOn ℝ 0
        (saddlePositiveContourMoment a j D)
        (Set.Ioo (-1 : ℝ) 1)
      rw [contDiffOn_zero]
      intro u hu
      have hj : (j : ℝ) + 1 < -a / 2 := by
        simpa using! ha
      exact
        (saddlePositiveContourMoment_hasDerivAt
          hD j hj hu).continuousAt.continuousWithinAt
  | succ n ih =>
      have hj : (j : ℝ) + 1 < -a / 2 := by
        push_cast at ha
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hnext :
          (n : ℝ) + ((j + 1 : ℕ) : ℝ) + 1 < -a / 2 := by
        push_cast at ha ⊢
        linarith
      rw [show (↑(n + 1) : WithTop ℕ∞) =
          (↑n : WithTop ℕ∞) + 1 by simp,
        contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      refine ⟨?_, ?_, ?_⟩
      · intro u hu
        exact
          (saddlePositiveContourMoment_hasDerivAt
            hD j hj hu).differentiableAt.differentiableWithinAt
      · simp
      · exact (ih (j + 1) hnext).congr
          (fun u hu =>
            (saddlePositiveContourMoment_hasDerivAt
              hD j hj hu).deriv)
theorem saddleMellinInversePower_eq_squaredPositiveCpow
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    saddleMellinInversePower r z =
      saddlePositiveCpow (-z / 2) (r ^ 2) := by
  unfold saddleMellinInversePower
  calc
    (r : ℂ) ^ (-z) =
      (r : ℂ) ^ (((2 : ℝ) : ℂ) * (-z / 2)) := by
        congr 1
        push_cast
        ring
    _ = (((r ^ (2 : ℝ) : ℝ) : ℂ)) ^ (-z / 2) :=
      Complex.cpow_mul_ofReal_nonneg hr.le 2 (-z / 2)
    _ = saddlePositiveCpow (-z / 2) (r ^ 2) := by
      simp [saddlePositiveCpow,
        max_eq_left (sq_nonneg r)]
@[simp] theorem saddlePositiveContourMoment_zero
    {a : ℝ} (j : ℕ)
    (ha : (j : ℝ) < -a / 2) (D : ℝ → ℂ) :
    saddlePositiveContourMoment a j D 0 = 0 := by
  unfold saddlePositiveContourMoment
  have hzero :
      (fun t : ℝ =>
        saddlePositiveCpow
            (saddleContourExponent a t - (j : ℂ)) 0 *
          ((saddleContourFallingPolynomial a j).eval
              (t : ℂ) * D t)) =
        fun _ : ℝ => (0 : ℂ) := by
    funext t
    have hexp :
        saddleContourExponent a t - (j : ℂ) ≠ 0 := by
      apply ne_of_apply_ne Complex.re
      have hpositive :
          0 < (saddleContourExponent a t - (j : ℂ)).re := by
        rw [saddleContourExponent_sub_nat_re]
        linarith
      simpa using! hpositive.ne'
    simp [saddlePositiveCpow, Complex.zero_cpow hexp]
  rw [hzero, integral_zero]
def plusSaddleSquaredRemainder
    (ε ℓ : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    saddlePositiveContourMoment (saddleTaylorContour N) 0
      (fun t : ℝ =>
        plusSaddleMellinData ε ℓ
          ((saddleTaylorContour N : ℂ) +
            (t : ℂ) * Complex.I)) u
def minusSaddleSquaredRemainder
    (ε ℓ : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    saddlePositiveContourMoment (saddleTaylorContour N) 0
      (fun t : ℝ =>
        minusSaddleMellinData ε ℓ
          ((saddleTaylorContour N : ℂ) +
            (t : ℂ) * Complex.I)) u
theorem plusSaddleTaylorRemainder_eq_squared
    (ε ℓ : ℝ) (N : ℕ)
    {r : ℝ} (hr : 0 < r) :
    plusSaddleTaylorRemainder ε ℓ N r =
      plusSaddleSquaredRemainder ε ℓ N (r ^ 2) := by
  unfold plusSaddleTaylorRemainder
    plusSaddleSquaredRemainder
    saddlePositiveContourMoment
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [saddleMellinInversePower_eq_squaredPositiveCpow
    hr ((saddleTaylorContour N : ℂ) +
      (t : ℂ) * Complex.I)]
  have hq :
      -((saddleTaylorContour N : ℂ) +
          (t : ℂ) * Complex.I) / 2 =
        saddleContourExponent (saddleTaylorContour N) t := by
    unfold saddleContourExponent
    ring
  rw [hq]
  simp [saddleContourFallingPolynomial]
theorem minusSaddleTaylorRemainder_eq_squared
    (ε ℓ : ℝ) (N : ℕ)
    {r : ℝ} (hr : 0 < r) :
    minusSaddleTaylorRemainder ε ℓ N r =
      minusSaddleSquaredRemainder ε ℓ N (r ^ 2) := by
  unfold minusSaddleTaylorRemainder
    minusSaddleSquaredRemainder
    saddlePositiveContourMoment
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [saddleMellinInversePower_eq_squaredPositiveCpow
    hr ((saddleTaylorContour N : ℂ) +
      (t : ℂ) * Complex.I)]
  have hq :
      -((saddleTaylorContour N : ℂ) +
          (t : ℂ) * Complex.I) / 2 =
        saddleContourExponent (saddleTaylorContour N) t := by
    unfold saddleContourExponent
    ring
  rw [hq]
  simp [saddleContourFallingPolynomial]
theorem plusSaddleSquaredRemainder_contDiffOn
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (n N : ℕ)
    (hshift : (n : ℝ) + 1 <
      -(saddleTaylorContour N) / 2) :
    ContDiffOn ℝ n
      (plusSaddleSquaredRemainder ε ℓ N)
      (Set.Ioo (-1 : ℝ) 1) := by
  have hmoment :
      ∀ k : ℕ,
        Integrable (fun t : ℝ =>
          (t : ℂ) ^ k *
            plusSaddleMellinData ε ℓ
              ((saddleTaylorContour N : ℂ) +
                (t : ℂ) * Complex.I)) := by
    intro k
    exact plusSaddleMellinData_shiftedLine_moment_integrable
      hε hℓ horder
      (fun j : ℕ => saddleTaylorContour_ne_pole N j) k
  have hsmooth :=
    saddlePositiveContourMoment_contDiffOn hmoment
      n 0 (by simpa using! hshift)
  exact (contDiff_const.contDiffOn.mul hsmooth)
theorem minusSaddleSquaredRemainder_contDiffOn
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (n N : ℕ)
    (hshift : (n : ℝ) + 1 <
      -(saddleTaylorContour N) / 2) :
    ContDiffOn ℝ n
      (minusSaddleSquaredRemainder ε ℓ N)
      (Set.Ioo (-1 : ℝ) 1) := by
  have hmoment :
      ∀ k : ℕ,
        Integrable (fun t : ℝ =>
          (t : ℂ) ^ k *
            minusSaddleMellinData ε ℓ
              ((saddleTaylorContour N : ℂ) +
                (t : ℂ) * Complex.I)) := by
    intro k
    exact minusSaddleMellinData_shiftedLine_moment_integrable
      hε hℓ horder
      (fun j : ℕ => saddleTaylorContour_ne_pole N j) k
  have hsmooth :=
    saddlePositiveContourMoment_contDiffOn hmoment
      n 0 (by simpa using! hshift)
  exact (contDiff_const.contDiffOn.mul hsmooth)
def saddleSquaredResiduePolynomial
    (c : ℕ → ℂ) (N : ℕ) (u : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1),
    c j * ((u : ℂ) ^ j)
theorem saddleTaylorContour_negativeHalf_pos (N : ℕ) :
    0 < -(saddleTaylorContour N) / 2 := by
  simp only [saddleTaylorContour, neg_neg]
  positivity
@[simp] theorem saddleSquaredResiduePolynomial_zero
    (c : ℕ → ℂ) (N : ℕ) :
    saddleSquaredResiduePolynomial c N 0 = c 0 := by
  classical
  unfold saddleSquaredResiduePolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [zero_pow hj]
  · simp
theorem saddleSquaredResiduePolynomial_contDiff
    (c : ℕ → ℂ) (N n : ℕ) :
    ContDiff ℝ n (saddleSquaredResiduePolynomial c N) := by
  unfold saddleSquaredResiduePolynomial
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul
    (Complex.ofRealCLM.contDiff.pow j)
@[simp] theorem plusSaddleSquaredRemainder_zero
    (ε ℓ : ℝ) (N : ℕ) :
    plusSaddleSquaredRemainder ε ℓ N 0 = 0 := by
  unfold plusSaddleSquaredRemainder
  rw [saddlePositiveContourMoment_zero 0
    (by simpa using! saddleTaylorContour_negativeHalf_pos N)]
  simp
@[simp] theorem minusSaddleSquaredRemainder_zero
    (ε ℓ : ℝ) (N : ℕ) :
    minusSaddleSquaredRemainder ε ℓ N 0 = 0 := by
  unfold minusSaddleSquaredRemainder
  rw [saddlePositiveContourMoment_zero 0
    (by simpa using! saddleTaylorContour_negativeHalf_pos N)]
  simp
theorem plusSaddleProfile_eq_squaredTaylor
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    plusSaddleProfile ε ℓ r =
      saddleSquaredResiduePolynomial
        (plusSaddlePoleResidue ε ℓ) N (r ^ 2) +
      plusSaddleSquaredRemainder ε ℓ N (r ^ 2) := by
  rcases hr.eq_or_lt with hzero | hpositive
  · subst r
    simp [plusSaddleProfile,
      plusSaddlePoleResidue_zero hℓ]
  · rw [plusSaddleProfile_eq_residue_sum_add_remainder
      hε hℓ horder hpositive N,
      plusSaddleTaylorRemainder_eq_squared
        ε ℓ N hpositive]
    congr 1
    unfold saddleSquaredResiduePolynomial
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    rw [← pow_mul]
theorem minusSaddleProfile_eq_squaredTaylor
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    minusSaddleProfile ε ℓ r =
      saddleSquaredResiduePolynomial
        (minusSaddlePoleResidue ε ℓ) N (r ^ 2) +
      minusSaddleSquaredRemainder ε ℓ N (r ^ 2) := by
  rcases hr.eq_or_lt with hzero | hpositive
  · subst r
    simp [minusSaddleProfile,
      minusSaddlePoleResidue_zero hℓ]
  · rw [minusSaddleProfile_eq_residue_sum_add_remainder
      hε hℓ horder hpositive N,
      minusSaddleTaylorRemainder_eq_squared
        ε ℓ N hpositive]
    congr 1
    unfold saddleSquaredResiduePolynomial
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    rw [← pow_mul]
theorem saddleTaylorContour_smoothShift (n : ℕ) :
    (n : ℝ) + 1 <
      -(saddleTaylorContour (n + 2)) / 2 := by
  simp only [saddleTaylorContour, neg_neg]
  push_cast
  linarith
theorem plusSaddleFunction_contDiff_nat
    {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (n : ℕ) :
    ContDiff ℝ n (plusSaddleFunction ε d) := by
  have hdimension : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast hd) (by norm_num)
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    let N : ℕ := n + 2
    have hshift :
        (n : ℝ) + 1 <
          -(saddleTaylorContour N) / 2 := by
      exact saddleTaylorContour_smoothShift n
    have hremScalar :
        ContDiffAt ℝ n
          (plusSaddleSquaredRemainder
            ε ((d : ℝ) / 2) N)
          (‖(0 : Euclidean d)‖ ^ 2) := by
      simpa using!
        (plusSaddleSquaredRemainder_contDiffOn
          hε hdimension horder n N hshift).contDiffAt
            (isOpen_Ioo.mem_nhds
              (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by
                constructor <;> norm_num))
    have hrem :
        ContDiffAt ℝ n
          (fun y : Euclidean d =>
            plusSaddleSquaredRemainder
              ε ((d : ℝ) / 2) N (‖y‖ ^ 2))
          (0 : Euclidean d) :=
      hremScalar.fun_comp
        (f := fun y : Euclidean d => ‖y‖ ^ 2)
        (0 : Euclidean d)
        (contDiff_norm_sq ℝ).contDiffAt
    have hpoly :
        ContDiffAt ℝ n
          (fun y : Euclidean d =>
            saddleSquaredResiduePolynomial
              (plusSaddlePoleResidue
                ε ((d : ℝ) / 2)) N (‖y‖ ^ 2))
          (0 : Euclidean d) :=
      (saddleSquaredResiduePolynomial_contDiff
        (plusSaddlePoleResidue ε ((d : ℝ) / 2))
          N n).contDiffAt.fun_comp
            (f := fun y : Euclidean d => ‖y‖ ^ 2)
            (0 : Euclidean d)
            (contDiff_norm_sq ℝ).contDiffAt
    refine (hpoly.add hrem).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y : Euclidean d => ?_))
    exact plusSaddleProfile_eq_squaredTaylor
      hε hdimension horder N (norm_nonneg y)
  · exact
      ((plusSaddleFunction_contDiffOn hε hd horder).contDiffAt
          ((isOpen_compl_singleton
            (x := (0 : Euclidean d))).mem_nhds
              (by simpa using! hx))).of_le
                (mod_cast le_top)
theorem minusSaddleFunction_contDiff_nat
    {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (n : ℕ) :
    ContDiff ℝ n (minusSaddleFunction ε d) := by
  have hdimension : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast hd) (by norm_num)
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    let N : ℕ := n + 2
    have hshift :
        (n : ℝ) + 1 <
          -(saddleTaylorContour N) / 2 := by
      exact saddleTaylorContour_smoothShift n
    have hremScalar :
        ContDiffAt ℝ n
          (minusSaddleSquaredRemainder
            ε ((d : ℝ) / 2) N)
          (‖(0 : Euclidean d)‖ ^ 2) := by
      simpa using!
        (minusSaddleSquaredRemainder_contDiffOn
          hε hdimension horder n N hshift).contDiffAt
            (isOpen_Ioo.mem_nhds
              (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by
                constructor <;> norm_num))
    have hrem :
        ContDiffAt ℝ n
          (fun y : Euclidean d =>
            minusSaddleSquaredRemainder
              ε ((d : ℝ) / 2) N (‖y‖ ^ 2))
          (0 : Euclidean d) :=
      hremScalar.fun_comp
        (f := fun y : Euclidean d => ‖y‖ ^ 2)
        (0 : Euclidean d)
        (contDiff_norm_sq ℝ).contDiffAt
    have hpoly :
        ContDiffAt ℝ n
          (fun y : Euclidean d =>
            saddleSquaredResiduePolynomial
              (minusSaddlePoleResidue
                ε ((d : ℝ) / 2)) N (‖y‖ ^ 2))
          (0 : Euclidean d) :=
      (saddleSquaredResiduePolynomial_contDiff
        (minusSaddlePoleResidue ε ((d : ℝ) / 2))
          N n).contDiffAt.fun_comp
            (f := fun y : Euclidean d => ‖y‖ ^ 2)
            (0 : Euclidean d)
            (contDiff_norm_sq ℝ).contDiffAt
    refine (hpoly.add hrem).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y : Euclidean d => ?_))
    exact minusSaddleProfile_eq_squaredTaylor
      hε hdimension horder N (norm_nonneg y)
  · exact
      ((minusSaddleFunction_contDiffOn hε hd horder).contDiffAt
          ((isOpen_compl_singleton
            (x := (0 : Euclidean d))).mem_nhds
              (by simpa using! hx))).of_le
                (mod_cast le_top)
theorem plusSaddleFunction_contDiff
    {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ContDiff ℝ ∞ (plusSaddleFunction ε d) := by
  exact contDiff_infty.mpr
    (fun n => plusSaddleFunction_contDiff_nat
      hε hd horder n)
theorem minusSaddleFunction_contDiff
    {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ContDiff ℝ ∞ (minusSaddleFunction ε d) := by
  exact contDiff_infty.mpr
    (fun n => minusSaddleFunction_contDiff_nat
      hε hd horder n)
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology
theorem saddleRightHalfPlane_boundary_rectangle
    {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.re})
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (T : ℝ) :
    (∫ a in A..B,
      F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
    (∫ a in A..B,
      F ((a : ℂ) + (T : ℂ) * Complex.I)) +
    Complex.I *
      (∫ t in -T..T,
        F ((B : ℂ) + (t : ℂ) * Complex.I)) -
    Complex.I *
      (∫ t in -T..T,
        F ((A : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
  let z : ℂ :=
    (A : ℂ) + ((-T : ℝ) : ℂ) * Complex.I
  let w : ℂ :=
    (B : ℂ) + (T : ℂ) * Complex.I
  have hrect :
      DifferentiableOn ℂ F
        (Complex.reProdIm
          [[z.re, w.re]] [[z.im, w.im]]) := by
    apply hF.mono
    intro u hu
    have hre : u.re ∈ [[z.re, w.re]] :=
      (Complex.mem_reProdIm.mp hu).1
    rcases Set.mem_uIcc.mp hre with hleft | hright
    · have hza : z.re = A := by
        simp [z, Complex.mul_re]
      rw [hza] at hleft
      exact hA.trans_le hleft.1
    · have hwb : w.re = B := by
        simp [w, Complex.mul_re]
      rw [hwb] at hright
      exact hB.trans_le hright.1
  have h :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      F z w hrect
  simpa [z, w, Complex.mul_re, Complex.mul_im,
    smul_eq_mul] using! h
theorem plusSaddleMellinData_positive_vertical_integral_eq
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r)
    (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B) :
    (∫ t : ℝ,
      saddleMellinInversePower r
          ((B : ℂ) + (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      saddleMellinInversePower r
          ((A : ℂ) + (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((A : ℂ) + (t : ℂ) * Complex.I)) := by
  let F : ℂ → ℂ := fun z =>
    saddleMellinInversePower r z *
      plusSaddleMellinData ε ℓ z
  have hhol :
      DifferentiableOn ℂ F {z : ℂ | 0 < z.re} :=
    (saddleMellinInversePower_differentiable
      hr).differentiableOn.mul
        (plusSaddleMellinData_differentiableOn_rightHalfPlane
          hε horder ℓ)
  have hleft :
      Integrable (fun t : ℝ =>
        F ((A : ℂ) + (t : ℂ) * Complex.I)) :=
    plusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder
      (fun n => saddlePositiveContour_ne_pole hA n) hr
  have hright :
      Integrable (fun t : ℝ =>
        F ((B : ℂ) + (t : ℂ) * Complex.I)) :=
    plusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder
      (fun n => saddlePositiveContour_ne_pole hB n) hr
  have hlower :
      Tendsto
        (fun T : ℝ =>
          ∫ a in A..B,
            F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        Filter.atTop (𝓝 0) := by
    simpa [F] using!
      plusSaddleMellinData_weighted_horizontalIntegral_tendsto_zero
        hε hℓ horder hr hAB (-1) (by norm_num)
  have hupper :
      Tendsto
        (fun T : ℝ =>
          ∫ a in A..B,
            F ((a : ℂ) + (T : ℂ) * Complex.I))
        Filter.atTop (𝓝 0) := by
    simpa [F] using!
      plusSaddleMellinData_weighted_horizontalIntegral_tendsto_zero
        hε hℓ horder hr hAB 1 (by norm_num)
  exact saddleInfiniteRectangle_vertical_integral_eq
    hleft hright hlower hupper
    (fun T => saddleRightHalfPlane_boundary_rectangle
      hhol hA hB T)
theorem minusSaddleMellinData_positive_vertical_integral_eq
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r)
    (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B) :
    (∫ t : ℝ,
      saddleMellinInversePower r
          ((B : ℂ) + (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      saddleMellinInversePower r
          ((A : ℂ) + (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((A : ℂ) + (t : ℂ) * Complex.I)) := by
  let F : ℂ → ℂ := fun z =>
    saddleMellinInversePower r z *
      minusSaddleMellinData ε ℓ z
  have hhol :
      DifferentiableOn ℂ F {z : ℂ | 0 < z.re} :=
    (saddleMellinInversePower_differentiable
      hr).differentiableOn.mul
        (minusSaddleMellinData_differentiableOn_rightHalfPlane
          hε horder ℓ)
  have hleft :
      Integrable (fun t : ℝ =>
        F ((A : ℂ) + (t : ℂ) * Complex.I)) :=
    minusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder
      (fun n => saddlePositiveContour_ne_pole hA n) hr
  have hright :
      Integrable (fun t : ℝ =>
        F ((B : ℂ) + (t : ℂ) * Complex.I)) :=
    minusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder
      (fun n => saddlePositiveContour_ne_pole hB n) hr
  have hlower :
      Tendsto
        (fun T : ℝ =>
          ∫ a in A..B,
            F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        Filter.atTop (𝓝 0) := by
    simpa [F] using!
      minusSaddleMellinData_weighted_horizontalIntegral_tendsto_zero
        hε hℓ horder hr hAB (-1) (by norm_num)
  have hupper :
      Tendsto
        (fun T : ℝ =>
          ∫ a in A..B,
            F ((a : ℂ) + (T : ℂ) * Complex.I))
        Filter.atTop (𝓝 0) := by
    simpa [F] using!
      minusSaddleMellinData_weighted_horizontalIntegral_tendsto_zero
        hε hℓ horder hr hAB 1 (by norm_num)
  exact saddleInfiniteRectangle_vertical_integral_eq
    hleft hright hlower hupper
    (fun T => saddleRightHalfPlane_boundary_rectangle
      hhol hA hB T)
theorem plusSaddleProfile_eq_positive_contour
    {ε ℓ r a : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (ha : 0 < a) :
    plusSaddleProfile ε ℓ r =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
            plusSaddleMellinData ε ℓ
              ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [plusSaddleProfile_eq_normalized_vertical_integral hr]
  congr 1
  rcases le_total ℓ a with hleft | hright
  · exact
      (plusSaddleMellinData_positive_vertical_integral_eq
        hε hℓ horder hr hℓ ha hleft).symm
  · exact
      plusSaddleMellinData_positive_vertical_integral_eq
        hε hℓ horder hr ha hℓ hright
theorem minusSaddleProfile_eq_positive_contour
    {ε ℓ r a : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (ha : 0 < a) :
    minusSaddleProfile ε ℓ r =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
            minusSaddleMellinData ε ℓ
              ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [minusSaddleProfile_eq_normalized_vertical_integral hr]
  congr 1
  rcases le_total ℓ a with hleft | hright
  · exact
      (minusSaddleMellinData_positive_vertical_integral_eq
        hε hℓ horder hr hℓ ha hleft).symm
  · exact
      minusSaddleMellinData_positive_vertical_integral_eq
        hε hℓ horder hr ha hℓ hright
def plusSaddlePositiveSquaredContour
    (ε ℓ a u : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    saddlePositiveContourMoment a 0
      (fun t : ℝ =>
        plusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I)) u
def minusSaddlePositiveSquaredContour
    (ε ℓ a u : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    saddlePositiveContourMoment a 0
      (fun t : ℝ =>
        minusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I)) u
theorem plusSaddleProfile_eq_positive_squaredContour
    {ε ℓ r a : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (ha : 0 < a) :
    plusSaddleProfile ε ℓ r =
      plusSaddlePositiveSquaredContour ε ℓ a (r ^ 2) := by
  rw [plusSaddleProfile_eq_positive_contour
    hε hℓ horder hr ha]
  unfold plusSaddlePositiveSquaredContour
    saddlePositiveContourMoment
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [saddleMellinInversePower_eq_squaredPositiveCpow
    hr ((a : ℂ) + (t : ℂ) * Complex.I)]
  have hq :
      -((a : ℂ) + (t : ℂ) * Complex.I) / 2 =
        saddleContourExponent a t := by
    unfold saddleContourExponent
    ring
  rw [hq]
  simp [saddleContourFallingPolynomial]
theorem minusSaddleProfile_eq_positive_squaredContour
    {ε ℓ r a : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (ha : 0 < a) :
    minusSaddleProfile ε ℓ r =
      minusSaddlePositiveSquaredContour ε ℓ a (r ^ 2) := by
  rw [minusSaddleProfile_eq_positive_contour
    hε hℓ horder hr ha]
  unfold minusSaddlePositiveSquaredContour
    saddlePositiveContourMoment
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [saddleMellinInversePower_eq_squaredPositiveCpow
    hr ((a : ℂ) + (t : ℂ) * Complex.I)]
  have hq :
      -((a : ℂ) + (t : ℂ) * Complex.I) / 2 =
        saddleContourExponent a t := by
    unfold saddleContourExponent
    ring
  rw [hq]
  simp [saddleContourFallingPolynomial]
theorem saddlePositiveCpow_hasDerivAt_of_pos
    {z : ℂ} (hz : z ≠ 0)
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (saddlePositiveCpow z)
      (z * saddlePositiveCpow (z - 1) u) u := by
  have hevent :
      saddlePositiveCpow z =ᶠ[𝓝 u]
        (fun v : ℝ => (v : ℂ) ^ z) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    change 0 < v at hv
    simp [saddlePositiveCpow, max_eq_left hv.le]
  have hvalue :
      saddlePositiveCpow (z - 1) u =
        (u : ℂ) ^ (z - 1) := by
    simp [saddlePositiveCpow, max_eq_left hu.le]
  rw [hvalue]
  exact
    (hasDerivAt_ofReal_cpow_const hu.ne' hz).congr_of_eventuallyEq
      hevent
theorem saddlePositiveContourPower_frequency_continuous_of_pos
    (a : ℝ) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    Continuous (fun t : ℝ =>
      saddlePositiveCpow
        (saddleContourExponent a t - (j : ℂ)) u) := by
  have hfrequency :
      Continuous (fun t : ℝ =>
        saddleContourExponent a t - (j : ℂ)) := by
    unfold saddleContourExponent
    fun_prop
  unfold saddlePositiveCpow
  apply hfrequency.const_cpow
  left
  rw [max_eq_left hu.le]
  exact Complex.ofReal_ne_zero.mpr hu.ne'
theorem saddlePositiveCpow_norm_le_one_of_nonpos
    {z : ℂ} (hz : z.re ≤ 0)
    {u : ℝ} (hu : u ∈ Set.Ioi (1 : ℝ)) :
    ‖saddlePositiveCpow z u‖ ≤ 1 := by
  have hupos : 0 < u := lt_trans zero_lt_one hu
  unfold saddlePositiveCpow
  rw [max_eq_left hupos.le,
    Complex.norm_cpow_eq_rpow_re_of_pos hupos]
  exact Real.rpow_le_one_of_one_le_of_nonpos hu.le hz
theorem saddlePositiveContourMoment_hasDerivAt_of_positiveContour
    {D : ℝ → ℂ}
    (hD : ∀ k : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ k * D t))
    {a : ℝ} (ha : 0 < a) (j : ℕ)
    {u : ℝ} (hu : u ∈ Set.Ioi (1 : ℝ)) :
    HasDerivAt (saddlePositiveContourMoment a j D)
      (saddlePositiveContourMoment a (j + 1) D u) u := by
  let W : ℕ → ℝ → ℂ :=
    fun k t =>
      (saddleContourFallingPolynomial a k).eval
          (t : ℂ) * D t
  have hW (k : ℕ) : Integrable (W k) := by
    try dsimp [W]
    exact saddlePolynomialWeightedData_integrable hD
      (saddleContourFallingPolynomial a k)
  have hupos : 0 < u := lt_trans zero_lt_one hu
  have hkernel (k : ℕ) (v : ℝ) (hv : 0 < v) :
      AEStronglyMeasurable
        (fun t : ℝ =>
          saddlePositiveCpow
              (saddleContourExponent a t - (k : ℂ)) v *
            W k t) :=
    (saddlePositiveContourPower_frequency_continuous_of_pos
      a k hv).aestronglyMeasurable.mul
        (hW k).aestronglyMeasurable
  have hpower (k : ℕ) (t : ℝ) :
      (saddleContourExponent a t - (k : ℂ)).re ≤ 0 := by
    rw [saddleContourExponent_sub_nat_re]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hpoint (v : ℝ)
      (hv : v ∈ Set.Ioi (1 : ℝ)) :
      Integrable
        (fun t : ℝ =>
          saddlePositiveCpow
              (saddleContourExponent a t - (j : ℂ)) v *
            W j t) := by
    apply (hW j).norm.mono'
      (hkernel j v (lt_trans zero_lt_one hv))
    filter_upwards [] with t
    rw [norm_mul]
    calc
      ‖saddlePositiveCpow
            (saddleContourExponent a t - (j : ℂ)) v‖ *
          ‖W j t‖ ≤ 1 * ‖W j t‖ := by
        gcongr
        exact saddlePositiveCpow_norm_le_one_of_nonpos
          (hpower j t) hv
      _ = ‖W j t‖ := one_mul _
  have hdiff (t v : ℝ)
      (hv : v ∈ Set.Ioi (1 : ℝ)) :
      HasDerivAt
        (fun x : ℝ =>
          saddlePositiveCpow
              (saddleContourExponent a t - (j : ℂ)) x *
            W j t)
        (saddlePositiveCpow
            (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) v *
          W (j + 1) t) v := by
    have hnonzero :
        saddleContourExponent a t - (j : ℂ) ≠ 0 := by
      apply ne_of_apply_ne Complex.re
      rw [saddleContourExponent_sub_nat_re]
      have hk : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hneg : -a / 2 - (j : ℝ) < 0 := by
        linarith
      simpa using! hneg.ne
    have hderiv :=
      (saddlePositiveCpow_hasDerivAt_of_pos
        hnonzero (lt_trans zero_lt_one hv)).mul_const
          (W j t)
    have harg :
        saddleContourExponent a t - ((j + 1 : ℕ) : ℂ) =
          saddleContourExponent a t - (j : ℂ) - 1 := by
      push_cast
      ring
    have hfall :
        W (j + 1) t =
          W j t * (saddleContourExponent a t - (j : ℂ)) := by
      try dsimp [W]
      rw [saddleContourFallingPolynomial_eval_succ]
      ring
    rw [harg, hfall]
    convert! hderiv using 1
    all_goals ring
  have hmeas :
      ∀ᶠ v in 𝓝 u,
        AEStronglyMeasurable
          (fun t : ℝ =>
            saddlePositiveCpow
                (saddleContourExponent a t - (j : ℂ)) v *
              W j t) := by
    filter_upwards [Ioi_mem_nhds hupos] with v hv
    exact hkernel j v hv
  have hresult :=
    _root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume)
      (F := fun (v : ℝ) (t : ℝ) =>
        saddlePositiveCpow
            (saddleContourExponent a t - (j : ℂ)) v *
          W j t)
      (F' := fun (v : ℝ) (t : ℝ) =>
        saddlePositiveCpow
            (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) v *
          W (j + 1) t)
      (bound := fun t : ℝ => ‖W (j + 1) t‖)
      (isOpen_Ioi.mem_nhds hu)
      hmeas
      (hpoint u hu)
      (hkernel (j + 1) u hupos)
      (Filter.Eventually.of_forall (fun t => by
        intro v hv
        rw [norm_mul]
        calc
          ‖saddlePositiveCpow
                (saddleContourExponent a t -
                  ((j + 1 : ℕ) : ℂ)) v‖ *
              ‖W (j + 1) t‖ ≤
            1 * ‖W (j + 1) t‖ := by
              gcongr
              exact saddlePositiveCpow_norm_le_one_of_nonpos
                (hpower (j + 1) t) hv
          _ = ‖W (j + 1) t‖ := one_mul _))
      ((hW (j + 1)).norm)
      (Filter.Eventually.of_forall (fun t => by
        intro v hv
        exact hdiff t v hv))
  change
    HasDerivAt
      (fun v : ℝ =>
        ∫ t : ℝ,
          saddlePositiveCpow
              (saddleContourExponent a t - (j : ℂ)) v *
            W j t)
      (∫ t : ℝ,
        saddlePositiveCpow
            (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) u *
          W (j + 1) t) u
  exact hresult.2
theorem saddlePositiveContourMoment_contDiffOn_of_positiveContour
    {D : ℝ → ℂ}
    (hD : ∀ k : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ k * D t))
    {a : ℝ} (ha : 0 < a) (n j : ℕ) :
    ContDiffOn ℝ n
      (saddlePositiveContourMoment a j D)
      (Set.Ioi (1 : ℝ)) := by
  induction n generalizing j with
  | zero =>
      change ContDiffOn ℝ 0
        (saddlePositiveContourMoment a j D)
        (Set.Ioi (1 : ℝ))
      rw [contDiffOn_zero]
      intro u hu
      exact
        (saddlePositiveContourMoment_hasDerivAt_of_positiveContour
          hD ha j hu).continuousAt.continuousWithinAt
  | succ n ih =>
      rw [show (↑(n + 1) : WithTop ℕ∞) =
          (↑n : WithTop ℕ∞) + 1 by simp,
        contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨?_, ?_, ?_⟩
      · intro u hu
        exact
          (saddlePositiveContourMoment_hasDerivAt_of_positiveContour
            hD ha j hu).differentiableAt.differentiableWithinAt
      · simp
      · exact (ih (j + 1)).congr
          (fun u hu =>
            (saddlePositiveContourMoment_hasDerivAt_of_positiveContour
              hD ha j hu).deriv)
theorem saddlePositiveContourMoment_contDiffOn_infty_of_positiveContour
    {D : ℝ → ℂ}
    (hD : ∀ k : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ k * D t))
    {a : ℝ} (ha : 0 < a) (j : ℕ) :
    ContDiffOn ℝ ∞
      (saddlePositiveContourMoment a j D)
      (Set.Ioi (1 : ℝ)) := by
  rw [contDiffOn_infty]
  exact fun n =>
    saddlePositiveContourMoment_contDiffOn_of_positiveContour
      hD ha n j
theorem saddlePositiveContourMoment_iteratedDeriv_of_positiveContour
    {D : ℝ → ℂ}
    (hD : ∀ k : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ k * D t))
    {a : ℝ} (ha : 0 < a) (n j : ℕ)
    {u : ℝ} (hu : u ∈ Set.Ioi (1 : ℝ)) :
    iteratedDeriv n (saddlePositiveContourMoment a j D) u =
      saddlePositiveContourMoment a (j + n) D u := by
  induction n generalizing j u with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hevent :
          deriv (saddlePositiveContourMoment a j D) =ᶠ[𝓝 u]
            saddlePositiveContourMoment a (j + 1) D := by
        filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
        exact
          (saddlePositiveContourMoment_hasDerivAt_of_positiveContour
            hD ha j hv).deriv
      rw [hevent.iteratedDeriv_eq n]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! ih (j + 1) hu
def saddleContourMomentL1
    (a : ℝ) (j : ℕ) (D : ℝ → ℂ) : ℝ :=
  ∫ t : ℝ,
    ‖(saddleContourFallingPolynomial a j).eval
        (t : ℂ) * D t‖
theorem saddlePositiveContourMoment_norm_le
    {D : ℝ → ℂ}
    (hD : ∀ k : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ k * D t))
    (a : ℝ) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    ‖saddlePositiveContourMoment a j D u‖ ≤
      u ^ (-a / 2 - (j : ℝ)) *
        saddleContourMomentL1 a j D := by
  let W : ℝ → ℂ := fun t =>
    (saddleContourFallingPolynomial a j).eval
      (t : ℂ) * D t
  have hW : Integrable W := by
    exact saddlePolynomialWeightedData_integrable hD
      (saddleContourFallingPolynomial a j)
  unfold saddlePositiveContourMoment saddleContourMomentL1
  calc
    ‖∫ t : ℝ,
      saddlePositiveCpow
        (saddleContourExponent a t - (j : ℂ)) u *
        ((saddleContourFallingPolynomial a j).eval
          (t : ℂ) * D t)‖ ≤
      ∫ t : ℝ,
        ‖saddlePositiveCpow
          (saddleContourExponent a t - (j : ℂ)) u *
          ((saddleContourFallingPolynomial a j).eval
            (t : ℂ) * D t)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t : ℝ,
        u ^ (-a / 2 - (j : ℝ)) *
          ‖(saddleContourFallingPolynomial a j).eval
            (t : ℂ) * D t‖ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with t
          rw [norm_mul]
          congr 1
          unfold saddlePositiveCpow
          rw [max_eq_left hu.le,
            Complex.norm_cpow_eq_rpow_re_of_pos hu,
            saddleContourExponent_sub_nat_re]
    _ = u ^ (-a / 2 - (j : ℝ)) *
          (∫ t : ℝ,
            ‖(saddleContourFallingPolynomial a j).eval
              (t : ℂ) * D t‖) := by
          exact integral_const_mul_of_integrable hW.norm
theorem plusSaddlePositiveSquaredContour_contDiffOn
    {ε ℓ a : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ha : 0 < a) :
    ContDiffOn ℝ ∞
      (plusSaddlePositiveSquaredContour ε ℓ a)
      (Set.Ioi (1 : ℝ)) := by
  unfold plusSaddlePositiveSquaredContour
  apply contDiffOn_const.mul
  apply saddlePositiveContourMoment_contDiffOn_infty_of_positiveContour
      (a := a) (j := 0) _ ha
  intro k
  exact plusSaddleMellinData_shiftedLine_moment_integrable
    hε hℓ horder
    (fun n => saddlePositiveContour_ne_pole ha n) k
theorem minusSaddlePositiveSquaredContour_contDiffOn
    {ε ℓ a : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ha : 0 < a) :
    ContDiffOn ℝ ∞
      (minusSaddlePositiveSquaredContour ε ℓ a)
      (Set.Ioi (1 : ℝ)) := by
  unfold minusSaddlePositiveSquaredContour
  apply contDiffOn_const.mul
  apply saddlePositiveContourMoment_contDiffOn_infty_of_positiveContour
      (a := a) (j := 0) _ ha
  intro k
  exact minusSaddleMellinData_shiftedLine_moment_integrable
    hε hℓ horder
    (fun n => saddlePositiveContour_ne_pole ha n) k
theorem plusSaddlePositiveSquaredContour_eq_of_pos
    {ε ℓ a b u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) :
    plusSaddlePositiveSquaredContour ε ℓ a u =
      plusSaddlePositiveSquaredContour ε ℓ b u := by
  have hroot : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsquare : (Real.sqrt u) ^ 2 = u :=
    Real.sq_sqrt hu.le
  calc
    plusSaddlePositiveSquaredContour ε ℓ a u =
      plusSaddlePositiveSquaredContour ε ℓ a
        ((Real.sqrt u) ^ 2) := by rw [hsquare]
    _ = plusSaddleProfile ε ℓ (Real.sqrt u) :=
      (plusSaddleProfile_eq_positive_squaredContour
        hε hℓ horder hroot ha).symm
    _ = plusSaddlePositiveSquaredContour ε ℓ b
        ((Real.sqrt u) ^ 2) :=
      plusSaddleProfile_eq_positive_squaredContour
        hε hℓ horder hroot hb
    _ = plusSaddlePositiveSquaredContour ε ℓ b u := by
      rw [hsquare]
theorem minusSaddlePositiveSquaredContour_eq_of_pos
    {ε ℓ a b u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) :
    minusSaddlePositiveSquaredContour ε ℓ a u =
      minusSaddlePositiveSquaredContour ε ℓ b u := by
  have hroot : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsquare : (Real.sqrt u) ^ 2 = u :=
    Real.sq_sqrt hu.le
  calc
    minusSaddlePositiveSquaredContour ε ℓ a u =
      minusSaddlePositiveSquaredContour ε ℓ a
        ((Real.sqrt u) ^ 2) := by rw [hsquare]
    _ = minusSaddleProfile ε ℓ (Real.sqrt u) :=
      (minusSaddleProfile_eq_positive_squaredContour
        hε hℓ horder hroot ha).symm
    _ = minusSaddlePositiveSquaredContour ε ℓ b
        ((Real.sqrt u) ^ 2) :=
      minusSaddleProfile_eq_positive_squaredContour
        hε hℓ horder hroot hb
    _ = minusSaddlePositiveSquaredContour ε ℓ b u := by
      rw [hsquare]
def saddleOuterCutoff (u : ℝ) : ℂ :=
  (Real.smoothTransition (u - 2) : ℂ)
theorem saddleOuterCutoff_contDiff :
    ContDiff ℝ ∞ saddleOuterCutoff := by
  unfold saddleOuterCutoff
  exact Complex.ofRealCLM.contDiff.comp
    (Real.smoothTransition.contDiff.comp
      (contDiff_id.sub contDiff_const))
def plusSaddleOuterSquaredProfile (ε ℓ u : ℝ) : ℂ :=
  saddleOuterCutoff u *
    plusSaddlePositiveSquaredContour ε ℓ 2 u
def minusSaddleOuterSquaredProfile (ε ℓ u : ℝ) : ℂ :=
  saddleOuterCutoff u *
    minusSaddlePositiveSquaredContour ε ℓ 2 u
theorem plusSaddleOuterSquaredProfile_contDiff
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ContDiff ℝ ∞ (plusSaddleOuterSquaredProfile ε ℓ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro u
  by_cases hu : u < (2 : ℝ)
  · have hevent :
        plusSaddleOuterSquaredProfile ε ℓ =ᶠ[𝓝 u]
          (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds hu] with v hv
      change v < 2 at hv
      have hvzero :
          Real.smoothTransition (v - 2) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      simp [plusSaddleOuterSquaredProfile,
        saddleOuterCutoff, hvzero]
    exact contDiffAt_const.congr_of_eventuallyEq hevent
  · have hone : u ∈ Set.Ioi (1 : ℝ) := by
      change 1 < u
      linarith
    have hcontour :
        ContDiffAt ℝ ∞
          (plusSaddlePositiveSquaredContour ε ℓ 2) u :=
      (plusSaddlePositiveSquaredContour_contDiffOn
        hε hℓ horder (by norm_num)).contDiffAt
          (isOpen_Ioi.mem_nhds hone)
    exact saddleOuterCutoff_contDiff.contDiffAt.mul hcontour
theorem minusSaddleOuterSquaredProfile_contDiff
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ContDiff ℝ ∞ (minusSaddleOuterSquaredProfile ε ℓ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro u
  by_cases hu : u < (2 : ℝ)
  · have hevent :
        minusSaddleOuterSquaredProfile ε ℓ =ᶠ[𝓝 u]
          (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds hu] with v hv
      change v < 2 at hv
      have hvzero :
          Real.smoothTransition (v - 2) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      simp [minusSaddleOuterSquaredProfile,
        saddleOuterCutoff, hvzero]
    exact contDiffAt_const.congr_of_eventuallyEq hevent
  · have hone : u ∈ Set.Ioi (1 : ℝ) := by
      change 1 < u
      linarith
    have hcontour :
        ContDiffAt ℝ ∞
          (minusSaddlePositiveSquaredContour ε ℓ 2) u :=
      (minusSaddlePositiveSquaredContour_contDiffOn
        hε hℓ horder (by norm_num)).contDiffAt
          (isOpen_Ioi.mem_nhds hone)
    exact saddleOuterCutoff_contDiff.contDiffAt.mul hcontour
theorem plusSaddleOuterSquaredProfile_eq_zero
    (ε ℓ : ℝ) {u : ℝ} (hu : u < 2) :
    plusSaddleOuterSquaredProfile ε ℓ u = 0 := by
  have hcut : Real.smoothTransition (u - 2) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  simp [plusSaddleOuterSquaredProfile, saddleOuterCutoff, hcut]
theorem minusSaddleOuterSquaredProfile_eq_zero
    (ε ℓ : ℝ) {u : ℝ} (hu : u < 2) :
    minusSaddleOuterSquaredProfile ε ℓ u = 0 := by
  have hcut : Real.smoothTransition (u - 2) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  simp [minusSaddleOuterSquaredProfile, saddleOuterCutoff, hcut]
theorem plusSaddleOuterSquaredProfile_eq_positiveContour
    {ε ℓ a u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ha : 0 < a) (hu : 3 < u) :
    plusSaddleOuterSquaredProfile ε ℓ u =
      plusSaddlePositiveSquaredContour ε ℓ a u := by
  have hcut : Real.smoothTransition (u - 2) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  unfold plusSaddleOuterSquaredProfile saddleOuterCutoff
  rw [hcut]
  norm_num
  exact plusSaddlePositiveSquaredContour_eq_of_pos
    hε hℓ horder (by norm_num) ha (by linarith)
theorem minusSaddleOuterSquaredProfile_eq_positiveContour
    {ε ℓ a u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ha : 0 < a) (hu : 3 < u) :
    minusSaddleOuterSquaredProfile ε ℓ u =
      minusSaddlePositiveSquaredContour ε ℓ a u := by
  have hcut : Real.smoothTransition (u - 2) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  unfold minusSaddleOuterSquaredProfile saddleOuterCutoff
  rw [hcut]
  norm_num
  exact minusSaddlePositiveSquaredContour_eq_of_pos
    hε hℓ horder (by norm_num) ha (by linarith)
theorem saddleOuterSquaredProfile_schwartz_decay
    {G : ℝ → ℂ}
    (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ u : ℝ, u < 2 → G u = 0)
    (D : ℝ → ℝ → ℂ)
    (hD : ∀ a : ℝ, 0 < a → ∀ j : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ j * D a t))
    (htail : ∀ a : ℝ, 0 < a → ∀ u : ℝ, 3 < u →
      G u =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          saddlePositiveContourMoment a 0 (D a) u)
    (k n : ℕ) :
    ∃ C : ℝ, ∀ u : ℝ,
      ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖ ≤ C := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let a : ℝ := 2 * ((k + 1 : ℕ) : ℝ)
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  have hcontinuous :
      Continuous (fun u : ℝ =>
        ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖) := by
    apply Continuous.mul (by fun_prop)
    exact
      (hG.of_le (mod_cast le_top)).continuous_iteratedFDeriv'.norm
  have hbounded :
      BddAbove
        ((fun u : ℝ =>
          ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖) ''
            Set.Icc (2 : ℝ) 4) :=
    isCompact_Icc.bddAbove_image hcontinuous.continuousOn
  obtain ⟨B, hB⟩ := hbounded
  let L : ℝ := saddleContourMomentL1 a n (D a)
  have hL : 0 ≤ L := by
    unfold L saddleContourMomentL1
    exact integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨max 0 (max B (‖c‖ * L)), ?_⟩
  intro u
  by_cases hlow : u < (2 : ℝ)
  · have hevent : G =ᶠ[𝓝 u]
          (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds hlow] with v hv
      exact hzero v hv
    have hiter :=
      (hevent.iteratedFDeriv ℝ n).eq_of_nhds
    rw [hiter]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply,
      norm_zero, mul_zero] using!
      (le_max_left (0 : ℝ) (max B (‖c‖ * L)))
  · by_cases hupper : u ≤ (4 : ℝ)
    · have hmem : u ∈ Set.Icc (2 : ℝ) 4 :=
        ⟨le_of_not_gt hlow, hupper⟩
      have hinner :
          ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖ ≤ B :=
        hB ⟨u, hmem, rfl⟩
      exact hinner.trans
        ((le_max_left B (‖c‖ * L)).trans
          (le_max_right 0 _))
    · have hu4 : (4 : ℝ) < u := lt_of_not_ge hupper
      have hu3 : (3 : ℝ) < u := by linarith
      have hu0 : (0 : ℝ) < u := by linarith
      have hu1 : (1 : ℝ) ≤ u := by linarith
      have huoi : u ∈ Set.Ioi (1 : ℝ) := by
        change 1 < u
        linarith
      have hevent :
          G =ᶠ[𝓝 u]
            (fun v : ℝ =>
              c * saddlePositiveContourMoment a 0 (D a) v) := by
        filter_upwards [Ioi_mem_nhds hu3] with v hv
        exact htail a ha v hv
      have hiter :
          iteratedDeriv n G u =
            c * saddlePositiveContourMoment a n (D a) u := by
        rw [hevent.iteratedDeriv_eq n,
          iteratedDeriv_const_mul_field,
          saddlePositiveContourMoment_iteratedDeriv_of_positiveContour
            (hD a ha) ha n 0 huoi]
        simp
      have hmoment :
          ‖saddlePositiveContourMoment a n (D a) u‖ ≤
            u ^ (-a / 2 - (n : ℝ)) * L := by
        exact saddlePositiveContourMoment_norm_le
          (hD a ha) a n hu0
      have hexponent :
          -a / 2 - (n : ℝ) ≤ -(k : ℝ) := by
        try dsimp [a]
        push_cast
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hpower :
          u ^ (-a / 2 - (n : ℝ)) ≤
            u ^ (-(k : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hu1 hexponent
      have hcancel :
          u ^ k * u ^ (-(k : ℝ)) = 1 := by
        rw [Real.rpow_neg hu0.le, Real.rpow_natCast]
        exact mul_inv_cancel₀ (pow_ne_zero _ hu0.ne')
      have htailbound :
          ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖ ≤
            ‖c‖ * L := by
        calc
          ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖ =
              u ^ k *
                (‖c‖ *
                  ‖saddlePositiveContourMoment a n (D a) u‖) := by
                rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
                  hiter, norm_mul, Real.norm_of_nonneg hu0.le]
          _ ≤ u ^ k *
              (‖c‖ *
                (u ^ (-a / 2 - (n : ℝ)) * L)) := by
                gcongr
          _ ≤ u ^ k *
              (‖c‖ * (u ^ (-(k : ℝ)) * L)) := by
                gcongr
          _ = (u ^ k * u ^ (-(k : ℝ))) *
                (‖c‖ * L) := by ring
          _ = ‖c‖ * L := by rw [hcancel, one_mul]
      exact htailbound.trans
        ((le_max_right B (‖c‖ * L)).trans
          (le_max_right 0 _))
theorem plusSaddleOuterSquaredProfile_schwartz_decay
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (k n : ℕ) :
    ∃ C : ℝ, ∀ u : ℝ,
      ‖u‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (plusSaddleOuterSquaredProfile ε ℓ) u‖ ≤ C := by
  apply saddleOuterSquaredProfile_schwartz_decay
    (plusSaddleOuterSquaredProfile_contDiff hε hℓ horder)
    (fun u hu =>
      plusSaddleOuterSquaredProfile_eq_zero ε ℓ hu)
    (fun a t =>
      plusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I))
    _ _ k n
  · intro a ha j
    exact plusSaddleMellinData_shiftedLine_moment_integrable
      hε hℓ horder
      (fun m => saddlePositiveContour_ne_pole ha m) j
  · intro a ha u hu
    simpa [plusSaddlePositiveSquaredContour] using!
      plusSaddleOuterSquaredProfile_eq_positiveContour
        hε hℓ horder ha hu
theorem minusSaddleOuterSquaredProfile_schwartz_decay
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (k n : ℕ) :
    ∃ C : ℝ, ∀ u : ℝ,
      ‖u‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (minusSaddleOuterSquaredProfile ε ℓ) u‖ ≤ C := by
  apply saddleOuterSquaredProfile_schwartz_decay
    (minusSaddleOuterSquaredProfile_contDiff hε hℓ horder)
    (fun u hu =>
      minusSaddleOuterSquaredProfile_eq_zero ε ℓ hu)
    (fun a t =>
      minusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I))
    _ _ k n
  · intro a ha j
    exact minusSaddleMellinData_shiftedLine_moment_integrable
      hε hℓ horder
      (fun m => saddlePositiveContour_ne_pole ha m) j
  · intro a ha u hu
    simpa [minusSaddlePositiveSquaredContour] using!
      minusSaddleOuterSquaredProfile_eq_positiveContour
        hε hℓ horder ha hu
def plusSaddleOuterScalarSchwartz
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    𝓢(ℝ, ℂ) where
  toFun := plusSaddleOuterSquaredProfile ε ℓ
  smooth' := plusSaddleOuterSquaredProfile_contDiff
    hε hℓ horder
  decay' := plusSaddleOuterSquaredProfile_schwartz_decay
    hε hℓ horder
def minusSaddleOuterScalarSchwartz
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    𝓢(ℝ, ℂ) where
  toFun := minusSaddleOuterSquaredProfile ε ℓ
  smooth' := minusSaddleOuterSquaredProfile_contDiff
    hε hℓ horder
  decay' := minusSaddleOuterSquaredProfile_schwartz_decay
    hε hℓ horder
def saddleSquaredSchwartzPullback (d : ℕ) :
    𝓢(ℝ, ℂ) →L[ℂ] TestFunction d := by
  apply SchwartzMap.compCLM ℂ
    (Function.hasTemperateGrowth_norm_sq (Euclidean d))
  refine ⟨1, 1, ?_⟩
  intro x
  change ‖x‖ ≤ 1 * (1 + ‖‖x‖ ^ 2‖) ^ 1
  rw [one_mul, pow_one, Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (‖x‖ - (1 / 2 : ℝ))]
def plusSaddleOuterSchwartz
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (d : ℕ) : TestFunction d :=
  saddleSquaredSchwartzPullback d
    (plusSaddleOuterScalarSchwartz hε hℓ horder)
def minusSaddleOuterSchwartz
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (d : ℕ) : TestFunction d :=
  saddleSquaredSchwartzPullback d
    (minusSaddleOuterScalarSchwartz hε hℓ horder)
@[simp] theorem plusSaddleOuterSchwartz_apply
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (d : ℕ) (x : Euclidean d) :
    plusSaddleOuterSchwartz hε hℓ horder d x =
      plusSaddleOuterSquaredProfile ε ℓ (‖x‖ ^ 2) := rfl
@[simp] theorem minusSaddleOuterSchwartz_apply
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (d : ℕ) (x : Euclidean d) :
    minusSaddleOuterSchwartz hε hℓ horder d x =
      minusSaddleOuterSquaredProfile ε ℓ (‖x‖ ^ 2) := rfl
theorem plusSaddleOuterDifference_hasCompactSupport
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (d : ℕ) :
    HasCompactSupport (fun x : Euclidean d =>
      plusSaddleProfile ε ℓ ‖x‖ -
        plusSaddleOuterSchwartz hε hℓ horder d x) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Euclidean d) 2)
  intro x hx
  by_contra houtside
  have hr2 : (2 : ℝ) < ‖x‖ := by
    by_contra hnot
    apply houtside
    exact mem_closedBall_zero_iff.mpr (le_of_not_gt hnot)
  have hr : 0 < ‖x‖ := by linarith
  have hsquare : (3 : ℝ) < ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - 2)]
  change
    plusSaddleProfile ε ℓ ‖x‖ -
      plusSaddleOuterSchwartz hε hℓ horder d x ≠ 0 at hx
  have houter :
      plusSaddleOuterSchwartz hε hℓ horder d x =
        plusSaddlePositiveSquaredContour ε ℓ 2 (‖x‖ ^ 2) := by
    rw [plusSaddleOuterSchwartz_apply]
    exact plusSaddleOuterSquaredProfile_eq_positiveContour
      (a := (2 : ℝ)) hε hℓ horder (by norm_num) hsquare
  have hsource :
      plusSaddleProfile ε ℓ ‖x‖ =
        plusSaddlePositiveSquaredContour ε ℓ 2 (‖x‖ ^ 2) :=
    plusSaddleProfile_eq_positive_squaredContour
      (a := (2 : ℝ)) hε hℓ horder hr (by norm_num)
  exact hx (by rw [hsource, houter, sub_self])
theorem minusSaddleOuterDifference_hasCompactSupport
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (d : ℕ) :
    HasCompactSupport (fun x : Euclidean d =>
      minusSaddleProfile ε ℓ ‖x‖ -
        minusSaddleOuterSchwartz hε hℓ horder d x) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Euclidean d) 2)
  intro x hx
  by_contra houtside
  have hr2 : (2 : ℝ) < ‖x‖ := by
    by_contra hnot
    apply houtside
    exact mem_closedBall_zero_iff.mpr (le_of_not_gt hnot)
  have hr : 0 < ‖x‖ := by linarith
  have hsquare : (3 : ℝ) < ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - 2)]
  change
    minusSaddleProfile ε ℓ ‖x‖ -
      minusSaddleOuterSchwartz hε hℓ horder d x ≠ 0 at hx
  have houter :
      minusSaddleOuterSchwartz hε hℓ horder d x =
        minusSaddlePositiveSquaredContour ε ℓ 2 (‖x‖ ^ 2) := by
    rw [minusSaddleOuterSchwartz_apply]
    exact minusSaddleOuterSquaredProfile_eq_positiveContour
      (a := (2 : ℝ)) hε hℓ horder (by norm_num) hsquare
  have hsource :
      minusSaddleProfile ε ℓ ‖x‖ =
        minusSaddlePositiveSquaredContour ε ℓ 2 (‖x‖ ^ 2) :=
    minusSaddleProfile_eq_positive_squaredContour
      (a := (2 : ℝ)) hε hℓ horder hr (by norm_num)
  exact hx (by rw [hsource, houter, sub_self])
def plusSaddleSchwartz
    {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    TestFunction d where
  toFun := plusSaddleFunction ε d
  smooth' := plusSaddleFunction_contDiff hε hd horder
  decay' := by
    intro k n
    let ℓ : ℝ := (d : ℝ) / 2
    have hℓ : 0 < ℓ := by
      try dsimp [ℓ]
      exact div_pos (by exact_mod_cast hd) (by norm_num)
    let tail : TestFunction d :=
      plusSaddleOuterSchwartz hε hℓ horder d
    have hcompact :
        HasCompactSupport (fun x : Euclidean d =>
          plusSaddleFunction ε d x - tail x) := by
      simpa [plusSaddleFunction, ℓ, tail] using!
        plusSaddleOuterDifference_hasCompactSupport
          hε hℓ horder d
    have hsmooth :
        ContDiff ℝ ∞ (fun x : Euclidean d =>
          plusSaddleFunction ε d x - tail x) :=
      (plusSaddleFunction_contDiff hε hd horder).sub
        (tail.smooth ⊤)
    let correction : TestFunction d :=
      hcompact.toSchwartzMap hsmooth
    let full : TestFunction d := tail + correction
    have hfun :
        plusSaddleFunction ε d =
          (fun x : Euclidean d => full x) := by
      funext x
      change
        plusSaddleFunction ε d x =
          tail x +
            (plusSaddleFunction ε d x - tail x)
      ring
    rw [hfun]
    exact full.decay' k n
def minusSaddleSchwartz
    {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    TestFunction d where
  toFun := minusSaddleFunction ε d
  smooth' := minusSaddleFunction_contDiff hε hd horder
  decay' := by
    intro k n
    let ℓ : ℝ := (d : ℝ) / 2
    have hℓ : 0 < ℓ := by
      try dsimp [ℓ]
      exact div_pos (by exact_mod_cast hd) (by norm_num)
    let tail : TestFunction d :=
      minusSaddleOuterSchwartz hε hℓ horder d
    have hcompact :
        HasCompactSupport (fun x : Euclidean d =>
          minusSaddleFunction ε d x - tail x) := by
      simpa [minusSaddleFunction, ℓ, tail] using!
        minusSaddleOuterDifference_hasCompactSupport
          hε hℓ horder d
    have hsmooth :
        ContDiff ℝ ∞ (fun x : Euclidean d =>
          minusSaddleFunction ε d x - tail x) :=
      (minusSaddleFunction_contDiff hε hd horder).sub
        (tail.smooth ⊤)
    let correction : TestFunction d :=
      hcompact.toSchwartzMap hsmooth
    let full : TestFunction d := tail + correction
    have hfun :
        minusSaddleFunction ε d =
          (fun x : Euclidean d => full x) := by
      funext x
      change
        minusSaddleFunction ε d x =
          tail x +
            (minusSaddleFunction ε d x - tail x)
      ring
    rw [hfun]
    exact full.decay' k n
def saddleSourceContourEnvelopeScale
    (ε ℓ u : ℝ) : ℝ :=
  Real.exp (-(ℓ * u) * Real.log Real.pi / 2) *
    Real.Gamma (ℓ * (1 + u) / 2) *
      Real.exp (ℓ * realHyperbolicShellPhase ε u)
def saddleSourceContourDamping
    (ε ℓ u T : ℝ) : ℝ :=
  upperGammaDamping ℓ (1 + u) T +
    positiveShellDamping ε ℓ (u - 1) T -
      upperShortShellDamping ε ℓ (u - 1) T
def saddleSourceNormalizedEnvelope
    (ε ℓ u T : ℝ) : ℂ :=
  saddleMellinEnvelope ε ℓ
      (saddleSourceMellinContour ℓ u T) /
    (saddleSourceContourEnvelopeScale ε ℓ u : ℂ)
def saddleSourceCenteredEnvelope
    (ε ℓ u v T : ℝ) : ℂ :=
  saddleSourceNormalizedEnvelope ε ℓ u T *
    Complex.exp (Complex.I * ((ℓ * T * v : ℝ) : ℂ))
def saddleSourceCenteredPlusIntegrand
    (ε ℓ u v T : ℝ) : ℂ :=
  saddleSourceCenteredEnvelope ε ℓ u v T *
    plusPolynomial ε ((T : ℂ) + Complex.I * (u : ℂ))
def saddleSourceCenteredMinusIntegrand
    (ε ℓ u v T : ℝ) : ℂ :=
  saddleSourceCenteredEnvelope ε ℓ u v T *
    minusPolynomial ε ((T : ℂ) + Complex.I * (u : ℂ))
@[simp] theorem saddleSourceContourDamping_eq_firstBranch
    (ε ℓ u T : ℝ) :
    saddleSourceContourDamping ε ℓ u T =
      upperFirstBranchSaddleDamping ε ℓ u T := rfl
@[simp] theorem saddleSourceContourDamping_eq_secondBranch
    (ε ℓ δ T : ℝ) :
    saddleSourceContourDamping ε ℓ (1 + δ) T =
      upperSaddleDamping ε ℓ δ T := by
  have hη : 1 + (1 + δ) = 2 + δ := by ring
  have hδ : (1 + δ) - 1 = δ := by ring
  simp [saddleSourceContourDamping, upperSaddleDamping,
    hη, hδ]
def saddleSourceCenteredPrefactor
    (ε ℓ u v : ℝ) : ℝ :=
  (ℓ / (2 * Real.pi)) *
    Real.exp (-(ℓ * (1 + u) * v)) *
      saddleSourceContourEnvelopeScale ε ℓ u
def saddleSourceGaussianVariance
    (ε ℓ u : ℝ) : ℝ :=
  upperSaddleVariance ε ℓ (u - 1)
def saddleSourceGaussianKernel
    (ε ℓ u T : ℝ) : ℝ :=
  Real.exp
    (-(ℓ * saddleSourceGaussianVariance ε ℓ u / 2) * T ^ 2)
def saddleSourceGaussianPlusIntegrand
    (ε ℓ u T : ℝ) : ℂ :=
  (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
    plusPolynomial ε (Complex.I * (u : ℂ))
def saddleSourceGaussianMinusIntegrand
    (ε ℓ u T : ℝ) : ℂ :=
  (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
    minusPolynomial ε (Complex.I * (u : ℂ))
end
noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology
def upperImaginaryExp (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (x : ℂ))
def upperGammaCenteredKernel
    (ℓ η T a : ℝ) : ℂ :=
  (upperImaginaryExp (a * T) - 1 -
    Complex.I * ((a * T : ℝ) : ℂ)) *
      (upperGammaMeasureDensity ℓ η a : ℂ)
def upperGammaCenteredPhase
    (ℓ η T : ℝ) : ℂ :=
  ∫ a : ℝ in Ioi 0, upperGammaCenteredKernel ℓ η T a
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
def saddleSourceCosineQuadraticRemainder
    (a u T : ℝ) : ℂ :=
  Complex.cos
      ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) -
    (Real.cosh (u * a) : ℂ) +
    Complex.I * ((a * T * Real.sinh (u * a) : ℝ) : ℂ) +
    ((a ^ 2 * T ^ 2 / 2 * Real.cosh (u * a) : ℝ) : ℂ)
def saddleSourceShellCenteredPhase
    (ε ℓ u T : ℝ) : ℂ :=
  (ℓ : ℂ) *
    (mellinShellPhase ε
        ((T : ℂ) + Complex.I * (u : ℂ)) -
      (realHyperbolicShellPhase ε u : ℂ) +
      Complex.I *
        ((T * saddleSourceShellDerivative ε u : ℝ) : ℂ))
def saddleSourceShellQuadraticRemainder
    (ε u T : ℝ) : ℂ :=
  (∫ a in shortCutoff ε..shortEndpoint ε,
    (shortShellDensity ε a : ℂ) *
      saddleSourceCosineQuadraticRemainder a u T) +
  (∫ a in shellLocation ε..shellLocation ε + 1,
    (positiveShellDensity ε a : ℂ) *
      saddleSourceCosineQuadraticRemainder a u T)
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
def upperGammaQuadraticKernel
    (ℓ η T a : ℝ) : ℂ :=
  (((a * T) ^ 2 / 2 *
    upperGammaMeasureDensity ℓ η a : ℝ) : ℂ)
def upperGammaCubicRemainderKernel
    (ℓ η T a : ℝ) : ℂ :=
  (upperImaginaryExp (a * T) - 1 -
    Complex.I * ((a * T : ℝ) : ℂ) +
      (((a * T) ^ 2 / 2 : ℝ) : ℂ)) *
        (upperGammaMeasureDensity ℓ η a : ℂ)
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
def upperCenteredLaplaceKernel
    (c T a : ℝ) : ℂ :=
  (upperImaginaryExp (a * T) - 1 -
      Complex.I * ((a * T : ℝ) : ℂ)) *
    ((Real.exp (-c * a) / a : ℝ) : ℂ)
def upperGammaCenteredTruncatedKernel
    (ℓ η T : ℝ) (n : ℕ) (a : ℝ) : ℂ :=
  upperCenteredLaplaceKernel η T a *
    ((∑ k ∈ Finset.range (n + 1),
      Real.exp (-(2 * a / ℓ)) ^ k : ℝ) : ℂ)
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
def saddleSourceStationaryLogRadius
    (ε ℓ u : ℝ) : ℝ :=
  -(Real.log Real.pi) / 2 +
    saddleDigamma (ℓ * (1 + u) / 2) / 2 +
      saddleSourceShellDerivative ε u
def saddleSourceCenteredPhase
    (ε ℓ u T : ℝ) : ℂ :=
  upperGammaCenteredPhase ℓ (1 + u) T +
    saddleSourceShellCenteredPhase ε ℓ u T
def saddleSourceGaussianPhaseRemainder
    (ε ℓ u T : ℝ) : ℂ :=
  saddleSourceCenteredPhase ε ℓ u T +
    ((ℓ * saddleSourceGaussianVariance ε ℓ u / 2 *
      T ^ 2 : ℝ) : ℂ)
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
end
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
def saddleGaussianTailWeight (T : ℝ) : ℝ :=
  1 + |T| ^ 3
def saddleGaussianTailSet (R : ℝ) : Set ℝ :=
  {T : ℝ | R ≤ |T|}
def saddleGaussianOuterPhi
    (B Q c ℓ δ : ℝ) : ℝ :=
  (B + 1) / 2 * δ + 4 * Real.log (2 + δ) -
    c * ℓ * Q * Real.exp (B * δ)
def saddleSourceFirstBranchVarianceCoefficient
    (ε : ℝ) : ℝ :=
  (3 / 2 : ℝ) +
    (2 + ε / 2) *
      upperPositiveShellVariance ε (ε / 2)
def saddleFirstBranchTailLogMajorant
    (c C ℓ : ℝ) : ℝ :=
  4 * Real.sqrt (Real.pi * C / c) *
      Real.exp
        (-(c / (4 * C)) *
          (Real.log ℓ / 4) ^ (1 / 6 : ℝ)) +
    (16 / c) *
      Real.sqrt (C / (Real.log ℓ / 4))
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
def saddleSourceFirstBranchThirdMomentCoefficient
    (ε : ℝ) : ℝ :=
  (5 / 2 : ℝ) +
    (3 / 2 : ℝ) * shortEndpoint ε * (2 + ε / 2) +
    (2 + ε / 2) ^ 2 *
      upperPositiveShellThirdMoment ε (ε / 2)
def saddleSourceSecondBranchVarianceFloor (ε : ℝ) : ℝ :=
  (99 / 200 : ℝ) * (shellLocation ε) ^ 2 *
    shellWeight ε *
      Real.exp ((ε / 2) * shellLocation ε)
end
noncomputable section
open Filter Set
open scoped Topology
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
def saddleSourceFirstBranchCentralRadius
    (ε ℓ u : ℝ) : ℝ :=
  (ℓ * (1 + u)) ^ (1 / 12 : ℝ) /
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)
def saddleSourceSecondBranchCentralRadius
    (ε ℓ u : ℝ) : ℝ :=
  ℓ ^ (1 / 12 : ℝ) /
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)
def saddleSourceSecondBranchLocalFrequency (ε : ℝ) : ℝ :=
  1 / (2 * (shellLocation ε + 1))
def saddleSourceSecondBranchGaussianRate
    (ε ℓ δ : ℝ) : ℝ :=
  (ℓ / (100 * Real.exp 1)) *
    saddleSourceGaussianVariance ε ℓ (1 + δ)
def saddleSourceSecondBranchGammaGaussianRate
    (ℓ δ : ℝ) : ℝ :=
  (ℓ / (8 * Real.exp 1)) / (2 + δ)
def saddleSourceSecondBranchGammaLinearRate
    (ℓ : ℝ) : ℝ :=
  ℓ / (8 * Real.exp 1)
def saddleSourceSecondBranchOuterBarrier
    (ε ℓ δ : ℝ) : ℝ :=
  (99 / 5000 : ℝ) * ℓ * shellWeight ε *
    Real.exp (δ * shellLocation ε) *
      saddleSourceSecondBranchLocalFrequency ε ^ 2
def saddleSourceSecondBranchMomentCoefficient : ℝ :=
  let C : ℝ := 8 * Real.exp 1
  2 * (1 + (6 * C) ^ 3) *
      (1 + 2 * Real.pi * C) +
    8 * C * (1 + (6 * C) ^ 3)
def saddleSourceSecondBranchVarianceCoefficient (ε : ℝ) : ℝ :=
  2 + (shellLocation ε + 1) ^ 2 * shellWeight ε
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
def saddleSourceGaussianNormalizedTailMajorant (x : ℝ) : ℝ :=
  4 * Real.sqrt (2 * Real.pi) *
    Real.exp (-(x ^ (1 / 6 : ℝ)) / 8)
end
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
end
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
end
noncomputable section
open Filter
open scoped Topology
def EventualLowerBound : Prop :=
  ∀ c : ℝ, c < criticalRadius →
    ∀ᶠ d : ℕ in atTop, c ≤ normalizedProgram d
def EventualUpperBound : Prop :=
  ∀ c : ℝ, criticalRadius < c →
    ∀ᶠ d : ℕ in atTop, normalizedProgram d ≤ c
def UniformAdmissibleLowerBound : Prop :=
  ∀ c : ℝ, c < criticalRadius →
    ∀ᶠ d : ℕ in atTop,
      ∀ f : Admissible d, c ≤ normalizedCost f
def ConstructivePrimalUpperBound : Prop :=
  ∀ c : ℝ, criticalRadius < c →
    ∀ᶠ d : ℕ in atTop,
      ∃ f : Admissible d, normalizedCost f ≤ c
structure OrderedEpsilonUpperConstruction where
  epsilonBound : ℝ
  epsilonBound_pos : 0 < epsilonBound
  normalizedRadius : ℝ → ℕ → ℝ
  limitingRadius : ℝ → ℝ
  limitingRadius_tendsto :
    Tendsto limitingRadius (𝓝[>] (0 : ℝ)) (𝓝 criticalRadius)
  normalizedRadius_tendsto :
    ∀ ε : ℝ, 0 < ε → ε < epsilonBound →
      Tendsto (normalizedRadius ε) atTop (𝓝 (limitingRadius ε))
  admissibleWitness :
    ∀ ε : ℝ, 0 < ε → ε < epsilonBound →
      ∀ᶠ d : ℕ in atTop,
        ∃ f : Admissible d, normalizedCost f ≤ normalizedRadius ε d
end
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology
def SaddleSourceSchwartzRealization : Prop :=
  ∀ ε : ℝ, 0 < ε →
    shortCutoff ε ≤ shortEndpoint ε →
      ∀ d : ℕ, 0 < d →
        ∃ fminus fplus : TestFunction d,
          (∀ x : Euclidean d,
            fminus x = minusSaddleFunction ε d x) ∧
          (∀ x : Euclidean d,
            fplus x = plusSaddleFunction ε d x)
def SaddleSourceEventualSigns : Prop :=
  ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ᶠ d : ℕ in atTop,
      (∀ x : Euclidean d,
        0 ≤ (plusSaddleFunction ε d x).re) ∧
      (∀ x : Euclidean d,
        saddleSourceRadius ε d ≤ ‖x‖ →
          (minusSaddleFunction ε d x).re ≤ 0)
noncomputable def saddleOrderedUpperConstruction
    (hschwartz : SaddleSourceSchwartzRealization)
    (hsigns : SaddleSourceEventualSigns) :
    OrderedEpsilonUpperConstruction := by
  have heventually :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        shortCutoff ε ≤ shortEndpoint ε ∧
          (∀ᶠ d : ℕ in atTop,
            (∀ x : Euclidean d,
              0 ≤ (plusSaddleFunction ε d x).re) ∧
            (∀ x : Euclidean d,
              saddleSourceRadius ε d ≤ ‖x‖ →
                (minusSaddleFunction ε d x).re ≤ 0)) :=
    eventually_upper_shortCutoff_le_shortEndpoint.and hsigns
  have hmembership :
      {ε : ℝ |
        shortCutoff ε ≤ shortEndpoint ε ∧
          (∀ᶠ d : ℕ in atTop,
            (∀ x : Euclidean d,
              0 ≤ (plusSaddleFunction ε d x).re) ∧
            (∀ x : Euclidean d,
              saddleSourceRadius ε d ≤ ‖x‖ →
                (minusSaddleFunction ε d x).re ≤ 0))} ∈
        𝓝[>] (0 : ℝ) := heventually
  have hexists :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hmembership
  let ε₀ : ℝ := Classical.choose hexists
  have hchosen := Classical.choose_spec hexists
  have hε₀ : 0 < ε₀ := hchosen.1
  have hinterval := hchosen.2
  refine
    { epsilonBound := ε₀
      epsilonBound_pos := hε₀
      normalizedRadius := fun ε d =>
        saddleSourceRadius ε d / Real.sqrt (d : ℝ)
      limitingRadius := limitingSaddleRadius
      limitingRadius_tendsto := tendsto_limitingSaddleRadius
      normalizedRadius_tendsto := ?_
      admissibleWitness := ?_ }
  · intro ε hε _hsmall
    exact tendsto_saddleSourceRadius_normalized hε
  · intro ε hε hsmall
    have hproperties := hinterval
      (show ε ∈ Ioo (0 : ℝ) ε₀ from ⟨hε, hsmall⟩)
    obtain ⟨horder, hsignε⟩ := hproperties
    filter_upwards [hsignε, eventually_gt_atTop (0 : ℕ)]
      with d hsign hd
    obtain ⟨fminus, fplus, hminus, hplus⟩ :=
      hschwartz ε hε horder d hd
    let f : Admissible d :=
      saddleSourceAdmissible hε hd horder
        (saddleSourceRadius_pos ε d)
        fminus fplus hminus hplus hsign.1 hsign.2
    refine ⟨f, ?_⟩
    exact le_of_eq (saddleSourceAdmissible_normalizedCost
      hε hd horder (saddleSourceRadius_pos ε d)
      fminus fplus hminus hplus hsign.1 hsign.2)
end
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
def lowerGammaBoundaryCapped (ℓ R D y : ℝ) : ℝ :=
  if y = 0 then D else min (lowerGammaBoundaryLog ℓ R y) D
def stripRegularizedOuter (ℓ : ℝ) (b : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ y : ℝ,
    stripRegularizedHolomorphicPoissonKernel ℓ z y *
      (b y : ℂ)
def lowerStripCappedGammaOuter
    (ℓ R D : ℝ) (z : ℂ) : ℂ :=
  stripRegularizedOuter ℓ
    (lowerGammaBoundaryCapped ℓ R D) z
end
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
def horizontalStripRealTraceExtension
    (a b : ℝ) (H : ℂ → ℝ)
    (bottom top : ℝ → ℝ) (z : ℂ) : ℝ :=
  if z.im = a then bottom z.re
  else if z.im = b then top z.re
  else H z
def lowerStripCappedGammaHarmonic
    (d : ℕ) (R D : ℝ) (z : ℂ) : ℝ :=
  horizontalStripRealTraceExtension
    (-((d : ℝ) / 2)) ((d : ℝ) / 2)
    (fun w : ℂ =>
      (lowerStripCappedGammaOuter ((d : ℝ) / 2) R D w).re)
    (lowerGammaBoundaryCapped ((d : ℝ) / 2) R D)
    (fun _ : ℝ => 0) z
end
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
def stripPoissonWeightedMeasure
    (σ s : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun x : ℝ =>
      ENNReal.ofReal (stripPoissonKernel σ (s - x)))
def lowerGammaScaledCappedClipped
    (d : ℕ) (c D n Y : ℝ) : ℝ :=
  max
    (lowerGammaBoundaryCapped ((d : ℝ) / 2)
      (c * Real.sqrt d) D (((d : ℝ) / 2) * Y) + n)
    0
def lowerGammaScaledCappedLowerClip
    (d : ℕ) (c D n Y : ℝ) : ℝ :=
  max
    (lowerGammaBoundaryCapped ((d : ℝ) / 2)
      (c * Real.sqrt d) D (((d : ℝ) / 2) * Y))
    (-n)
def lowerRiemannErrorMajorant (T : ℝ) : ℝ :=
  3 * |lowerRiemannLog T 0| +
    2 * |lowerRiemannLog T 1| +
      (1 / 2 : ℝ) *
        Real.log (lowerCoth (Real.pi * |T| / 2))
def lowerRiemannPoissonError (σ : ℝ) : ℝ :=
  ∫ T : ℝ,
    stripPoissonKernel σ T * lowerRiemannErrorMajorant T
def stripPoissonCoreMass (σ : ℝ) : ℝ :=
  ∫ T in Icc (-1 : ℝ) 1, stripPoissonKernel σ T
def lowerInverseQuadraticMass : ℝ :=
  ∫ S : ℝ, 1 / (1 + |S|) ^ 2
end
noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal Interval Topology
end
noncomputable section
open Set
def quotientRootMap (d : ℕ) (x : ℝ) : ℝ :=
  x ^ ((d : ℝ)⁻¹) / Real.sqrt (d : ℝ)
def packingGeometricRoot (d : ℕ) : ℝ :=
  (unitBallVolume d / (2 : ℝ) ^ d) ^ ((d : ℝ)⁻¹) *
    Real.sqrt (d : ℝ)
end
noncomputable section
open Filter
open scoped Nat Topology
def normalizedVolumeLog (d : ℕ) : ℝ :=
  Real.log (unitBallVolume d) / (d : ℝ) +
    Real.log (d : ℝ) / 2
def normalizedVolumeRoot (d : ℕ) : ℝ :=
  unitBallVolume d ^ ((d : ℝ)⁻¹) * Real.sqrt (d : ℝ)
end
noncomputable section
open Filter Function MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace Pointwise ContDiff
def radialFlatBumpReal (d : ℕ) (x : Euclidean d) : ℝ :=
  expNegInvGlue (1 - 4 * ‖x‖ ^ 2)
def radialFlatBumpFun (d : ℕ) (x : Euclidean d) : ℂ :=
  (radialFlatBumpReal d x : ℂ)
theorem radialFlatBumpReal_nonneg (d : ℕ) (x : Euclidean d) :
    0 ≤ radialFlatBumpReal d x :=
  expNegInvGlue.nonneg _
theorem radialFlatBumpReal_zero_pos (d : ℕ) :
    0 < radialFlatBumpReal d (0 : Euclidean d) := by
  unfold radialFlatBumpReal
  simpa using! expNegInvGlue.pos_of_pos (by norm_num : (0 : ℝ) < 1)
theorem support_radialFlatBumpReal (d : ℕ) :
    Function.support (radialFlatBumpReal d) =
      Metric.ball (0 : Euclidean d) (1 / 2 : ℝ) := by
  ext x
  simp only [Function.mem_support, radialFlatBumpReal,
    Metric.mem_ball, dist_zero_right]
  constructor
  · intro hx
    have hpos : 0 < 1 - 4 * ‖x‖ ^ 2 := by
      exact lt_of_not_ge (fun h => hx (expNegInvGlue.zero_of_nonpos h))
    nlinarith [norm_nonneg x]
  · intro hx
    have hpos : 0 < 1 - 4 * ‖x‖ ^ 2 := by
      nlinarith [norm_nonneg x]
    exact (expNegInvGlue.pos_of_pos hpos).ne'
theorem support_radialFlatBumpFun (d : ℕ) :
    Function.support (radialFlatBumpFun d) =
      Metric.ball (0 : Euclidean d) (1 / 2 : ℝ) := by
  rw [← support_radialFlatBumpReal d]
  ext x
  simp [radialFlatBumpFun]
theorem radialFlatBumpFun_contDiff (d : ℕ) :
    ContDiff ℝ ∞ (radialFlatBumpFun d) := by
  change ContDiff ℝ ∞
    (fun x : Euclidean d =>
      Complex.ofRealCLM (expNegInvGlue (1 - 4 * ‖x‖ ^ 2)))
  exact Complex.ofRealCLM.contDiff.comp
    (expNegInvGlue.contDiff.comp
      (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ))))
theorem radialFlatBumpFun_hasCompactSupport (d : ℕ) :
    HasCompactSupport (radialFlatBumpFun d) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Euclidean d) (1 / 2 : ℝ))
  rw [support_radialFlatBumpFun]
  exact Metric.ball_subset_closedBall
def radialFlatBump (d : ℕ) : TestFunction d :=
  (radialFlatBumpFun_hasCompactSupport d).toSchwartzMap
    (radialFlatBumpFun_contDiff d)
@[simp] theorem radialFlatBump_apply (d : ℕ) (x : Euclidean d) :
    radialFlatBump d x = (radialFlatBumpReal d x : ℂ) := by
  rfl
theorem radialFlatBump_real (d : ℕ) : IsRealValued (radialFlatBump d) := by
  intro x
  simp
theorem radialFlatBump_radial (d : ℕ) : IsRadial (radialFlatBump d) := by
  intro x y hxy
  simp [radialFlatBumpReal, hxy]
theorem integral_radialFlatBumpReal_pos (d : ℕ) :
    0 < ∫ x : Euclidean d, radialFlatBumpReal d x := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (show Continuous (radialFlatBumpReal d) by
      unfold radialFlatBumpReal
      fun_prop)
  · have hcomplex :
        Integrable (radialFlatBump d : Euclidean d → ℂ) :=
      (radialFlatBump d).integrable
    simpa using! hcomplex.re
  · exact radialFlatBumpReal_nonneg d
  · exact (radialFlatBumpReal_zero_pos d).ne'
theorem IsRadial.fourier {d : ℕ} {f : TestFunction d}
    (hf : IsRadial f) : IsRadial (𝓕 f : TestFunction d) := by
  intro x y hxy
  let A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d :=
    Submodule.reflection (ℝ ∙ (x - y))ᗮ
  have hA : A x = y := Submodule.reflection_sub hxy
  have hcomp : (f : Euclidean d → ℂ) ∘ A = f := by
    funext z
    exact hf (A z) z (A.norm_map z)
  change (𝓕 (f : Euclidean d → ℂ)) x =
    (𝓕 (f : Euclidean d → ℂ)) y
  calc
    (𝓕 (f : Euclidean d → ℂ)) x =
        (𝓕 ((f : Euclidean d → ℂ) ∘ A)) x := by rw [hcomp]
    _ = (𝓕 (f : Euclidean d → ℂ)) (A x) :=
      Real.fourier_comp_linearIsometry A (f : Euclidean d → ℂ) x
    _ = (𝓕 (f : Euclidean d → ℂ)) y := by rw [hA]
theorem fourier_conj_apply_of_real {d : ℕ} (f : TestFunction d)
    (hf : IsRealValued f) (ξ : Euclidean d) :
    starRingEnd ℂ ((𝓕 f : TestFunction d) ξ) =
      ((𝓕 f : TestFunction d) (-ξ)) := by
  change starRingEnd ℂ ((𝓕 (f : Euclidean d → ℂ)) ξ) =
    (𝓕 (f : Euclidean d → ℂ)) (-ξ)
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  have hreal : starRingEnd ℂ (f x) = f x :=
    Complex.conj_eq_iff_im.mpr (hf x)
  have htwo : starRingEnd ℂ (2 : ℂ) = 2 := Complex.conj_ofNat 2
  simp [smul_eq_mul, map_mul, ← Complex.exp_conj, hreal, htwo]
theorem IsRealValued.fourier_of_radial {d : ℕ} {f : TestFunction d}
    (hf : IsRealValued f) (hrad : IsRadial f) :
    IsRealValued (𝓕 f : TestFunction d) := by
  intro ξ
  apply Complex.conj_eq_iff_im.mp
  rw [fourier_conj_apply_of_real f hf]
  exact hrad.fourier (-ξ) ξ (by simp)
def radialAutocorrelation (d : ℕ) : TestFunction d :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (radialFlatBump d) (radialFlatBump d)
theorem fourier_radialAutocorrelation_apply (d : ℕ) (ξ : Euclidean d) :
    ((𝓕 (radialAutocorrelation d) : TestFunction d) ξ) =
      ((𝓕 (radialFlatBump d) : TestFunction d) ξ) ^ 2 := by
  unfold radialAutocorrelation
  rw [SchwartzMap.fourier_convolution]
  simp [pow_two]
theorem fourier_radialFlatBump_real (d : ℕ) :
    IsRealValued (𝓕 (radialFlatBump d) : TestFunction d) :=
  (radialFlatBump_real d).fourier_of_radial (radialFlatBump_radial d)
theorem fourier_radialAutocorrelation_real (d : ℕ) :
    IsRealValued (𝓕 (radialAutocorrelation d) : TestFunction d) := by
  intro ξ
  rw [fourier_radialAutocorrelation_apply]
  simp [pow_two, Complex.mul_im, fourier_radialFlatBump_real d ξ]
theorem fourier_radialAutocorrelation_nonneg (d : ℕ) (ξ : Euclidean d) :
    0 ≤ ((𝓕 (radialAutocorrelation d) : TestFunction d) ξ).re := by
  rw [fourier_radialAutocorrelation_apply]
  simp only [pow_two, Complex.mul_re, fourier_radialFlatBump_real d ξ,
    mul_zero, sub_zero]
  exact mul_self_nonneg _
theorem fourier_radialFlatBump_zero (d : ℕ) :
    ((𝓕 (radialFlatBump d) : TestFunction d) (0 : Euclidean d)) =
      (↑(∫ x : Euclidean d, radialFlatBumpReal d x) : ℂ) := by
  change (𝓕 (radialFlatBump d : Euclidean d → ℂ)) 0 = _
  rw [Real.fourier_eq']
  simpa [radialFlatBump_apply] using!
    (integral_ofReal (𝕜 := ℂ)
      (f := radialFlatBumpReal d)
      (μ := (volume : Measure (Euclidean d))))
theorem fourier_radialAutocorrelation_zero_pos (d : ℕ) :
    0 < ((𝓕 (radialAutocorrelation d) : TestFunction d)
      (0 : Euclidean d)).re := by
  rw [fourier_radialAutocorrelation_apply,
    fourier_radialFlatBump_zero]
  simpa [pow_two, Complex.mul_re] using!
    mul_pos (integral_radialFlatBumpReal_pos d)
      (integral_radialFlatBumpReal_pos d)
theorem support_radialFlatBump (d : ℕ) :
    Function.support (radialFlatBump d : Euclidean d → ℂ) =
      Metric.ball (0 : Euclidean d) (1 / 2 : ℝ) :=
  support_radialFlatBumpFun d
theorem support_radialAutocorrelation_subset (d : ℕ) :
    Function.support (radialAutocorrelation d : Euclidean d → ℂ) ⊆
      Metric.ball (0 : Euclidean d) (1 : ℝ) := by
  have hconv :
      (radialAutocorrelation d : Euclidean d → ℂ) =
        MeasureTheory.convolution
          (radialFlatBump d : Euclidean d → ℂ)
          (radialFlatBump d : Euclidean d → ℂ)
          (ContinuousLinearMap.mul ℂ ℂ) volume := by
    funext x
    exact SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ)
      (radialFlatBump d) (radialFlatBump d) x
  rw [hconv]
  calc
    Function.support
        (MeasureTheory.convolution
          (radialFlatBump d : Euclidean d → ℂ)
          (radialFlatBump d : Euclidean d → ℂ)
          (ContinuousLinearMap.mul ℂ ℂ) volume) ⊆
        Function.support (radialFlatBump d : Euclidean d → ℂ) +
          Function.support (radialFlatBump d : Euclidean d → ℂ) :=
      MeasureTheory.support_convolution_subset
        (ContinuousLinearMap.mul ℂ ℂ)
    _ = Metric.ball (0 : Euclidean d) (1 : ℝ) := by
      rw [support_radialFlatBump]
      rw [ball_add_ball (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (0 : ℝ) < 1 / 2)]
      norm_num
theorem radialAutocorrelation_outside_eq_zero (d : ℕ)
    (x : Euclidean d) (hx : 1 ≤ ‖x‖) :
    radialAutocorrelation d x = 0 := by
  by_contra hne
  have hsupport : x ∈ Function.support
      (radialAutocorrelation d : Euclidean d → ℂ) := hne
  have hball := support_radialAutocorrelation_subset d hsupport
  have hnorm : ‖x‖ < (1 : ℝ) := by
    simpa [Metric.mem_ball, dist_zero_right] using! hball
  linarith
theorem radialAutocorrelation_real (d : ℕ) :
    IsRealValued (radialAutocorrelation d) := by
  intro x
  rw [radialAutocorrelation, SchwartzMap.convolution_apply,
    MeasureTheory.convolution_def]
  change
    (∫ t : Euclidean d,
      (radialFlatBumpReal d t : ℂ) *
        (radialFlatBumpReal d (x - t) : ℂ)).im = 0
  simp_rw [← Complex.ofReal_mul]
  have hreal :
      (∫ t : Euclidean d,
        (↑(radialFlatBumpReal d t *
          radialFlatBumpReal d (x - t)) : ℂ)) =
        (↑(∫ t : Euclidean d,
          radialFlatBumpReal d t * radialFlatBumpReal d (x - t)) : ℂ) :=
    integral_ofReal (𝕜 := ℂ)
  rw [hreal]
  simp
theorem fourier_radialAutocorrelation_radial (d : ℕ) :
    IsRadial (𝓕 (radialAutocorrelation d) : TestFunction d) := by
  intro x y hxy
  rw [fourier_radialAutocorrelation_apply,
    fourier_radialAutocorrelation_apply]
  rw [(radialFlatBump_radial d).fourier x y hxy]
theorem radialAutocorrelation_radial (d : ℕ) :
    IsRadial (radialAutocorrelation d) := by
  intro x y hxy
  have h := (fourier_radialAutocorrelation_radial d).fourier
    (-x) (-y) (by simpa using! hxy)
  simpa [fourier_sq_apply] using! h
def autocorrelationAdmissible (d : ℕ) : Admissible d where
  function := radialAutocorrelation d
  real := radialAutocorrelation_real d
  radial := radialAutocorrelation_radial d
  fourier_real := fourier_radialAutocorrelation_real d
  fourier_nonneg := fourier_radialAutocorrelation_nonneg d
  fourier_zero_pos := fourier_radialAutocorrelation_zero_pos d
  outside_nonpos := by
    intro x hx
    rw [radialAutocorrelation_outside_eq_zero d x hx]
    simp
end
noncomputable section
end
noncomputable section
open Filter
open scoped Topology
def SharpBinaryLogAsymptotic : Prop :=
  Tendsto
    (fun d : ℕ => Real.logb 2 (linearProgram d) / (d : ℝ))
    atTop (nhds (-criticalBinaryExponent))
theorem saddleSourceSchwartzRealization :
    SaddleSourceSchwartzRealization := by
  intro ε hε horder d hd
  refine ⟨minusSaddleSchwartz hε hd horder,
    plusSaddleSchwartz hε hd horder, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl
noncomputable def saddleOrderedUpperConstruction_of_sourceSigns
    (hsigns : SaddleSourceEventualSigns) :
    OrderedEpsilonUpperConstruction :=
  saddleOrderedUpperConstruction
    saddleSourceSchwartzRealization hsigns
end
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology
end
noncomputable section
open Filter
open scoped Topology
def manuscriptQuotientRootSet (d : ℕ) : Set ℝ :=
  Set.range fun f : Admissible d => quotient f ^ ((d : ℝ)⁻¹)
def manuscriptNormalizedQuotientInfRoot (d : ℕ) : ℝ :=
  (sInf (quotientSet d)) ^ ((d : ℝ)⁻¹) / Real.sqrt (d : ℝ)
def manuscriptPackingDeficit (d : ℕ) : ℝ :=
  max 0 (criticalPackingBase - (linearProgram d) ^ ((d : ℝ)⁻¹))
def manuscriptPackingRootError (d : ℕ) : ℝ :=
  (linearProgram d) ^ ((d : ℝ)⁻¹) - criticalPackingBase
def manuscriptBinaryExponentError (d : ℕ) : ℝ :=
  -(Real.logb 2 (linearProgram d) / (d : ℝ)) -
    criticalBinaryExponent
def manuscriptQuotientRootError (d : ℕ) : ℝ :=
  normalizedProgram d - criticalRadius
end
end CohnElkies
section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
section
open Metric MeasureTheory
variable {r : ℝ} {ι : Type*} [Fintype ι]
theorem EuclideanSpace.euclidean_ball_volume_positive [Nonempty ι] (x : EuclideanSpace ℝ ι) (hr : 0 < r) :
    0 < volume (ball x r) := by
  simpa using! measure_ball_pos (μ := volume) x hr
open Classical in

theorem EuclideanSpace.euclidean_ball_volume_finite
    [NullSingletonClass (volume : Measure (EuclideanSpace ℝ ι))]
    (x : EuclideanSpace ℝ ι) :
    volume (ball x r) < ⊤ := by
  simpa using! measure_ball_lt_top (μ := volume) (x := x) (r := r)
end
section
open MeasureTheory Metric Filter
open Module
open scoped BigOperators ENNReal Pointwise
instance CohnElkies.numeralTwoAtLeast : Nat.AtLeastTwo 2 := ⟨by decide⟩
instance CohnElkies.euclideanFiniteDimensional (d : ℕ) :
    FiniteDimensional ℝ (EuclideanSpace ℝ (Fin d)) := by
  infer_instance
instance CohnElkies.euclideanBorelSpace (d : ℕ) :
    BorelSpace (EuclideanSpace ℝ (Fin d)) := by
  infer_instance
section Definitions
structure SpherePacking (d : ℕ) where
  centers : Set (EuclideanSpace ℝ (Fin d))
  separation : ℝ
  separation_pos : 0 < separation := by positivity
  centers_dist : Pairwise (separation ≤ dist · · : centers → centers → Prop)
structure PeriodicSpherePacking (d : ℕ) extends SpherePacking d where
  lattice : Submodule ℤ (EuclideanSpace ℝ (Fin d))
  lattice_action : ∀ ⦃x y⦄, x ∈ lattice → y ∈ centers → x + y ∈ centers
  lattice_discrete : DiscreteTopology lattice := by infer_instance
  lattice_isZLattice : IsZLattice ℝ lattice := by infer_instance
variable {d : ℕ}
attribute [instance] PeriodicSpherePacking.lattice_discrete
attribute [instance] PeriodicSpherePacking.lattice_isZLattice
theorem SpherePacking.distinct_centers_separation_bound (S : SpherePacking d) (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ S.centers) (hy : y ∈ S.centers) (hxy : x ≠ y) :
    S.separation ≤ dist x y := by
  simpa using!
    S.centers_dist (Subtype.coe_ne_coe.mp (by simpa using! hxy) : (⟨x, hx⟩ : S.centers) ≠ ⟨y, hy⟩)
instance PeriodicSpherePacking.instDiscretePackingLattice (S : PeriodicSpherePacking d) :
    DiscreteTopology S.lattice :=
  S.lattice_discrete
instance PeriodicSpherePacking.instFullRankPackingLattice (S : PeriodicSpherePacking d) :
    IsZLattice ℝ S.lattice :=
  S.lattice_isZLattice
instance SpherePacking.instDiscretePackingCenters (S : SpherePacking d) :
    DiscreteTopology S.centers :=
  DiscreteTopology.of_forall_le_dist S.separation_pos S.centers_dist
noncomputable instance PeriodicSpherePacking.latticeCenterTranslationAction (S : PeriodicSpherePacking d) :
    AddAction S.lattice S.centers := by
  refine
    { vadd := fun x y => ⟨(x : EuclideanSpace ℝ (Fin d)) + y,
        S.lattice_action x.property y.property⟩
      zero_vadd := ?_
      add_vadd := ?_ }
  · intro x y z
    apply Subtype.ext
    exact add_assoc (x : EuclideanSpace ℝ (Fin d)) y z
  · intro y
    apply Subtype.ext
    exact zero_add (y : EuclideanSpace ℝ (Fin d))
@[reducible] def SpherePacking.occupiedBallRegion (S : SpherePacking d) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ x : S.centers, ball (x : EuclideanSpace ℝ (Fin d)) (S.separation / 2)
noncomputable def SpherePacking.densityInsideRadius (S : SpherePacking d) (R : ℝ) :
    ℝ≥0∞ :=
  volume (S.occupiedBallRegion ∩ ball 0 R) / (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R))
noncomputable def SpherePacking.upperPackingDensity (S : SpherePacking d) : ℝ≥0∞ :=
  limsup S.densityInsideRadius atTop
theorem PeriodicSpherePacking.integral_basis_spans_packing_lattice
    (S : PeriodicSpherePacking d) {ι : Type*} (b : Basis ι ℤ S.lattice) :
    Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) = S.lattice :=
  Basis.ofZLatticeBasis_span ℝ S.lattice b
theorem PeriodicSpherePacking.mem_integral_basis_span_iff
    (S : PeriodicSpherePacking d) {ι : Type*} (b : Basis ι ℤ S.lattice) (v) :
    v ∈ Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) ↔ v ∈ S.lattice :=
  SetLike.ext_iff.mp (S.integral_basis_spans_packing_lattice b) v
end Definitions
section Scaling
variable {d : ℕ}
open Real
def SpherePacking.rescaleConfiguration (S : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    SpherePacking d := by
  refine
    { centers := (fun x : EuclideanSpace ℝ (Fin d) => c • x) '' S.centers
      separation := c * S.separation
      separation_pos := mul_pos hc S.separation_pos
      centers_dist := ?_ }
  rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, hy, rfl⟩⟩ hxy
  have hne : x ≠ y := by
    intro h
    apply hxy
    subst y
    rfl
  have hdist := S.distinct_centers_separation_bound x y hx hy hne
  change c * S.separation ≤ dist (c • x) (c • y)
  simpa [dist_smul₀, abs_of_pos hc] using
    mul_le_mul_of_nonneg_left hdist hc.le
noncomputable def PeriodicSpherePacking.rescaleConfiguration (S : PeriodicSpherePacking d) {c : ℝ}
    (hc : 0 < c) :
    PeriodicSpherePacking d := by
  let scale : EuclideanSpace ℝ (Fin d) →ₗ[ℤ] EuclideanSpace ℝ (Fin d) :=
    (LinearMap.lsmul ℝ (EuclideanSpace ℝ (Fin d)) c).restrictScalars ℤ
  let scaledLattice : Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
    S.lattice.map scale
  let latticeEquiv : S.lattice ≃ scaledLattice :=
    { toFun := fun x => ⟨c • (x : EuclideanSpace ℝ (Fin d)),
        ⟨x, x.property, rfl⟩⟩
      invFun := fun y => ⟨c⁻¹ • (y : EuclideanSpace ℝ (Fin d)), by
        obtain ⟨x, hx, hxy⟩ := y.property
        change c • x = (y : EuclideanSpace ℝ (Fin d)) at hxy
        rw [← hxy]
        simpa [smul_smul, hc.ne'] using hx⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp [smul_smul, hc.ne']
      right_inv := by
        intro y
        apply Subtype.ext
        simp [smul_smul, hc.ne'] }
  let latticeHomeomorph : S.lattice ≃ₜ scaledLattice :=
    { latticeEquiv with
      continuous_toFun := by
        change Continuous (fun x : S.lattice =>
          (⟨c • (x : EuclideanSpace ℝ (Fin d)), _⟩ : scaledLattice))
        fun_prop
      continuous_invFun := by
        change Continuous (fun y : scaledLattice =>
          (⟨c⁻¹ • (y : EuclideanSpace ℝ (Fin d)), _⟩ : S.lattice))
        fun_prop }
  letI : DiscreteTopology scaledLattice := latticeHomeomorph.discreteTopology
  have scaled_span_top :
      Submodule.span ℝ (scaledLattice : Set (EuclideanSpace ℝ (Fin d))) = ⊤ := by
    have all_scaled_mem : ∀ x : EuclideanSpace ℝ (Fin d),
        c • x ∈ Submodule.span ℝ
          (scaledLattice : Set (EuclideanSpace ℝ (Fin d))) := by
      intro x
      have hx : x ∈ Submodule.span ℝ
          (S.lattice : Set (EuclideanSpace ℝ (Fin d))) := by
        rw [S.lattice_isZLattice.span_top]
        exact Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx =>
          apply Submodule.subset_span
          exact ⟨x, hx, rfl⟩
      | zero =>
          simp
      | add x y hx hy ihx ihy =>
          simpa [smul_add] using
            (Submodule.add_mem (Submodule.span ℝ
              (scaledLattice : Set (EuclideanSpace ℝ (Fin d)))) ihx ihy)
      | smul a x hx ih =>
          rw [smul_comm c a]
          exact Submodule.smul_mem (Submodule.span ℝ
            (scaledLattice : Set (EuclideanSpace ℝ (Fin d)))) a ih
    apply top_unique
    intro x _
    simpa [smul_smul, hc.ne'] using all_scaled_mem (c⁻¹ • x)
  letI : IsZLattice ℝ scaledLattice := ⟨scaled_span_top⟩
  refine
    { toSpherePacking := S.toSpherePacking.rescaleConfiguration hc
      lattice := scaledLattice
      lattice_action := ?_
      lattice_discrete := inferInstance
      lattice_isZLattice := inferInstance }
  rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  refine ⟨x + y, S.lattice_action hx hy, ?_⟩
  change c • (x + y) = c • x + c • y
  exact smul_add c x y
lemma SpherePacking.rescale_occupied_region {S : SpherePacking d} {c : ℝ} (hc : 0 < c) :
    (S.rescaleConfiguration hc).occupiedBallRegion = c • S.occupiedBallRegion := by
  have hc0 : (c : ℝ) ≠ 0 := hc.ne'
  ext x
  simp [SpherePacking.occupiedBallRegion, SpherePacking.rescaleConfiguration, Set.smul_set_iUnion, Set.mem_smul_set,
    _root_.smul_ball hc0, Real.norm_eq_abs, abs_of_pos hc, mul_div_assoc]
end Scaling
noncomputable section Density
variable {d : ℕ} (S : SpherePacking d)
def PeriodicSpherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ S : PeriodicSpherePacking d, S.upperPackingDensity
def SpherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ S : SpherePacking d, S.upperPackingDensity
end Density
section DensityLemmas
namespace SpherePacking
@[simp]
lemma rescale_local_packing_density {d : ℕ} (S : SpherePacking d) {c : ℝ} (hc : 0 < c)
    (R : ℝ) :
    (S.rescaleConfiguration hc).densityInsideRadius (c * R) = S.densityInsideRadius R := by
  have hball : ball (0 : EuclideanSpace ℝ (Fin d)) (c * R) = c • ball 0 R := by
    simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos hc] using!
      (smul_ball hc.ne.symm (0 : EuclideanSpace ℝ (Fin d)) R).symm
  rw [densityInsideRadius, rescale_occupied_region, hball, ← Set.smul_set_inter₀ hc.ne.symm]
  rw [Measure.addHaar_smul_of_nonneg _ hc.le,
    Measure.addHaar_smul_of_nonneg _ hc.le]
  rw [ENNReal.mul_div_mul_left, densityInsideRadius]
  · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le, finrank_euclideanSpace_fin]
    positivity
  · apply ENNReal.ofReal_ne_top
@[simp]
lemma rescale_local_packing_density_radius {d : ℕ} (S : SpherePacking d) {c : ℝ} (hc : 0 < c)
    (R : ℝ) :
    (S.rescaleConfiguration hc).densityInsideRadius R = S.densityInsideRadius (R / c) := by
  simpa [mul_div_assoc', hc.ne.symm] using! (rescale_local_packing_density (S := S) hc (R := R / c))
end DensityLemmas.SpherePacking
section BasicResults
open scoped ENNReal
open EuclideanSpace
variable {d : ℕ} (S : SpherePacking d)
lemma nearby_ball_union_subset_clipped_union
    (X : Set (EuclideanSpace ℝ (Fin d))) (r R : ℝ) :
    ⋃ x ∈ X ∩ ball 0 R, ball x r ⊆ (⋃ x ∈ X, ball x r) ∩ ball 0 (R + r) := by
  intro x hx
  simp only [Set.mem_inter_iff, Set.mem_iUnion, mem_ball, exists_prop, dist_zero_right] at hx ⊢
  obtain ⟨y, ⟨hy₁, hy₂⟩⟩ := hx
  use ⟨y, ⟨hy₁.left, hy₂⟩⟩
  exact lt_of_le_of_lt (norm_le_norm_add_norm_sub' x y) (by gcongr <;> tauto)
lemma clipped_ball_union_subset_nearby_union
    (X : Set (EuclideanSpace ℝ (Fin d))) (r R : ℝ) :
    (⋃ x ∈ X, ball x r) ∩ ball 0 (R - r) ⊆ ⋃ x ∈ X ∩ ball 0 R, ball x r := by
  intro x hx
  simp only [Set.mem_inter_iff, Set.mem_iUnion, mem_ball, exists_prop, dist_zero_right] at hx ⊢
  obtain ⟨⟨y, ⟨hy₁, hy₂⟩⟩, hx⟩ := hx
  use y, ⟨hy₁, ?_⟩, hy₂
  refine lt_of_le_of_lt (norm_le_norm_add_norm_sub x y) ?_
  rw [← sub_add_cancel R r]
  exact add_lt_add hx (by simpa [dist_eq_norm, norm_sub_rev] using! hy₂)
theorem SpherePacking.volume_center_ball_union_eq_tsum
    (R : ℝ) {r' : ℝ} (hr' : r' ≤ S.separation / 2) :
    volume (⋃ x : ↑(S.centers ∩ ball 0 R), ball (x : EuclideanSpace ℝ (Fin d)) r')
      = ∑' x : ↑(S.centers ∩ ball 0 R), volume (ball (x : EuclideanSpace ℝ (Fin d)) r') := by
  have : Countable ↑(S.centers ∩ ball 0 R) :=
    Set.Countable.mono Set.inter_subset_left (countable_of_Lindelof_of_discrete (X := S.centers))
  apply measure_iUnion ?_ (fun _ ↦ measurableSet_ball)
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  apply ball_disjoint_ball
  simp_rw [ne_eq, Subtype.mk.injEq] at h ⊢
  linarith [S.distinct_centers_separation_bound x y hx.left hy.left h]
theorem SpherePacking.center_count_in_ball_upper_bound (hd : 0 < d) (R : ℝ) :
    (S.centers ∩ ball 0 R).encard ≤
      volume (S.occupiedBallRegion ∩ ball 0 (R + S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  have h := volume.mono <|
    nearby_ball_union_subset_clipped_union S.centers (S.separation / 2) R
  change volume _ ≤ volume _ at h
  simp_rw [Set.biUnion_eq_iUnion, S.volume_center_ball_union_eq_tsum R (le_refl _),
    Measure.addHaar_ball_center, ENNReal.tsum_set_const] at h
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rwa [← ENNReal.le_div_iff_mul_le] at h <;> left
  · exact (euclidean_ball_volume_positive _ (by linarith [S.separation_pos])).ne.symm
  · exact (euclidean_ball_volume_finite _).ne
theorem SpherePacking.center_count_in_ball_lower_bound (R : ℝ) :
    (S.centers ∩ ball 0 R).encard ≥
      volume (S.occupiedBallRegion ∩ ball 0 (R - S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  have h := volume.mono <|
    clipped_ball_union_subset_nearby_union S.centers (S.separation / 2) R
  change volume _ ≤ volume _ at h
  simp_rw [Set.biUnion_eq_iUnion, S.volume_center_ball_union_eq_tsum _ (le_refl _),
    Measure.addHaar_ball_center, ENNReal.tsum_set_const] at h
  exact ENNReal.div_le_of_le_mul h
theorem SpherePacking.finite_centers_inside_ball (R : ℝ) :
    Finite ↑(S.centers ∩ ball 0 R) := by
  apply Set.encard_lt_top_iff.mp
  rcases eq_or_ne d 0 with rfl | hd
  · exact Set.encard_lt_top_iff.2 <| Set.Finite.of_subsingleton (S.centers ∩ ball 0 R)
  · have hd' : 0 < d := Nat.pos_of_ne_zero hd
    haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd'
    apply ENat.toENNReal_lt.mp
    refine lt_of_le_of_lt (S.center_count_in_ball_upper_bound hd' R) ?_
    refine ENNReal.div_lt_top
      (ne_of_lt <|
        lt_of_le_of_lt (volume.mono Set.inter_subset_right) (EuclideanSpace.euclidean_ball_volume_finite _))
      (euclidean_ball_volume_positive _ (by linarith [S.separation_pos])).ne.symm
theorem SpherePacking.local_density_lower_bound (hd : 0 < d) (R : ℝ) :
    S.densityInsideRadius R
      ≥ (S.centers ∩ ball 0 (R - S.separation / 2)).encard
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [densityInsideRadius, occupiedBallRegion]
  apply ENNReal.div_le_div_right
  exact (ENNReal.le_div_iff_mul_le
    (Or.inl (euclidean_ball_volume_positive _ (by linarith [S.separation_pos])).ne.symm)
    (Or.inl (euclidean_ball_volume_finite _).ne)).1 <|
      (by simpa [sub_add_cancel] using! (S.center_count_in_ball_upper_bound hd (R - S.separation / 2)))
theorem SpherePacking.local_density_upper_bound (hd : 0 < d) (R : ℝ) :
    S.densityInsideRadius R
      ≤ (S.centers ∩ ball 0 (R + S.separation / 2)).encard
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [densityInsideRadius, occupiedBallRegion]
  apply ENNReal.div_le_div_right
  exact (ENNReal.div_le_iff_le_mul
    (Or.inl (euclidean_ball_volume_positive _ (by linarith [S.separation_pos])).ne.symm)
    (Or.inl (euclidean_ball_volume_finite _).ne)).1 <|
      (by simpa [add_sub_cancel_right] using! (S.center_count_in_ball_lower_bound (R + S.separation / 2)))
end BasicResults
end
section
theorem ENat.tsum_constant_eq_card_mul {α : Type*} (c : ENat) :
    ∑' (_ : α), c = ENat.card α * c := by
  classical
  by_cases hα : Finite α
  · letI := Fintype.ofFinite α
    simp [tsum_fintype, ENat.card_eq_coe_fintype_card, nsmul_eq_mul]
  · letI := not_finite_iff_infinite.mp hα
    by_cases hc : c = 0
    · simp [hc]
    · rw [ENat.card_eq_top_of_infinite, ENat.top_mul hc]
      apply HasSum.tsum_eq
      change Filter.Tendsto (fun s : Finset α => ∑ i ∈ s, c)
        Filter.atTop (nhds (⊤ : ENat))
      apply tendsto_order.2
      constructor
      · intro b hb
        have hbtop : b ≠ ⊤ := ne_of_lt hb
        obtain ⟨s, hs⟩ := Finset.exists_card_eq (α := α) (b.toNat + 1)
        apply Filter.eventually_atTop.2
        refine ⟨s, ?_⟩
        intro t hst
        have hcard : s.card ≤ t.card := Finset.card_le_card hst
        have hbc : b < (s.card : ENat) := by
          rw [← ENat.coe_toNat hbtop, hs]
          exact_mod_cast Nat.lt_succ_self b.toNat
        have hc_one : (1 : ENat) ≤ c := Order.one_le_iff_ne_zero.2 hc
        calc
          b < (s.card : ENat) := hbc
          _ ≤ (t.card : ENat) := by exact_mod_cast hcard
          _ ≤ (t.card : ENat) * c := by
            simpa using (mul_le_mul_right hc_one (t.card : ENat))
          _ = ∑ i ∈ t, c := by
            simp [nsmul_eq_mul]
      · intro b hb
        exact (not_lt_of_ge le_top hb).elim
theorem ENat.tsum_subtype_constant_eq_encard_mul {α : Type*} (s : Set α) (c : ENat) :
    ∑' (_ : s), c = s.encard * c := by
  rw [ENat.tsum_constant_eq_card_mul, Set.encard]
theorem ENat.tsum_unit_eq_cardinality {α : Type*} : ∑' (_ : α), 1 = ENat.card α := by
  simp [ENat.tsum_constant_eq_card_mul]
theorem ENat.tsum_subtype_unit_eq_encard {α : Type*} (s : Set α) : ∑' (_ : s), 1 = s.encard := by
  rw [ENat.tsum_unit_eq_cardinality, Set.encard]
end
section
namespace ENat
open Function Set
section tsum
variable {ι : Sort*} {α β : Type*} {f g : α → ℕ∞} {s t : Set α}
protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset
@[simp] protected theorem summable : Summable f :=
  ENat.hasSum.summable
protected theorem tsum_reindex_injective_le {φ : α → β} (hφ : Injective φ) (g : β → ℕ∞) :
    ∑' x, g (φ x) ≤ ∑' y, g y :=
  (ENat.summable (f := fun x => g (φ x))).tsum_le_tsum_of_inj φ hφ (fun _ _ ↦ bot_le)
    (fun _ ↦ le_rfl) (ENat.summable (f := g))
protected theorem tsum_le_reindex_surjection {φ : α → β} (hφ : Surjective φ) (g : β → ℕ∞) :
    ∑' y, g y ≤ ∑' x, g (φ x) :=
  calc ∑' y, g y = ∑' y, g (φ (surjInv hφ y)) := by simp [surjInv_eq hφ]
    _ ≤ ∑' x, g (φ x) :=
      ENat.tsum_reindex_injective_le (injective_surjInv hφ) _
protected theorem tsum_reindex_bijection {φ : α → β} (hφ : φ.Bijective) (g : β → ℕ∞) :
    ∑' x, g (φ x) = ∑' y, g y :=
  (ENat.tsum_reindex_injective_le hφ.injective g).antisymm
    (ENat.tsum_le_reindex_surjection hφ.surjective g)
protected theorem tsum_dependent_subtype_reindex {β : α → Type*} (f : (Σ a, β a) → ℕ∞) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  Summable.tsum_sigma' (fun _ ↦ ENat.summable) ENat.summable
variable {ι : Type*}
theorem tsum_disjoint_subtype_union (f : α → ℕ∞) (t : ι → Set α) (ht : Pairwise (Disjoint on t)) :
    ∑' x : ⋃ i, t i, f x = ∑' i, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i, t i, f x = ∑' x : Σ i, t i, f x.2 :=
    (ENat.tsum_reindex_bijection
      (sigmaToiUnion_bijective t (fun _ _ hij ↦ ht hij)) _).symm
    _ = _ := ENat.tsum_dependent_subtype_reindex _
end ENat.tsum
open Function
theorem Set.encard_disjoint_union_eq_tsum {ι α : Type*} {s : ι → Set α}
    (hs : Set.PairwiseDisjoint Set.univ s) : (⋃ i, s i).encard = ∑' i, (s i).encard := by
  simpa [ENat.tsum_subtype_unit_eq_encard] using!
    (ENat.tsum_disjoint_subtype_union (f := fun _ : α => (1 : ℕ∞)) (t := s) (by
      simpa [Set.PairwiseDisjoint, Set.pairwise_univ] using! hs))
end
section
open ZSpan
variable {E ι K : Type*} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [NormedAddCommGroup E] [NormedSpace K E] (b : Module.Basis ι K E) [FloorRing K] [Fintype ι]
section BasisIndexEquiv
variable {d : ℕ}
namespace ZLattice
noncomputable def coordinateIndexEquiv (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    (Module.Free.ChooseBasisIndex ℤ Λ) ≃ (Fin d) := by
  let c := EuclideanSpace.equiv (Fin d) ℝ
  let e := c.toLinearEquiv.restrictScalars ℤ
  let L : Submodule ℤ (Fin d → ℝ) := Λ.map e.toLinearMap
  have hmem (x : EuclideanSpace ℝ (Fin d)) : x ∈ Λ ↔ e x ∈ L := by
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      exact e.injective he ▸ hy
  let h : Λ ≃ₜ L := c.toHomeomorph.subtype (by simpa [e] using hmem)
  letI : DiscreteTopology L := h.discreteTopology
  have hset : (L : Set (Fin d → ℝ)) =
      c.toLinearEquiv.toLinearMap '' (Λ : Set (EuclideanSpace ℝ (Fin d))) := by
    ext x
    change (∃ y, y ∈ Λ ∧ e y = x) ↔
      ∃ y, y ∈ Λ ∧ c.toLinearEquiv.toLinearMap y = x
    simp [e]
  letI : IsZLattice ℝ L := ⟨by
    calc
      Submodule.span ℝ (L : Set (Fin d → ℝ)) =
          Submodule.map c.toLinearEquiv.toLinearMap
            (Submodule.span ℝ (Λ : Set (EuclideanSpace ℝ (Fin d)))) := by
              rw [Submodule.map_span]
              rw [hset]
      _ = Submodule.map c.toLinearEquiv.toLinearMap ⊤ := by
            rw [IsZLattice.span_top]
      _ = ⊤ := Submodule.map_eq_top_iff.mpr rfl⟩
  exact (Module.Free.chooseBasis ℤ Λ).indexEquiv
    ((IsZLattice.basis L).map (e.submoduleMap Λ).symm)
end ZLattice
end BasisIndexEquiv
end
section
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
section aux_lemmas
variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))
lemma bounded_union_of_center_balls (hD_isBounded : IsBounded D) :
    IsBounded (⋃ x ∈ S.centers ∩ D, ball x (S.separation / 2)) := by
  rcases (isBounded_iff_forall_norm_le).1 hD_isBounded with ⟨L, hL⟩
  refine (isBounded_iff_forall_norm_le).2 ⟨L + S.separation / 2, ?_⟩
  intro x hx
  rcases Set.mem_iUnion₂.1 hx with ⟨y, hy, hx⟩
  exact (norm_le_norm_add_norm_sub' x y).trans <|
    add_le_add (hL y hy.2) (le_of_lt (by simpa [mem_ball, dist_eq_norm] using! hx))
lemma pairwise_disjoint_center_balls (D : Set (EuclideanSpace ℝ (Fin d))) :
    Set.PairwiseDisjoint (S.centers ∩ D) (fun x ↦ ball x (S.separation / 2)) := by
  intro x hx y hy hxy
  exact ball_disjoint_ball (by simpa [add_halves] using! S.distinct_centers_separation_bound _ _ hx.left hy.left hxy)
theorem finite_of_bounded_union_with_uniform_volume
    {ι τ : Type*} {s : Set ι} {f : ι → Set (EuclideanSpace ℝ τ)} {c : ℝ≥0∞} (hc : 0 < c)
    [Fintype τ] [NullSingletonClass (volume : Measure (EuclideanSpace ℝ τ))]
    (h_measurable : ∀ x ∈ s, MeasurableSet (f x))
    (h_bounded : IsBounded (⋃ x ∈ s, f x))
    (h_volume : ∀ x ∈ s, c ≤ volume (f x))
    (h_disjoint : s.PairwiseDisjoint f) :
    s.Finite := by
  classical
  have h_finite_volume : volume (⋃ x ∈ s, f x) < ⊤ :=
    h_bounded.measure_lt_top
  by_contra hs
  haveI : Infinite s := Set.infinite_coe_iff.mpr hs
  let e : ℕ ↪ s := Set.Infinite.natEmbedding s hs
  have h_sum :
      volume (⋃ n : ℕ, f (e n : ι)) =
        ∑' n : ℕ, volume (f (e n : ι)) := by
    apply measure_iUnion
    · intro m n hmn
      apply h_disjoint (e m).property (e n).property
      intro heq
      exact hmn (e.injective (Subtype.ext heq))
    · intro n
      exact h_measurable (e n) (e n).property
  have h_top : ∑' n : ℕ, volume (f (e n : ι)) = ⊤ := by
    apply top_unique
    calc
      (⊤ : ENNReal) = ∑' _ : ℕ, c := by
        simp [hc.ne']
      _ ≤ ∑' n : ℕ, volume (f (e n : ι)) :=
        ENNReal.tsum_le_tsum fun n => h_volume (e n) (e n).property
  have h_subset :
      (⋃ n : ℕ, f (e n : ι)) ⊆ ⋃ x ∈ s, f x := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion₂.mpr ⟨e n, (e n).property, hn⟩
  have h_le : (⊤ : ENNReal) ≤ volume (⋃ x ∈ s, f x) := by
    rw [← h_top, ← h_sum]
    exact volume.mono h_subset
  exact (ne_of_lt h_finite_volume) (top_unique h_le)
lemma finite_centers_in_bounded_region (hD_isBounded : IsBounded D) (hd : 0 < d) :
    Finite ↑(S.centers ∩ D) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  refine (Set.finite_coe_iff).2 <| finite_of_bounded_union_with_uniform_volume
      (c := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)))
      (hc := by
        simpa using!
          euclidean_ball_volume_positive (0 : EuclideanSpace ℝ (Fin d)) (by nlinarith [S.separation_pos]))
      (h_measurable := fun _ _ => measurableSet_ball)
      (h_bounded := bounded_union_of_center_balls S D hD_isBounded)
      (h_volume := fun _ _ => by simp [Measure.addHaar_ball_center])
      (h_disjoint := by simpa using! pairwise_disjoint_center_balls S D)
lemma finite_centers_in_fundamental_region {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    (hd : 0 < d) :
    Finite ↑(S.centers ∩ fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  finite_centers_in_bounded_region S _ (ZSpan.fundamentalDomain_isBounded _) hd
open scoped Pointwise in
lemma finite_centers_in_translated_fundamental_region
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (hd : 0 < d) (v : EuclideanSpace ℝ (Fin d)) :
    Finite ↑(S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))) :=
  finite_centers_in_bounded_region S _ ((ZSpan.fundamentalDomain_isBounded _).vadd v) hd
end aux_lemmas
section Pointwise
open scoped Pointwise
variable {d : ℕ}
lemma translates_disjoint_of_unique_cover {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D) {g h : Λ} (hgh : g ≠ h) :
    Disjoint (g +ᵥ D) (h +ᵥ D) := by
  refine Set.disjoint_left.2 (by
    intro x hxg hxh
    exact hgh <| neg_injective <| (hD_unique_covers x).unique
      (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using! hxg)
      (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using! hxh))
end Pointwise
section instances
variable {d : ℕ} (S : PeriodicSpherePacking d)
open scoped Pointwise
noncomputable def PeriodicSpherePacking.centerOrbitEquivFundamentalRegion
    (D : Set (EuclideanSpace ℝ (Fin d))) (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    Quotient S.latticeCenterTranslationAction.orbitRel ≃ ↑(S.centers ∩ D) := by
  classical
  have h_vadd (g : S.lattice) (x : S.centers) :
      ((g +ᵥ x : S.centers) : EuclideanSpace ℝ (Fin d)) =
        (g : EuclideanSpace ℝ (Fin d)) + x := by
    rfl
  let f : ↑(S.centers ∩ D) → Quotient S.latticeCenterTranslationAction.orbitRel :=
    fun x => Quotient.mk _ (⟨x.1, x.2.1⟩ : S.centers)
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).symm
  · intro x y hxy
    obtain ⟨g, hg⟩ := Quotient.exact hxy
    have hco : (g : EuclideanSpace ℝ (Fin d)) + y.1 = x.1 := by
      simpa only [h_vadd] using congrArg Subtype.val hg
    have hgD : (g : EuclideanSpace ℝ (Fin d)) + y.1 ∈ D :=
      hco.symm ▸ x.2.2
    have hgzero : g = 0 :=
      (hD_unique_covers y.1).unique hgD (by simpa using y.2.2)
    apply Subtype.ext
    simpa [hgzero] using hco.symm
  · intro q
    refine Quotient.inductionOn q ?_
    intro x
    obtain ⟨g, hg, -⟩ := hD_unique_covers (x : EuclideanSpace ℝ (Fin d))
    let y : S.centers := g +ᵥ x
    have hyD : (y : EuclideanSpace ℝ (Fin d)) ∈ D := by
      rw [show (y : EuclideanSpace ℝ (Fin d)) =
        (g : EuclideanSpace ℝ (Fin d)) + x from h_vadd g x]
      exact hg
    refine ⟨⟨y, y.property, hyD⟩, ?_⟩
    apply Quotient.sound
    refine ⟨g, ?_⟩
    apply Subtype.ext
    simp [y]
noncomputable def PeriodicSpherePacking.centerOrbitEquivBasisRegion
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) :
    Quotient S.latticeCenterTranslationAction.orbitRel ≃ ↑(S.centers ∩ (fundamentalDomain (b.ofZLatticeBasis ℝ _))) := by
  refine S.centerOrbitEquivFundamentalRegion _ ?_
  intro x
  obtain ⟨v, ⟨hv, hv'⟩⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  use ⟨v.val, ?_⟩, ?_, ?_
  · apply Set.mem_of_subset_of_mem ?_ v.prop
    rw [← Submodule.coe_toAddSubgroup, Basis.ofZLatticeBasis_span]
    rfl
  · simp only at hv' ⊢
    convert! hv using 1
  · intro s hs
    rw [← hv' ⟨s, ?_⟩ hs]
    apply Set.mem_of_subset_of_mem _ s.prop
    rw [← Submodule.coe_toAddSubgroup, Basis.ofZLatticeBasis_span]
    rfl
noncomputable def PeriodicSpherePacking.centerOrbitEquivTranslatedBasisRegion
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    Quotient S.latticeCenterTranslationAction.orbitRel ≃
      ↑(S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))) := by
  refine S.centerOrbitEquivFundamentalRegion _ ?_
  intro x
  obtain ⟨⟨g, hg_lattice⟩, hg, hg'⟩ :=
    exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) (x - v)
  refine ⟨⟨g, ?_⟩, ?_, ?_⟩
  · apply Set.mem_of_subset_of_mem ?_ hg_lattice
    rw [← Submodule.coe_toAddSubgroup, Basis.ofZLatticeBasis_span]
    rfl
  · change g + x ∈ v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _)
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change -v + (g + x) ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _)
    simp only [(Submodule.span ℤ (Set.range ⇑(b.ofZLatticeBasis ℝ S.lattice))).mk_vadd,
      vadd_eq_add] at hg
    convert hg using 1; abel
  · intro s hs
    apply Subtype.ext
    have hs' : s.val + (x - v) ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hs
      change -v + (s.val + x) ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) at hs
      convert hs using 1; abel
    have heq := hg' ⟨s.val, by
      apply Set.mem_of_subset_of_mem ?_ s.prop
      rw [← Submodule.coe_toAddSubgroup, Basis.ofZLatticeBasis_span]
      rfl⟩ hs'
    have hvals : s.val = g := congrArg
      (fun z : ↥(Submodule.span ℤ (Set.range ⇑(b.ofZLatticeBasis ℝ S.lattice))) =>
        (z : EuclideanSpace ℝ (Fin d))) heq
    exact hvals
instance (S : PeriodicSpherePacking 0) : Finite S.centers := inferInstance
noncomputable instance PeriodicSpherePacking.finiteCenterTranslationQuotient :
    Finite (Quotient S.latticeCenterTranslationAction.orbitRel) := by
  let b : Basis _ ℤ S.lattice := (ZLattice.module_free ℝ S.lattice).chooseBasis
  by_cases hd : 0 < d
  · haveI : Finite ↑(S.centers ∩ fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
      finite_centers_in_fundamental_region S b hd
    exact Finite.of_equiv _ (S.centerOrbitEquivBasisRegion b).symm
  · have : d = 0 := Nat.eq_zero_of_not_pos hd
    subst this
    exact Quotient.finite (AddAction.orbitRel ..)
noncomputable instance : Fintype (Quotient S.latticeCenterTranslationAction.orbitRel) :=
  Fintype.ofFinite _
end instances
section centerOrbitCardinality
open scoped Pointwise
open Finset Set
variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))
noncomputable def PeriodicSpherePacking.centerOrbitCardinality : ℕ :=
  Fintype.card (Quotient S.latticeCenterTranslationAction.orbitRel)
theorem PeriodicSpherePacking.card_centers_in_translated_region (hd : 0 < d)
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    haveI := @Fintype.ofFinite _ <| finite_centers_in_translated_fundamental_region S b hd v
    (S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))).toFinset.card = S.centerOrbitCardinality := by
  rw [centerOrbitCardinality]
  exact card_eq_of_equiv_fintype (by simpa using! (S.centerOrbitEquivTranslatedBasisRegion b v).symm)
theorem PeriodicSpherePacking.encard_centers_in_translated_region (hd : 0 < d)
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    (S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))).encard = S.centerOrbitCardinality := by
  rw [← S.card_centers_in_translated_region hd b]
  convert! Set.encard_eq_coe_toFinset_card _
end centerOrbitCardinality
section numReps_aux
variable {d : ℕ}
@[reducible] noncomputable def PeriodicSpherePacking.instFintypeBoundedCenterRepresentatives
  (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) :
  Fintype ↑(S.centers ∩ D) :=
    @Fintype.ofFinite _ <| finite_centers_in_bounded_region S D hD_isBounded hd
noncomputable def PeriodicSpherePacking.boundedCenterRepresentativeCount
  (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) : ℕ :=
  letI := S.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  Fintype.card ↑(S.centers ∩ D)
end numReps_aux
section theorem_2_3
variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))
open scoped Pointwise
theorem iUnion_lattice_inter_ball_sub_vadd_fundamentalDomain_subset_ball
    {ι : Type*} (b : Basis ι ℝ (EuclideanSpace ℝ (Fin d)))
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain b, ‖x‖ ≤ L) (R : ℝ) :
    ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R - L),
      x +ᵥ (fundamentalDomain b : Set (EuclideanSpace ℝ (Fin d)))
        ⊆ ball 0 R := by
  intro z hz
  rcases Set.mem_iUnion.mp hz with ⟨x, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨hx, hz⟩
  rw [Set.mem_vadd_set] at hz
  rcases hz with ⟨y, hy, rfl⟩
  have hxnorm : ‖x‖ < R - L := by
    simpa [mem_ball, dist_zero_right] using hx.2
  have hynorm : ‖y‖ ≤ L := hL y hy
  have hsum : ‖x + y‖ < R :=
    lt_of_le_of_lt (norm_add_le x y) (by linarith)
  simpa [mem_ball, dist_zero_right, vadd_eq_add] using hsum
theorem fundamental_region_translates_disjoint
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S.lattice) (hy : y ∈ S.lattice) (hxy : x ≠ y) :
    Disjoint (x +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))
      (y +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
    Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _))
  have hx' : x ∈ Λ := by simpa [Λ, S.integral_basis_spans_packing_lattice] using! hx
  have hy' : y ∈ Λ := by simpa [Λ, S.integral_basis_spans_packing_lattice] using! hy
  have hxy' : (⟨x, hx'⟩ : Λ) ≠ ⟨y, hy'⟩ := fun h => hxy (by simpa using! congrArg Subtype.val h)
  simpa [Λ] using!
    (translates_disjoint_of_unique_cover (d := d) (Λ := Λ)
      (D := fundamentalDomain (b.ofZLatticeBasis ℝ _))
      (by intro u; simpa using!
        exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) u) hxy')
theorem PeriodicSpherePacking.encard_centers_inter_ball_ge_numReps_nsmul_encard_lattice_inter_ball
    (hd : 0 < d) {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    (↑S.centers ∩ ball 0 R).encard ≥
      S.centerOrbitCardinality • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R - L)).encard := by
  have hsub := Set.inter_subset_inter_right S.centers
    (iUnion_lattice_inter_ball_sub_vadd_fundamentalDomain_subset_ball
      S (b.ofZLatticeBasis ℝ _) hL R)
  rw [Set.biUnion_eq_iUnion, Set.inter_iUnion] at hsub
  have henc := Set.encard_mono hsub
  rw [Set.encard_disjoint_union_eq_tsum] at henc
  · simp_rw [S.encard_centers_in_translated_region hd] at henc
    · convert! henc.ge
      rw [nsmul_eq_mul, ENat.tsum_subtype_constant_eq_encard_mul, mul_comm]
  · intro ⟨x, hx⟩ _ ⟨y, hy⟩ _ hxy
    have hxy' : x ≠ y := fun h => hxy (Subtype.ext h)
    refine Set.disjoint_left.2 fun u hux huy =>
      (Set.disjoint_left.1 (fundamental_region_translates_disjoint (S := S) b hx.left hy.left hxy'))
        hux.right huy.right
theorem ball_subset_iUnion_lattice_inter_ball_add_vadd_fundamentalDomain
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    ball 0 R
      ⊆ ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + L),
        x +ᵥ (fundamentalDomain (b.ofZLatticeBasis ℝ _) : Set (EuclideanSpace ℝ (Fin d))) := by
  letI : Fintype ι := Fintype.ofFinite ι
  intro x hx
  refine Set.mem_iUnion₂.2 ⟨floor (b.ofZLatticeBasis ℝ _) x, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, ← S.mem_integral_basis_span_iff b]
      exact Submodule.coe_mem _
    · rw [mem_ball_zero_iff] at hx ⊢
      have hfloor : ‖floor (b.ofZLatticeBasis ℝ _) x‖ = ‖x - fract (b.ofZLatticeBasis ℝ _) x‖ := by
        simp [fract]
      refine lt_of_le_of_lt (hfloor.le.trans (norm_sub_le _ _)) ?_
      exact add_lt_add_of_lt_of_le hx (hL _ (fract_mem_fundamentalDomain _ _))
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
    exact fract_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
theorem PeriodicSpherePacking.encard_centers_inter_ball_le_numReps_nsmul_encard_lattice_inter_ball
    (hd : 0 < d) {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    (↑S.centers ∩ ball 0 R).encard
      ≤ S.centerOrbitCardinality • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)).encard := by
  have hsub := Set.inter_subset_inter_right S.centers
    (ball_subset_iUnion_lattice_inter_ball_add_vadd_fundamentalDomain S b hL R)
  rw [Set.biUnion_eq_iUnion, Set.inter_iUnion] at hsub
  have henc := Set.encard_mono hsub
  rw [Set.encard_disjoint_union_eq_tsum] at henc
  · simp_rw [S.encard_centers_in_translated_region hd] at henc
    · convert! henc
      rw [nsmul_eq_mul, ENat.tsum_subtype_constant_eq_encard_mul, mul_comm]
  · intro ⟨x, hx⟩ _ ⟨y, hy⟩ _ hxy
    have hxy' : x ≠ y := fun h => hxy (Subtype.ext h)
    refine Set.disjoint_left.2 fun u hux huy =>
      (Set.disjoint_left.1 (fundamental_region_translates_disjoint (S := S) b hx.left hy.left hxy'))
        hux.right huy.right
end theorem_2_3
section theorem_2_2
open scoped Pointwise
variable {d : ℕ} (S : PeriodicSpherePacking d)
  {ι : Type*} [Finite ι]
  (D : Set (EuclideanSpace ℝ (Fin d))) {L : ℝ} (R : ℝ)
theorem lattice_region_is_additive_fundamental_domain
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D) :
    IsAddFundamentalDomain S.lattice D :=
  MeasureTheory.IsAddFundamentalDomain.mk' (μ := volume) hD_measurable.nullMeasurableSet
    hD_unique_covers
theorem ball_covered_by_nearby_lattice_translates
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    ball 0 (R - L) ⊆ ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D) := by
  intro x hx
  have hx' : ‖x‖ < R - L := by simpa [mem_ball_zero_iff] using! hx
  rcases hD_unique_covers x with ⟨g, hg, -⟩
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_inter_iff]
  refine ⟨-g.val, ⟨⟨by simp, ?_⟩, ?_⟩⟩
  · have : ‖g.val‖ < R := by
      have htri : ‖g.val‖ ≤ ‖g.val + x‖ + ‖x‖ := by
        simpa [sub_eq_add_neg, add_assoc] using! (norm_sub_le (a := g.val + x) (b := x))
      refine lt_of_le_of_lt htri ?_
      calc
        ‖g.val + x‖ + ‖x‖ < L + (R - L) := add_lt_add_of_le_of_lt (hL _ (by simpa using! hg)) hx'
        _ = R := by abel
    simpa [mem_ball_zero_iff, norm_neg] using! this
  · exact (Set.mem_vadd_set_iff_neg_vadd_mem).2 (by simpa using! hg)
instance (E : Type*) [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E] [Module ℤ E]
    [Module ℝ E] (μ : Measure E) [μ.IsAddLeftInvariant] [IsScalarTower ℤ ℝ E] (s : Submodule ℤ E) :
    VAddInvariantMeasure s E μ where
  measure_preimage_vadd c t ht := by
    simp only [Submodule.vadd_def, vadd_eq_add, measure_preimage_add]
theorem PeriodicSpherePacking.encard_lattice_inter_ball_ge_volume_ball_sub_div_volume
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L)) / volume D := by
  have hcover := volume.mono
    (ball_covered_by_nearby_lattice_translates (S := S) (D := D) (R := R)
      hD_unique_covers hL)
  rw [Set.biUnion_eq_iUnion] at hcover
  have hcount : Set.Countable
      ((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ ball 0 R) :=
    Set.Countable.mono Set.inter_subset_left
      (countable_of_Lindelof_of_discrete (X := S.lattice))
  letI : Countable
      ↑((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ ball 0 R) := hcount
  apply ENNReal.div_le_of_le_mul
  refine hcover.trans ?_
  calc
    volume (⋃ x : ↑((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ ball 0 R),
      (x : EuclideanSpace ℝ (Fin d)) +ᵥ D)
      ≤ ∑' x : ↑((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ ball 0 R),
        volume ((x : EuclideanSpace ℝ (Fin d)) +ᵥ D) := measure_iUnion_le _
    _ = ∑' _ : ↑((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ ball 0 R),
      volume D := by simp_rw [measure_vadd]
    _ = _ := ENNReal.tsum_set_const _ _
theorem nearby_lattice_translates_subset_expanded_ball (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D) ⊆ ball 0 (R + L) := by
  intro x hx
  rw [mem_ball_zero_iff]
  rcases (by simpa [Set.mem_iUnion, exists_prop, Set.mem_inter_iff] using! hx) with
    ⟨i, ⟨-, hi_ball⟩, hi_mem⟩
  have hi_ball' : ‖i‖ < R := by simpa [mem_ball_zero_iff] using! hi_ball
  have hi_mem' : ‖-i + x‖ ≤ L := hL _ (Set.mem_vadd_set_iff_neg_vadd_mem.mp hi_mem)
  calc
    _ = ‖i + (-i + x)‖ := by congr; abel
    _ ≤ ‖i‖ + ‖-i + x‖ := norm_add_le _ _
    _ < R + L := add_lt_add_of_lt_of_le hi_ball' hi_mem'
theorem PeriodicSpherePacking.encard_lattice_inter_ball_le_volume_ball_add_div_volume
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
    (hL : ∀ x ∈ D, ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)) / volume D := by
  classical
  let T : Set (EuclideanSpace ℝ (Fin d)) := ↑S.lattice ∩ ball 0 R
  letI : Countable T :=
    Set.Countable.mono Set.inter_subset_left
      (countable_of_Lindelof_of_discrete (X := S.lattice))
  have hfinite : volume D ≠ ⊤ := ne_of_lt <|
    ((Metric.isBounded_closedBall : Bornology.IsBounded
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) L)).subset
      (fun x hx => by simpa [Metric.mem_closedBall, dist_zero_right] using hL x hx)).measure_lt_top
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hnonzero : volume D ≠ 0 :=
    (lattice_region_is_additive_fundamental_domain S D hD_unique_covers hD_measurable).measure_ne_zero
      (fun hv => by
        have hp := euclidean_ball_volume_positive (0 : EuclideanSpace ℝ (Fin d)) (by norm_num : (0 : ℝ) < 1)
        simp [hv] at hp)
  apply (ENNReal.le_div_iff_mul_le (Or.inl hnonzero) (Or.inl hfinite)).2
  calc
    (T.encard : ℝ≥0∞) * volume D =
        ∑' x : T, volume ((x : EuclideanSpace ℝ (Fin d)) +ᵥ D) := by
          simp_rw [measure_vadd]
          exact (ENNReal.tsum_set_const T (volume D)).symm
    _ = volume (⋃ x : T, (x : EuclideanSpace ℝ (Fin d)) +ᵥ D) := by
      symm
      apply measure_iUnion
      · intro x y hxy
        exact translates_disjoint_of_unique_cover (Λ := S.lattice) (D := D)
          hD_unique_covers (g := ⟨x, x.property.1⟩) (h := ⟨y, y.property.1⟩)
          (fun h => hxy (Subtype.ext
            (congrArg (fun z : S.lattice => (z : EuclideanSpace ℝ (Fin d))) h)))
      · intro x
        have hxset : (x : EuclideanSpace ℝ (Fin d)) +ᵥ D =
            (fun z : EuclideanSpace ℝ (Fin d) => -(x : EuclideanSpace ℝ (Fin d)) + z) ⁻¹' D := by
          ext z
          simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_preimage, vadd_eq_add]
        rw [hxset]
        exact hD_measurable.preimage
          (measurable_const.add measurable_id :
            Measurable (fun z : EuclideanSpace ℝ (Fin d) => -(x : EuclideanSpace ℝ (Fin d)) + z))
    _ ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)) := by
      apply volume.mono
      simpa [T, Set.biUnion_eq_iUnion] using
        (nearby_lattice_translates_subset_expanded_ball (S := S) (D := D) (R := R) hL)
open ZSpan
variable (b : Basis ι ℤ S.lattice)
theorem
    PeriodicSpherePacking.encard_lattice_inter_ball_ge_volume_ball_sub_div_volume_fundamentalDomain
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  refine S.encard_lattice_inter_ball_ge_volume_ball_sub_div_volume
    _ R ?_ hL
  intro x
  rcases exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x with
    ⟨⟨v, hv⟩, hvD, hvuniq⟩
  refine ⟨⟨v, by simpa [S.integral_basis_spans_packing_lattice] using! hv⟩, hvD, ?_⟩
  rintro ⟨y, hy⟩ hyD
  have := hvuniq ⟨y, by simpa [S.integral_basis_spans_packing_lattice] using! hy⟩ hyD
  exact Subtype.ext (by simpa using! congrArg Subtype.val this)
theorem
    PeriodicSpherePacking.encard_lattice_inter_ball_le_volume_ball_add_div_volume_fundamentalDomain
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  refine S.encard_lattice_inter_ball_le_volume_ball_add_div_volume
    _ R ?_ (fundamentalDomain_measurableSet _) hL hd
  intro x
  rcases exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x with
    ⟨⟨v, hv⟩, hvD, hvuniq⟩
  refine ⟨⟨v, by simpa [S.integral_basis_spans_packing_lattice] using! hv⟩, hvD, ?_⟩
  rintro ⟨y, hy⟩ hyD
  have := hvuniq ⟨y, by simpa [S.integral_basis_spans_packing_lattice] using! hy⟩ hyD
  exact Subtype.ext (by simpa using! congrArg Subtype.val this)
section finiteDensity_limit
open MeasureTheory Measure Metric ZSpan
variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)
theorem finiteDensity_le_numReps_mul_volume_ball_ratio
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.densityInsideRadius R ≤
      S.centerOrbitCardinality
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := calc
  _ ≤ (S.centers ∩ ball 0 (R + S.separation / 2)).encard
      * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
    S.local_density_upper_bound hd R
  _ ≤ S.centerOrbitCardinality
        • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L)).encard
          * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
            / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    gcongr
    simpa using! ENat.toENNReal_le.mpr
      (S.encard_centers_inter_ball_le_numReps_nsmul_encard_lattice_inter_ball hd b hL _)
  _ ≤ S.centerOrbitCardinality
        * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L + L))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    rw [nsmul_eq_mul]
    gcongr
    exact S.encard_lattice_inter_ball_le_volume_ball_add_div_volume_fundamentalDomain _ b hL hd
  _ = S.centerOrbitCardinality
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, mul_two, ← add_assoc, ← ENNReal.mul_div_right_comm,
      ← ENNReal.mul_div_right_comm, mul_assoc, mul_assoc]
    congr 3
    rw [mul_comm]
theorem finiteDensity_ge_numReps_mul_volume_ball_ratio
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.densityInsideRadius R ≥
      S.centerOrbitCardinality
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
  calc
    _ ≥ (S.centers ∩ ball 0 (R - S.separation / 2)).encard
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
      S.local_density_lower_bound hd R
    _ ≥ S.centerOrbitCardinality
        • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d))
          (R - S.separation / 2 - L)).encard
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
      gcongr
      simpa using ENat.toENNReal_le.mpr
        (S.encard_centers_inter_ball_ge_numReps_nsmul_encard_lattice_inter_ball
          hd b hL (R - S.separation / 2))
    _ ≥ S.centerOrbitCardinality
        * (volume (ball (0 : EuclideanSpace ℝ (Fin d))
          (R - S.separation / 2 - L - L))
            / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))
              * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
                / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
      rw [nsmul_eq_mul]
      gcongr
      exact S.encard_lattice_inter_ball_ge_volume_ball_sub_div_volume_fundamentalDomain
        _ b hL
    _ = _ := by
      rw [show R - S.separation / 2 - L - L =
        R - S.separation / 2 - L * 2 by ring]
      simp only [div_eq_mul_inv]
      ac_rfl
open Filter Topology
section VolumeBallRatio
open scoped Topology NNReal
open Asymptotics Filter ENNReal EuclideanSpace
theorem volume_ball_add_div_volume_ball_add_tendsto_one_of_nonneg
    {d : ℕ} {C C' : ℝ} (hd : 0 < d) (hC : 0 ≤ C) (hC' : 0 ≤ C') :
      Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hshift : Tendsto (fun R : ℝ => R + C') atTop atTop :=
    tendsto_atTop_add_const_right _ C' tendsto_id
  have herror : Tendsto (fun R : ℝ => (C - C') / (R + C')) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp hshift).const_mul (C - C')
  have hratio : Tendsto (fun R : ℝ => (R + C) / (R + C')) atTop (𝓝 1) := by
    have hsum : Tendsto (fun R : ℝ => 1 + (C - C') / (R + C')) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add herror
    apply Tendsto.congr' (f₁ := fun R : ℝ => 1 + (C - C') / (R + C')) ?_ hsum
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hden : R + C' ≠ 0 := ne_of_gt (by linarith)
    field_simp; ring
  have hpow : Tendsto (fun R : ℝ => ((R + C) / (R + C')) ^ d) atTop (𝓝 1) := by
    simpa using hratio.pow d
  have henn : Tendsto
      (fun R : ℝ => ENNReal.ofReal (((R + C) / (R + C')) ^ d)) atTop (𝓝 1) := by
    simpa using tendsto_ofReal hpow
  apply Tendsto.congr'
    (f₁ := fun R : ℝ => ENNReal.ofReal (((R + C) / (R + C')) ^ d)) ?_ henn
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  symm
  rw [volume_ball, volume_ball, Fintype.card_fin, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_mul, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_div_of_pos, mul_div_mul_right, ← div_pow]
  <;> positivity
theorem Filter.atTop_invariant_under_translation {β : Type*} {f : ℝ → β} (C : ℝ) (α : Filter β) :
    Tendsto f atTop α ↔ Tendsto (fun x ↦ f (x + C)) atTop α := by
  have hmap : Filter.map (fun x : ℝ => x + C) atTop = atTop := by
    simpa using! (Filter.map_add_atTop_eq (α := ℝ) (k := C))
  constructor <;> intro hf
  · exact tendsto_map'_iff.mp (by simpa [hmap] using! hf)
  · have : Tendsto f (Filter.map (fun x : ℝ => x + C) atTop) α := tendsto_map'_iff.mpr hf
    simpa [hmap] using! this
theorem volume_ball_add_div_volume_ball_add_tendsto_one {d : ℕ} {C C' : ℝ} (hd : 0 < d) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  have hC₀ : 0 ≤ max (-C) (-C') + C := by linarith [le_max_left (-C) (-C')]
  have hC'₀ : 0 ≤ max (-C) (-C') + C' := by linarith [le_max_right (-C) (-C')]
  refine (Filter.atTop_invariant_under_translation (f := fun R ↦
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C)) /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) (max (-C) (-C')) _).mpr ?_
  simpa [add_assoc] using!
    volume_ball_add_div_volume_ball_add_tendsto_one_of_nonneg (d := d) (C := max (-C) (-C') + C)
      (C' := max (-C) (-C') + C') hd hC₀ hC'₀
end VolumeBallRatio
end finiteDensity_limit
end theorem_2_2
end
section
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open Filter
open scoped Pointwise
open scoped Topology
variable {d : ℕ}
section DensityEqFdDensity
variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)
lemma PeriodicSpherePacking.local_packing_density_tends_to_formula
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    Tendsto S.densityInsideRadius atTop
      (𝓝 (S.centerOrbitCardinality * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_
      (finiteDensity_ge_numReps_mul_volume_ball_ratio b · hL hd)
      (finiteDensity_le_numReps_mul_volume_ball_ratio b · hL hd)
  · rw [show ∀ a : ENNReal, 𝓝 a = 𝓝 (a * 1) by intro; rw [mul_one]]
    apply ENNReal.Tendsto.const_mul
    · simp_rw [sub_sub, sub_eq_add_neg]
      convert! volume_ball_add_div_volume_ball_add_tendsto_one hd (C := -(S.separation / 2 + L * 2))
      rw [add_zero]
    · left
      exact one_ne_zero
  · rw [show ∀ a : ENNReal, 𝓝 a = 𝓝 (a * 1) by intro; rw [mul_one]]
    apply ENNReal.Tendsto.const_mul
    · simp_rw [add_assoc]
      convert! volume_ball_add_div_volume_ball_add_tendsto_one hd (C := S.separation / 2 + L * 2)
      rw [add_zero]
    · left
      exact one_ne_zero
theorem PeriodicSpherePacking.density_eq_numReps_mul_volume_ball_div_volume_fundamentalDomain
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.upperPackingDensity
      = S.centerOrbitCardinality * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  limsSup_eq_of_le_nhds (S.local_packing_density_tends_to_formula b hL hd)
end DensityEqFdDensity
section ConstantEqNormalizedConstant
end ConstantEqNormalizedConstant
section Disjoint_Covering_of_Centers
end Disjoint_Covering_of_Centers
section Fundamental_Domains_in_terms_of_Basis
open Submodule
variable (S : PeriodicSpherePacking d) (b : Basis (Fin d) ℤ S.lattice)
theorem PeriodicSpherePacking.fundamental_region_admits_norm_bound :
  ∃ L : ℝ, ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L :=
  isBounded_iff_forall_norm_le.1 (fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b))
theorem PeriodicSpherePacking.basis_region_translates_cover_uniquely :
   ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) := by
  intro x
  obtain ⟨g, hg, h_unique⟩ :=
    exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  have hg_lattice : (g : EuclideanSpace ℝ (Fin d)) ∈ S.lattice :=
    (S.mem_integral_basis_span_iff b g).mp g.property
  refine ⟨⟨g, hg_lattice⟩, hg, ?_⟩
  rintro ⟨h, hh⟩ h_mem
  apply Subtype.ext
  exact congrArg
    (fun z : Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) =>
      (z : EuclideanSpace ℝ (Fin d)))
    (h_unique ⟨h, (S.mem_integral_basis_span_iff b h).mpr hh⟩ h_mem)
end Fundamental_Domains_in_terms_of_Basis
section Periodic_Density_Formula
noncomputable def PeriodicSpherePacking.coordinateIndexEquiv
    (P : PeriodicSpherePacking d) : (Module.Free.ChooseBasisIndex ℤ ↥P.lattice) ≃ (Fin d) :=
  ZLattice.coordinateIndexEquiv P.lattice
noncomputable def PeriodicSpherePacking.canonicalPackingLatticeBasis (S : PeriodicSpherePacking d) :
    Basis (Fin d) ℤ ↥S.lattice :=
  ((ZLattice.module_free ℝ S.lattice).chooseBasis).reindex S.coordinateIndexEquiv
@[simp] theorem PeriodicSpherePacking.density_eq_numReps_mul_volume_ball_div_covolume
  (S : PeriodicSpherePacking d) (hd : 0 < d) : S.upperPackingDensity =
  (ENat.toENNReal (S.centerOrbitCardinality : ENat)) *
  volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) /
  Real.toNNReal (ZLattice.covolume S.lattice) := by
  obtain ⟨L, hL⟩ := S.fundamental_region_admits_norm_bound S.canonicalPackingLatticeBasis
  rw [S.density_eq_numReps_mul_volume_ball_div_volume_fundamentalDomain
    S.canonicalPackingLatticeBasis hL hd]
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hfinite :
      volume (fundamentalDomain (S.canonicalPackingLatticeBasis.ofZLatticeBasis ℝ _)) ≠ ⊤ :=
    (Bornology.IsBounded.measure_lt_top
      (fundamentalDomain_isBounded (S.canonicalPackingLatticeBasis.ofZLatticeBasis ℝ _))).ne
  have hfund :
      IsAddFundamentalDomain S.lattice
        (fundamentalDomain (S.canonicalPackingLatticeBasis.ofZLatticeBasis ℝ _)) :=
    lattice_region_is_additive_fundamental_domain S _
      (S.basis_region_translates_cover_uniquely S.canonicalPackingLatticeBasis)
      (fundamentalDomain_measurableSet _)
  rw [ZLattice.covolume_eq_measure_fundamentalDomain S.lattice volume hfund]
  have hdenom :
      (↑(Real.toNNReal
        (volume.real (fundamentalDomain
          (S.canonicalPackingLatticeBasis.ofZLatticeBasis ℝ _)))) : ENNReal) =
        volume (fundamentalDomain (S.canonicalPackingLatticeBasis.ofZLatticeBasis ℝ _)) := by
    change ENNReal.ofReal
      (volume (fundamentalDomain
        (S.canonicalPackingLatticeBasis.ofZLatticeBasis ℝ _))).toReal = _
    exact ENNReal.ofReal_toReal hfinite
  rw [hdenom]
  norm_num
end Periodic_Density_Formula
section Empty_Centers
end Empty_Centers
end
section
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
section PeriodicConstantAux
open MeasureTheory Metric EuclideanSpace
open scoped Pointwise
variable {d : ℕ}
lemma center_distance_bound_of_disjoint_regions {x y : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    {A B : Set (EuclideanSpace ℝ (Fin d))}
    (hx : ball x r ⊆ A) (hy : ball y r ⊆ B) (hAB : Disjoint A B) :
    2 * r ≤ dist x y := by
  by_contra hlt
  have hlt' : dist x y < 2 * r := lt_of_not_ge hlt
  let m : EuclideanSpace ℝ (Fin d) := midpoint ℝ x y
  have hhalf : (1 / 2 : ℝ) * dist x y < r := by nlinarith
  have hmx : m ∈ ball x r := by
    simpa [Metric.mem_ball, dist_comm, m] using! (by simpa [m] using! hhalf : dist m x < r)
  have hmy : m ∈ ball y r := by
    simpa [Metric.mem_ball, dist_comm, m] using! (by simpa [m, dist_comm] using! hhalf : dist m y < r)
  exact Set.disjoint_left.1 hAB (hx hmx) (hy hmy)
open scoped Pointwise in

noncomputable def latticeReplicatedCenters (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    (F : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ g : Λ, g +ᵥ F
lemma mem_replicated_centers_iff {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {F : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ latticeReplicatedCenters (d := d) Λ F ↔ ∃ g : Λ, ∃ f ∈ F, x = g +ᵥ f := by
  simp [latticeReplicatedCenters, Set.mem_iUnion, Set.mem_vadd_set, eq_comm]
lemma replicated_centers_translation_closed {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {F : Set (EuclideanSpace ℝ (Fin d))} {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ Λ) (hy : y ∈ latticeReplicatedCenters (d := d) Λ F) :
    x + y ∈ latticeReplicatedCenters (d := d) Λ F := by
  rcases (mem_replicated_centers_iff (d := d) (Λ := Λ) (F := F) (x := y)).1 hy with ⟨g, f, hf, rfl⟩
  refine (mem_replicated_centers_iff (d := d) (Λ := Λ) (F := F)).2 ⟨(⟨x, hx⟩ : Λ) + g, f, hf, ?_⟩
  simp [Submodule.vadd_def, vadd_eq_add, add_assoc]
lemma translated_ball_subset_translated_region {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D : Set (EuclideanSpace ℝ (Fin d))} {r : ℝ} {g : Λ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : ball x r ⊆ D) :
    ball (g +ᵥ x) r ⊆ g +ᵥ D := by
  intro y hy
  refine Set.mem_vadd_set.2 ⟨(-g : Λ) +ᵥ y, ?_, by simp [Submodule.vadd_def, vadd_eq_add]⟩
  apply hx
  have :
      (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ y ∈
        (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ ball (g +ᵥ x) r :=
    Set.mem_vadd_set.2 ⟨y, by simpa [Submodule.vadd_def, vadd_eq_add] using! hy, rfl⟩
  simpa [Metric.vadd_ball, add_vadd, Submodule.vadd_def, vadd_eq_add] using! this
noncomputable def replicate_to_periodic_packing
    (S : SpherePacking d)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (D F : Set (EuclideanSpace ℝ (Fin d)))
    (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D)
    (hF_centers : F ⊆ S.centers)
    (hF_ball : ∀ x ∈ F, ball x (S.separation / 2) ⊆ D) :
    PeriodicSpherePacking d := by
  refine
    { centers := latticeReplicatedCenters (d := d) Λ F
      separation := S.separation
      separation_pos := S.separation_pos
      centers_dist := ?_
      lattice := Λ
      lattice_action := ?_
      lattice_discrete := inferInstance
      lattice_isZLattice := inferInstance }
  ·
    intro a b hab
    change S.separation ≤ dist (a : EuclideanSpace ℝ (Fin d)) (b : EuclideanSpace ℝ (Fin d))
    rcases (mem_replicated_centers_iff (d := d) (Λ := Λ) (F := F)
      (x := (a : EuclideanSpace ℝ (Fin d)))).1
        a.property with ⟨ga, fa, hfa, ha⟩
    rcases (mem_replicated_centers_iff (d := d) (Λ := Λ) (F := F)
      (x := (b : EuclideanSpace ℝ (Fin d)))).1
        b.property with ⟨gb, fb, hfb, hb⟩
    by_cases hgg : ga = gb
    · subst hgg
      have hne : fa ≠ fb := by
        intro h
        apply hab
        apply Subtype.ext
        simp [ha, hb, h]
      have hdist := S.distinct_centers_separation_bound fa fb (hF_centers hfa) (hF_centers hfb) hne
      have : S.separation ≤ dist (ga +ᵥ fa) (ga +ᵥ fb) := by
        have htrans : dist (ga +ᵥ fa) (ga +ᵥ fb) = dist fa fb :=
          dist_vadd_cancel_left (ga : EuclideanSpace ℝ (Fin d)) fa fb
        simpa [htrans] using! hdist
      simpa [ha, hb] using! this
    ·
      have hballa : ball (ga +ᵥ fa) (S.separation / 2) ⊆ ga +ᵥ D :=
        translated_ball_subset_translated_region (d := d) (Λ := Λ) (D := D) (g := ga) (x := fa) (r := S.separation / 2)
          (hF_ball fa hfa)
      have hballb : ball (gb +ᵥ fb) (S.separation / 2) ⊆ gb +ᵥ D :=
        translated_ball_subset_translated_region (d := d) (Λ := Λ) (D := D) (g := gb) (x := fb) (r := S.separation / 2)
          (hF_ball fb hfb)
      have hdisj : Disjoint (ga +ᵥ D) (gb +ᵥ D) :=
        translates_disjoint_of_unique_cover (d := d) (Λ := Λ) (D := D) hD_unique_covers hgg
      have : 2 * (S.separation / 2) ≤ dist (ga +ᵥ fa) (gb +ᵥ fb) :=
        center_distance_bound_of_disjoint_regions (d := d) hballa hballb hdisj
      have : S.separation ≤ dist (ga +ᵥ fa) (gb +ᵥ fb) := by
        simpa [two_mul, add_halves] using! this
      simpa [ha, hb] using! this
  ·
    intro x y hx hy
    exact replicated_centers_translation_closed (d := d) (Λ := Λ) (F := F) hx hy
end PeriodicConstantAux
section PeriodicConstantCube
open scoped Pointwise
variable {d : ℕ}
def axisAlignedCell (L : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Ico (0 : ℝ) L}
def insetAxisAlignedCell (L r : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Icc r (L - r)}
noncomputable def axisCellBasis (L : ℝ) (hL : 0 < L) :
    Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis).isUnitSMul
    (fun _ : Fin d ↦ IsUnit.mk0 L (ne_of_gt hL))
noncomputable def axisCellLattice (L : ℝ) (hL : 0 < L) :
    Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range (axisCellBasis (d := d) L hL))
lemma axis_cell_basis_fundamental_region (L : ℝ) (hL : 0 < L) :
    fundamentalDomain (axisCellBasis (d := d) L hL) = axisAlignedCell (d := d) L := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain, axisAlignedCell, axisCellBasis, Module.Basis.repr_isUnitSMul,
    Units.smul_def, Units.val_inv_eq_inv_val, Set.mem_setOf_eq,
    Set.mem_Ico]
  constructor
  · intro hx i
    specialize hx i
    refine ⟨?_, ?_⟩
    · have : 0 ≤ (L : ℝ) * (L⁻¹ * x.ofLp i) := mul_nonneg (le_of_lt hL) hx.1
      have : 0 ≤ (L * L⁻¹) * x.ofLp i := by simpa [mul_assoc] using! this
      simpa [mul_inv_cancel₀ (ne_of_gt hL)] using! this
    · have : (L : ℝ) * (L⁻¹ * x.ofLp i) < (L : ℝ) * 1 := mul_lt_mul_of_pos_left hx.2 hL
      have : (L * L⁻¹) * x.ofLp i < (L : ℝ) * 1 := by simpa [mul_assoc] using! this
      simpa [mul_inv_cancel₀ (ne_of_gt hL)] using! this
  · intro hx i
    specialize hx i
    have hLinv : 0 < (L⁻¹ : ℝ) := inv_pos.mpr hL
    refine ⟨mul_nonneg (le_of_lt hLinv) hx.1, ?_⟩
    have : (L⁻¹ : ℝ) * x.ofLp i < (L⁻¹ : ℝ) * L := mul_lt_mul_of_pos_left hx.2 hLinv
    simpa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hL), one_mul] using! this
end PeriodicConstantCube
section Periodic_Constant_Eq_Constant
open scoped Pointwise
namespace PeriodicConstant
variable {d : ℕ}
lemma axis_cell_translates_cover_uniquely (L : ℝ) (hL : 0 < L) :
    ∀ x, ∃! g : axisCellLattice (d := d) L hL, g +ᵥ x ∈ axisAlignedCell (d := d) L := fun x => by
    simpa [axisCellLattice, axis_cell_basis_fundamental_region (d := d) (L := L) (hL := hL)] using!
      exist_unique_vadd_mem_fundamentalDomain (axisCellBasis (d := d) L hL) x
end PeriodicConstant
section PeriodicConstantApprox
open scoped Pointwise
open MeasureTheory Metric
namespace PeriodicConstantApprox
variable {d : ℕ}
lemma lattice_points_in_ball_finite (L : ℝ) (hL : 0 < L) (R : ℝ) :
    Set.Finite {g : axisCellLattice (d := d) L hL | (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 R} := by
  letI : DiscreteTopology (axisCellLattice (d := d) L hL) := by
    unfold axisCellLattice
    infer_instance
  have hdiscrete := (inferInstance : DiscreteTopology (axisCellLattice (d := d) L hL))
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff] at hdiscrete
  obtain ⟨ε, hε, hεzero⟩ := hdiscrete
  have hzero : ∀ g : axisCellLattice (d := d) L hL, ‖g‖ < ε → g = 0 := by
    intro g hg
    apply hεzero g
    simpa [dist_zero_right] using hg
  let P : SpherePacking d :=
    { centers := (axisCellLattice (d := d) L hL : Set (EuclideanSpace ℝ (Fin d)))
      separation := ε
      separation_pos := hε
      centers_dist := by
        intro x y hxy
        by_contra hdist
        have hdist' : dist (x : EuclideanSpace ℝ (Fin d)) y < ε := by
          change ¬ ε ≤ dist (x : EuclideanSpace ℝ (Fin d)) y at hdist
          exact lt_of_not_ge hdist
        let g : axisCellLattice (d := d) L hL :=
          ⟨(x : EuclideanSpace ℝ (Fin d)) - y, sub_mem x.property y.property⟩
        have hg : ‖g‖ < ε := by
          simpa [g, dist_eq_norm] using hdist'
        have hgeq : g = 0 := hzero g hg
        apply hxy
        apply Subtype.ext
        exact sub_eq_zero.mp (congrArg (fun z : axisCellLattice (d := d) L hL =>
          (z : EuclideanSpace ℝ (Fin d))) hgeq) }
  have hfinite : Set.Finite (P.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
    (Set.finite_coe_iff).1 (P.finite_centers_inside_ball R)
  refine (hfinite.preimage (f := fun g : axisCellLattice (d := d) L hL =>
    (g : EuclideanSpace ℝ (Fin d))) Subtype.val_injective.injOn).subset ?_
  intro g hg
  exact ⟨g.property, hg⟩
end PeriodicConstantApprox
end PeriodicConstantApprox
end Periodic_Constant_Eq_Constant
end
section
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
namespace PeriodicConstantApprox
section CoordCubeCover
open Metric
variable (L : ℝ) (hL : 0 < L)
noncomputable def axisCellCoverIndex (x : EuclideanSpace ℝ (Fin d)) : axisCellLattice (d := d) L hL :=
  Classical.choose (PeriodicConstant.axis_cell_translates_cover_uniquely (d := d) L hL x)
end CoordCubeCover
section CoverVolumeBound
open scoped BigOperators
end CoverVolumeBound
section BoundaryControl
open scoped ENNReal Pointwise BigOperators
def constantCoordinateVector (c : ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun _ : Fin d => c)
variable (S : SpherePacking d)
end BoundaryControl
end PeriodicConstantApprox
namespace SpherePacking
open Filter
variable {d : ℕ}
end SpherePacking
namespace PeriodicConstantApprox
open Filter
variable {d : ℕ}
def uniformShellShift (d : ℕ) (c : ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun _ : Fin d => c)
section BoundaryControlShellVec
open scoped ENNReal Pointwise BigOperators
open SpherePacking EuclideanSpace MeasureTheory Metric
variable {d : ℕ}
variable (S : SpherePacking d)
end BoundaryControlShellVec
section CubeLatticeCovolume
open scoped ENNReal
open ZSpan
end CubeLatticeCovolume
section PeriodizeCubeDensity
open scoped ENNReal Pointwise
open SpherePacking EuclideanSpace MeasureTheory Metric Bornology
variable {d : ℕ}
end PeriodizeCubeDensity
end PeriodicConstantApprox
namespace SpherePacking
open Filter
open scoped ENNReal BigOperators
variable {d : ℕ}
end SpherePacking
end
section
open scoped BigOperators Real
open MeasureTheory
namespace SchwartzMap.UnitAddTorus
def coordinateTorusProjection (n : ℕ) : (Fin n → ℝ) → UnitAddTorus (Fin n) :=
  fun x i => (x i : UnitAddCircle)
@[continuity]
theorem continuous_coordinate_torus_projection {n : ℕ} : Continuous (coordinateTorusProjection n) := by
  simpa [coordinateTorusProjection, UnitAddCircle] using!
    (continuous_pi fun i => (AddCircle.continuous_mk' (p := (1 : ℝ))).comp (continuous_apply i))
def successorCoordinateHomeomorphism (α : Type*) [TopologicalSpace α] (n : ℕ) :
    (α × (Fin n → α)) ≃ₜ (Fin n.succ → α) where
  toEquiv := Fin.consEquiv (fun _ ↦ α)
  continuous_toFun := by
    simpa [Fin.consEquiv] using! Continuous.finCons (by fun_prop) (by fun_prop)
  continuous_invFun := by fun_prop
theorem coordinate_torus_projection_is_open_quotient (n : ℕ) : IsOpenQuotientMap (coordinateTorusProjection n) := by
  induction n with
  | zero =>
      have h : coordinateTorusProjection 0 =
          (Homeomorph.homeomorphOfUnique (Fin 0 → ℝ) (UnitAddTorus (Fin 0)) : _ → _) := by
        funext x; exact Subsingleton.elim _ _
      simpa [h] using!
        (Homeomorph.homeomorphOfUnique (Fin 0 → ℝ) (UnitAddTorus (Fin 0))).isOpenQuotientMap
  | succ n ih =>
      have h₁ : IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle)) := by
        simpa using!
          (QuotientAddGroup.isOpenQuotientMap_mk (G := ℝ) (N := AddSubgroup.zmultiples (1 : ℝ)))
      let eX := (successorCoordinateHomeomorphism (α := ℝ) n).symm
      let eY := successorCoordinateHomeomorphism (α := UnitAddCircle) n
      have heX : IsOpenQuotientMap (eX : (Fin n.succ → ℝ) → ℝ × (Fin n → ℝ)) :=
        eX.isOpenQuotientMap
      have hprod :
          IsOpenQuotientMap (Prod.map (fun x : ℝ => (x : UnitAddCircle)) (coordinateTorusProjection n)) :=
        IsOpenQuotientMap.prodMap h₁ (ih)
      have hconj :
          coordinateTorusProjection n.succ =
            (fun x =>
              eY
                (Prod.map (fun x : ℝ => (x : UnitAddCircle)) (coordinateTorusProjection n) (eX x))) := by
        funext x
        ext i
        cases i using Fin.cases with
        | zero => simp [coordinateTorusProjection, eY, successorCoordinateHomeomorphism, eX, Prod.map]
        | succ i => simp [coordinateTorusProjection, eY, successorCoordinateHomeomorphism, eX, Prod.map, Fin.tail]
      have hhomeoY : IsOpenQuotientMap eY := eY.isOpenQuotientMap
      rw [hconj]
      exact IsOpenQuotientMap.comp hhomeoY
        (IsOpenQuotientMap.comp hprod heX)
end SchwartzMap.UnitAddTorus
end
section
namespace SpherePacking.ForMathlib.Fourier
open scoped FourierTransform
open MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
end SpherePacking.ForMathlib.Fourier
end
section
open scoped BigOperators
open MeasureTheory
namespace SchwartzMap
variable {d : ℕ}
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
section StandardLattice
noncomputable def referenceIntegerLattice (d : ℕ) :
    Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))
namespace referenceIntegerLattice
instance instDiscreteReferenceIntegerLattice : DiscreteTopology (referenceIntegerLattice d) := by
  simpa [referenceIntegerLattice] using!
    (inferInstance :
      DiscreteTopology
        (Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))))
instance instFullRankPackingLattice : IsZLattice ℝ (referenceIntegerLattice d) := by
  simpa [referenceIntegerLattice] using!
    (inferInstance :
      IsZLattice ℝ
        (Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))))
end StandardLattice.referenceIntegerLattice
section PoissonSummation
namespace PoissonSummation
namespace Standard
noncomputable def embeddedIntegerVector (k : Fin d → ℤ) : (EuclideanSpace ℝ (Fin d)) :=
  WithLp.toLp (2 : ENNReal) (fun i : Fin d => (k i : ℝ))
@[simp]
lemma embedded_integer_vector_coordinate (k : Fin d → ℤ) (i : Fin d) :
    embeddedIntegerVector (d := d) k i = (k i : ℝ) := by
  simp [embeddedIntegerVector]
lemma embedded_integer_vector_mem_reference_lattice (k : Fin d → ℤ) :
    embeddedIntegerVector (d := d) k ∈ SchwartzMap.referenceIntegerLattice d := by
  have hsum :
      embeddedIntegerVector (d := d) k =
        ∑ i : Fin d, (k i) • ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis i) := by
    ext j
    simp [embeddedIntegerVector, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, Pi.single_apply]
  rw [hsum]
  refine (SchwartzMap.referenceIntegerLattice d).sum_mem ?_
  intro i hi
  refine (SchwartzMap.referenceIntegerLattice d).smul_mem (k i) ?_
  exact Submodule.subset_span ⟨i, rfl⟩
end SchwartzMap.PoissonSummation.PoissonSummation.Standard
namespace SchwartzMap
open TopologicalSpace MeasureTheory
variable {d : ℕ}
namespace PoissonSummation.Standard
open UnitAddTorus
def halfOpenUnitCell : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i : Fin d, x i ∈ Set.Ioc (0 : ℝ) 1}
lemma reference_lattice_element_eq_integer_vector (x : (EuclideanSpace ℝ (Fin d)))
    (hx : x ∈ SchwartzMap.referenceIntegerLattice d) :
    ∃ n : Fin d → ℤ, x = SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n := by
  let b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := EuclideanSpace.basisFun (Fin d) ℝ
  have hx_span :
      x ∈ Submodule.span ℤ (Set.range fun j : Fin d => (b.toBasis j : (EuclideanSpace ℝ (Fin d)))) := by
    simpa [SchwartzMap.referenceIntegerLattice, referenceIntegerLattice] using! hx
  have hx_repr :=
    (Module.Basis.mem_span_iff_repr_mem (R := ℤ) (b := b.toBasis) x).1 hx_span
  choose n hn using hx_repr
  have hn' : ∀ i : Fin d, (n i : ℝ) = x i := by
    intro i
    simpa [b] using! hn i
  refine ⟨n, ?_⟩
  ext i
  simp [SchwartzMap.PoissonSummation.Standard.embedded_integer_vector_coordinate, hn' i]
lemma reference_lattice_dual_self :
    LinearMap.BilinForm.dualSubmodule (B := (innerₗ (EuclideanSpace ℝ (Fin d)) : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin d))))
        (SchwartzMap.referenceIntegerLattice d) =
      SchwartzMap.referenceIntegerLattice d := by
  ext x
  constructor
  · intro hx
    have hxcoord : ∀ i : Fin d, ∃ n : ℤ, (n : ℝ) = x i := by
      intro i
      have hinner :
          inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ i) ∈ (1 : Submodule ℤ ℝ) := by
        simpa [innerₗ_apply_apply] using!
          hx _ (Submodule.subset_span ⟨i, by simp⟩)
      rcases Submodule.mem_one.mp hinner with ⟨n, hn⟩
      exact ⟨n, by simpa [-EuclideanSpace.basisFun_apply] using! hn⟩
    choose n hn using hxcoord
    have hx' : x = SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n := by
      ext i
      simp [SchwartzMap.PoissonSummation.Standard.embedded_integer_vector_coordinate, hn i]
    simpa [hx'] using!
      SchwartzMap.PoissonSummation.Standard.embedded_integer_vector_mem_reference_lattice (d := d) n
  · intro hx y hy
    rcases reference_lattice_element_eq_integer_vector (d := d) x hx with ⟨n, rfl⟩
    rcases reference_lattice_element_eq_integer_vector (d := d) y hy with ⟨m, rfl⟩
    refine Submodule.mem_one.mpr ⟨∑ i : Fin d, n i * m i, ?_⟩
    simp [innerₗ_apply_apply, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector,
      PiLp.inner_apply, map_sum, Int.cast_mul, mul_comm]
end SchwartzMap.PoissonSummation.Standard
namespace SchwartzMap
variable {d : ℕ}
namespace PoissonSummation.Standard
open UnitAddTorus
def euclideanTorusProjection : (EuclideanSpace ℝ (Fin d)) → UnitAddTorus (Fin d) :=
  fun x => UnitAddTorus.coordinateTorusProjection d ((WithLp.ofLp : (EuclideanSpace ℝ (Fin d)) → (Fin d → ℝ)) x)
@[continuity]
theorem continuous_euclidean_torus_projection : Continuous (euclideanTorusProjection (d := d)) := by
  simpa [euclideanTorusProjection] using! (UnitAddTorus.continuous_coordinate_torus_projection (n := d)).comp
    (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin d => ℝ))
theorem euclidean_torus_projection_is_open_quotient : IsOpenQuotientMap (euclideanTorusProjection (d := d)) := by
  unfold euclideanTorusProjection
  exact IsOpenQuotientMap.comp (UnitAddTorus.coordinate_torus_projection_is_open_quotient d)
    (PiLp.homeomorph (p := (2 : ENNReal)) (β := fun _ : Fin d => ℝ)).isOpenQuotientMap
@[simp]
theorem torus_projection_add_integer_vector (x : (EuclideanSpace ℝ (Fin d))) (n : Fin d → ℤ) :
    euclideanTorusProjection (d := d) (x + SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n) =
      euclideanTorusProjection (d := d) x := by
  ext i
  simp [euclideanTorusProjection, UnitAddTorus.coordinateTorusProjection]
theorem equal_torus_projections_differ_by_integer_vector {x y : (EuclideanSpace ℝ (Fin d))}
    (h : euclideanTorusProjection (d := d) x = euclideanTorusProjection (d := d) y) :
    ∃ n : Fin d → ℤ, x - y = SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n := by
  have hcoord : ∀ i : Fin d, ∃ n : ℤ, (n : ℝ) = (x i - y i : ℝ) := by
    intro i
    have hsub : ((x i - y i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      simpa [UnitAddCircle, AddCircle.coe_sub, euclideanTorusProjection, UnitAddTorus.coordinateTorusProjection] using!
        sub_eq_zero.2 (congrArg (fun t => t i) h)
    rcases (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := (x i - y i : ℝ))).1 hsub with ⟨n, hn⟩
    exact ⟨n, by simpa using! hn⟩
  choose n hn using hcoord
  refine ⟨n, ?_⟩
  ext i
  simp [SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector, hn i]
end SchwartzMap.PoissonSummation.Standard
end
section
open scoped BigOperators FourierTransform
open MeasureTheory
namespace SchwartzMap.PoissonSummation.Standard
variable {d : ℕ}
open UnitAddTorus
noncomputable def integerVectorLatticeEquiv : (Fin d → ℤ) ≃ (SchwartzMap.referenceIntegerLattice d) := by
  refine Equiv.ofBijective
    (fun n : Fin d → ℤ =>
      ⟨SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n,
        SchwartzMap.PoissonSummation.Standard.embedded_integer_vector_mem_reference_lattice (d := d) n⟩)
    ?_
  refine ⟨?_, ?_⟩
  · intro a b hab
    have hab' :
        SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) a =
          SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) b := by
      simpa using! congrArg Subtype.val hab
    funext i
    have := congrArg (fun x : (EuclideanSpace ℝ (Fin d)) => x i) hab'
    simpa [SchwartzMap.PoissonSummation.Standard.embedded_integer_vector_coordinate] using! this
  · intro ℓ
    rcases
        SchwartzMap.PoissonSummation.Standard.reference_lattice_element_eq_integer_vector (d := d)
          (x := (ℓ : (EuclideanSpace ℝ (Fin d)))) ℓ.property with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    simpa using! hn.symm
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
instance instMeasurableReferenceLatticeTranslation :
    MeasurableVAdd (SchwartzMap.referenceIntegerLattice d) (EuclideanSpace ℝ (Fin d)) := by
  refine { measurable_const_vadd := ?_, measurable_vadd_const := ?_ }
  · intro c
    simpa [Submodule.vadd_def, vadd_eq_add] using! (continuous_const.add continuous_id).measurable
  · intro x
    simpa [Submodule.vadd_def, vadd_eq_add] using!
      (continuous_subtype_val.add continuous_const).measurable
instance instReferenceLatticeTranslationInvariantVolume :
    MeasureTheory.VAddInvariantMeasure (SchwartzMap.referenceIntegerLattice d) (EuclideanSpace ℝ (Fin d)) (volume : Measure (EuclideanSpace ℝ (Fin d))) where
  measure_preimage_vadd c s hs := by
    simp [Submodule.vadd_def, vadd_eq_add, MeasureTheory.measure_preimage_add]
noncomputable def latticeTranslatedMap (ℓ : (SchwartzMap.referenceIntegerLattice d)) : C((EuclideanSpace ℝ (Fin d)), ℂ) :=
  (⟨(fun x => f x), f.continuous⟩ : C((EuclideanSpace ℝ (Fin d)), ℂ)).comp (ContinuousMap.addRight (ℓ : (EuclideanSpace ℝ (Fin d))))
lemma finite_reference_lattice_points_of_norm_bound (r : ℝ) :
    ( {ℓ : (SchwartzMap.referenceIntegerLattice d) | ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ r} : Set _ ).Finite := by
  haveI : DiscreteTopology (((SchwartzMap.referenceIntegerLattice d)).toAddSubgroup) := (inferInstance : DiscreteTopology (SchwartzMap.referenceIntegerLattice d))
  have hfinE : Set.Finite (Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) r ∩ (((SchwartzMap.referenceIntegerLattice d)).toAddSubgroup : Set (EuclideanSpace ℝ (Fin d)))) :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall AddSubgroup.isClosed_of_discrete
  let e : (SchwartzMap.referenceIntegerLattice d) ↪ (EuclideanSpace ℝ (Fin d)) := ⟨fun ℓ => (ℓ : (EuclideanSpace ℝ (Fin d))), Subtype.coe_injective⟩
  have hfin_pre : (e ⁻¹' (Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) r ∩ ((SchwartzMap.referenceIntegerLattice d) : Set (EuclideanSpace ℝ (Fin d))))).Finite := by
    simpa using! Set.Finite.preimage_embedding e (by
      simpa [Submodule.coe_toAddSubgroup] using! hfinE)
  have :
      (e ⁻¹' (Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) r ∩ ((SchwartzMap.referenceIntegerLattice d) : Set (EuclideanSpace ℝ (Fin d))))) = {ℓ : (SchwartzMap.referenceIntegerLattice d) | ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ r} := by
    ext ℓ
    simp [e, Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_zero]
  simpa [this] using! hfin_pre
lemma summable_restricted_lattice_translate_norms (K : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin d))) :
    Summable (fun ℓ : (SchwartzMap.referenceIntegerLattice d) => ‖(latticeTranslatedMap (d := d) f ℓ).restrict K‖) := by
  let k : ℕ := Module.finrank ℤ (SchwartzMap.referenceIntegerLattice d) + 1
  obtain ⟨C, hCpos, hC⟩ := f.decay k 0
  have hC' : ∀ x : (EuclideanSpace ℝ (Fin d)), ‖x‖ ^ k * ‖f x‖ ≤ C := by
    simpa [norm_iteratedFDeriv_zero] using! hC
  obtain ⟨r, hrK⟩ := K.isCompact.isBounded.subset_closedBall (0 : (EuclideanSpace ℝ (Fin d)))
  let r0 : ℝ := max r 0
  have hrK0 : (K : Set (EuclideanSpace ℝ (Fin d))) ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) r0 := by
    have hr_le : r ≤ r0 := le_max_left r 0
    have hball : Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) r ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) r0 :=
      Metric.closedBall_subset_closedBall hr_le
    exact fun x hx => hball (hrK hx)
  let R : ℝ := max (2 * r0) 1
  have hfin :
      ( {ℓ : (SchwartzMap.referenceIntegerLattice d) | ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ R} : Set _ ).Finite :=
    finite_reference_lattice_points_of_norm_bound (d := d) (r := R)
  have h_event :
      ∀ᶠ ℓ : (SchwartzMap.referenceIntegerLattice d) in Filter.cofinite,
        ‖(latticeTranslatedMap (d := d) f ℓ).restrict K‖ ≤ (C * (2 ^ k : ℝ)) * (‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k) := by
    filter_upwards [hfin.eventually_cofinite_notMem] with ℓ hℓ
    have hRlt : R < ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ := lt_of_not_ge (by simpa using! hℓ)
    have hnorm_lt : 2 * r0 < ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ := lt_of_le_of_lt (le_max_left _ _) hRlt
    have hnorm_pos : 0 < ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ := lt_trans (by positivity) hRlt
    refine (ContinuousMap.norm_le _ (by positivity)).2 ?_
    rintro ⟨x, hxK⟩
    have hxball : (x : (EuclideanSpace ℝ (Fin d))) ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) r0 := hrK0 hxK
    have hxnorm : ‖(x : (EuclideanSpace ℝ (Fin d)))‖ ≤ r0 := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_zero] using! hxball
    have hnorm_ge : (1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ ‖(x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ := by
      have hsub : ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ - ‖(x : (EuclideanSpace ℝ (Fin d)))‖ ≤ ‖(ℓ : (EuclideanSpace ℝ (Fin d))) + x‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using! (norm_sub_norm_le (ℓ : (EuclideanSpace ℝ (Fin d))) (-x))
      have hxlt : ‖(x : (EuclideanSpace ℝ (Fin d)))‖ < (1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ := by
        grind
      have : (1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ - ‖(x : (EuclideanSpace ℝ (Fin d)))‖ := by
        nlinarith [le_of_lt hxlt]
      have : (1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ ‖(ℓ : (EuclideanSpace ℝ (Fin d))) + x‖ := le_trans this hsub
      simpa [add_comm, add_left_comm, add_assoc] using! this
    have hnorm_xℓ_pos : 0 < ‖(x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ :=
      (by positivity : 0 < (1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖).trans_le hnorm_ge
    have hpow_pos : 0 < ‖(x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ^ k := pow_pos hnorm_xℓ_pos _
    have hdiv : ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ≤ C / (‖(x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ^ k) :=
      (le_div_iff₀' hpow_pos).2 (hC' (x + (ℓ : (EuclideanSpace ℝ (Fin d)))))
    have hpow_le : C / (‖(x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ^ k) ≤ (C * (2 ^ k : ℝ)) * (‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k) := by
      have hpow_ge : ((1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖) ^ k ≤ ‖(x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ^ k :=
        pow_le_pow_left₀ (by positivity) hnorm_ge _
      have hinv :
          (‖(x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ^ k)⁻¹ ≤ (2 ^ k : ℝ) * (‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k) := by
        have hapos : 0 < ((1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖) ^ k := by
          exact pow_pos (mul_pos (by positivity) hnorm_pos) _
        have :
            (‖(x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ^ k)⁻¹ ≤ (((1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖) ^ k)⁻¹ := by
          simpa [one_div] using! (one_div_le_one_div_of_le hapos hpow_ge)
        simpa [mul_assoc, mul_comm, inv_pow, mul_inv_rev, mul_pow] using! this
      have := mul_le_mul_of_nonneg_left hinv (le_of_lt hCpos)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! this
    have : ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ≤ (C * (2 ^ k : ℝ)) * (‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k) :=
      le_trans hdiv hpow_le
    simpa [latticeTranslatedMap, ContinuousMap.restrict_apply, ContinuousMap.comp_apply] using! this
  have hsum_pow : Summable (fun ℓ : (SchwartzMap.referenceIntegerLattice d) => (‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k : ℝ)) := by
    simpa [k] using!
      (ZLattice.summable_norm_pow_inv (L := (SchwartzMap.referenceIntegerLattice d)) (n := k) (Nat.lt_succ_self _))
  have hsum_bd :
      Summable (fun ℓ : (SchwartzMap.referenceIntegerLattice d) => (C * (2 ^ k : ℝ)) * (‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k)) :=
    hsum_pow.mul_left (C * (2 ^ k : ℝ))
  refine Summable.of_norm_bounded_eventually hsum_bd ?_
  filter_upwards [h_event] with ℓ hℓ
  simpa [Real.norm_of_nonneg (by positivity)] using! hℓ
noncomputable def latticePeriodizedMap : C((EuclideanSpace ℝ (Fin d)), ℂ) :=
  ∑' ℓ : (SchwartzMap.referenceIntegerLattice d), latticeTranslatedMap (d := d) f ℓ
lemma lattice_periodized_map_apply (x : (EuclideanSpace ℝ (Fin d))) :
    latticePeriodizedMap (d := d) f x = ∑' ℓ : (SchwartzMap.referenceIntegerLattice d), f (x + (ℓ : (EuclideanSpace ℝ (Fin d)))) := by
  have hsum := ContinuousMap.summable_of_locally_summable_norm
    (summable_restricted_lattice_translate_norms (d := d) f)
  simpa [latticePeriodizedMap, translate_apply] using! (ContinuousMap.tsum_apply hsum x).symm
@[simp] lemma lattice_periodization_translation_invariant (x : (EuclideanSpace ℝ (Fin d))) (ℓ₀ : (SchwartzMap.referenceIntegerLattice d)) :
    latticePeriodizedMap (d := d) f (x + ℓ₀) = latticePeriodizedMap (d := d) f x := by
  simpa [lattice_periodized_map_apply (d := d) f, add_assoc] using!
    (Equiv.addLeft ℓ₀).tsum_eq fun ℓ => f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))
noncomputable def euclideanTorusProjectionContinuous : C((EuclideanSpace ℝ (Fin d)), UnitAddTorus (Fin d)) :=
  ⟨PoissonSummation.Standard.euclideanTorusProjection (d := d),
    PoissonSummation.Standard.continuous_euclidean_torus_projection (d := d)⟩
lemma continuous_torus_projection_is_quotient : Topology.IsQuotientMap (euclideanTorusProjectionContinuous (d := d)) := by
  let h := PoissonSummation.Standard.euclidean_torus_projection_is_open_quotient (d := d)
  simpa [euclideanTorusProjectionContinuous] using! h.isQuotientMap
lemma lattice_periodization_factors_through_torus :
    Function.FactorsThrough (latticePeriodizedMap (d := d) f) (euclideanTorusProjectionContinuous (d := d)) := by
  intro x y hxy
  rcases PoissonSummation.Standard.equal_torus_projections_differ_by_integer_vector (d := d) (x := x) (y := y)
      (by simpa [euclideanTorusProjectionContinuous] using! hxy) with ⟨n, hn⟩
  have hx : x = y + SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! congrArg (fun t => t + y) hn
  simpa [hx] using!
    (lattice_periodization_translation_invariant (d := d) (f := f) y
      ⟨SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n,
        SchwartzMap.PoissonSummation.Standard.embedded_integer_vector_mem_reference_lattice (d := d) n⟩)
noncomputable def torusDescendedPeriodization : C(UnitAddTorus (Fin d), ℂ) :=
  Topology.IsQuotientMap.lift
    (hf := continuous_torus_projection_is_quotient (d := d))
    (g := latticePeriodizedMap (d := d) f)
    (lattice_periodization_factors_through_torus (d := d) (f := f))
@[simp] lemma embedded_integer_vector_neg (n : Fin d → ℤ) :
    SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) (-n) =
      -SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n := by
  ext i
  simp [SchwartzMap.PoissonSummation.Standard.embedded_integer_vector_coordinate]
end SchwartzMap.PoissonSummation.Standard
namespace SchwartzMap.PoissonSummation.Standard
variable {d : ℕ}
open UnitAddTorus
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
noncomputable def ball : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin d)) :=
  ⟨Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) (Real.sqrt d), isCompact_closedBall (0 : (EuclideanSpace ℝ (Fin d))) (Real.sqrt d)⟩
end SchwartzMap.PoissonSummation.Standard
end
section
open scoped BigOperators FourierTransform Real
open MeasureTheory Module
namespace SchwartzMap
variable {d : ℕ}
noncomputable abbrev polarIntegerLattice (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) : Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  LinearMap.BilinForm.dualSubmodule (B := (innerₗ (EuclideanSpace ℝ (Fin d)) : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin d)))) L
noncomputable def integralLatticeCoordinateBasis (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L] :
    Basis (Fin d) ℤ L := by
  haveI : Module.Free ℤ L := by infer_instance
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b₀ := Module.Free.chooseBasis ℤ L
  have hfinrank : Module.finrank ℤ L = d := by
    have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by
      simp
    exact (ZLattice.rank (K := ℝ) (L := L)).trans hE
  let e : Module.Free.ChooseBasisIndex ℤ L ≃ Fin d :=
    Fintype.equivOfCardEq (by
      simpa [hfinrank] using!
        (Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := L)).symm)
  exact b₀.reindex e
noncomputable def realLatticeCoordinateBasis (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L] :
    Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  (integralLatticeCoordinateBasis (d := d) L).ofZLatticeBasis ℝ L
noncomputable def referenceEuclideanBasis : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
noncomputable def latticeCoordinateEquiv (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L] :
    (EuclideanSpace ℝ (Fin d)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) :=
  (referenceEuclideanBasis (d := d)).equiv (realLatticeCoordinateBasis (d := d) L) (Equiv.refl (Fin d))
@[simp] lemma lattice_coordinate_equiv_apply_reference_basis (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : Fin d) : (latticeCoordinateEquiv (d := d) L) ((referenceEuclideanBasis (d := d)) i) = (realLatticeCoordinateBasis (d := d) L) i := by
  simpa [latticeCoordinateEquiv, referenceEuclideanBasis, realLatticeCoordinateBasis] using!
    (Basis.equiv_apply (b := referenceEuclideanBasis (d := d)) (b' := realLatticeCoordinateBasis (d := d) L) (e := Equiv.refl _)
      (i := i))
lemma coordinate_transport_maps_reference_lattice (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L] :
    Submodule.map ((latticeCoordinateEquiv (d := d) L).toLinearMap.restrictScalars ℤ)
        (SchwartzMap.referenceIntegerLattice d) = L := by
  have hspan : Submodule.span ℤ (Set.range (realLatticeCoordinateBasis (d := d) L)) = L := by
    simpa [realLatticeCoordinateBasis] using!
      (Module.Basis.ofZLatticeBasis_span (K := ℝ) (L := L) (b := integralLatticeCoordinateBasis (d := d) L))
  have himage :
      (fun a : (EuclideanSpace ℝ (Fin d)) => (latticeCoordinateEquiv (d := d) L) a) '' (Set.range (referenceEuclideanBasis (d := d))) =
        Set.range (realLatticeCoordinateBasis (d := d) L) := by
    have hfun : (fun a : (EuclideanSpace ℝ (Fin d)) => (latticeCoordinateEquiv (d := d) L) a) ∘ referenceEuclideanBasis (d := d) = realLatticeCoordinateBasis (d := d) L := by
      funext i
      simp [Function.comp]
    simpa [hfun] using!
      (Set.range_comp (g := fun a : (EuclideanSpace ℝ (Fin d)) => (latticeCoordinateEquiv (d := d) L) a) (f := referenceEuclideanBasis (d := d))).symm
  calc
    Submodule.map ((latticeCoordinateEquiv (d := d) L).toLinearMap.restrictScalars ℤ) (SchwartzMap.referenceIntegerLattice d) =
        Submodule.span ℤ ((fun a : (EuclideanSpace ℝ (Fin d)) => (latticeCoordinateEquiv (d := d) L) a) '' Set.range (referenceEuclideanBasis (d := d))) := by
          simp [SchwartzMap.referenceIntegerLattice, referenceEuclideanBasis, Submodule.map_span]
    _ = Submodule.span ℤ (Set.range (realLatticeCoordinateBasis (d := d) L)) := by simp [himage]
    _ = L := by simp [hspan]
section FundamentalDomain
end FundamentalDomain
section CovolumeDet
variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]
end CovolumeDet
section PoissonSummationLattices
variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]
noncomputable def latticeCoordinateTransport : (EuclideanSpace ℝ (Fin d)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) := latticeCoordinateEquiv (d := d) L
noncomputable def dualCoordinateTransport : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) := ((latticeCoordinateTransport (d := d) (L := L)).symm.toLinearMap).adjoint
noncomputable def latticeCoordinateAdjoint : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) := ((latticeCoordinateTransport (d := d) (L := L)).toLinearMap).adjoint
noncomputable def referenceLatticeCoordinateEquiv : SchwartzMap.referenceIntegerLattice d ≃ₗ[ℤ] L :=
  (LinearEquiv.restrictScalars ℤ (latticeCoordinateTransport (d := d) (L := L))).ofSubmodules
    (SchwartzMap.referenceIntegerLattice d) L
    (by
      simpa [LinearEquiv.restrictScalars_apply] using! (coordinate_transport_maps_reference_lattice (d := d) L))
@[simp]
lemma reference_lattice_coordinate_equiv_apply (x : SchwartzMap.referenceIntegerLattice d) :
    ((referenceLatticeCoordinateEquiv (d := d) L x : L) : (EuclideanSpace ℝ (Fin d))) = (latticeCoordinateTransport (d := d) (L := L)) x := by
  simp [referenceLatticeCoordinateEquiv]
lemma dual_transport_comp_coordinate_adjoint :
    (dualCoordinateTransport (d := d) L ∘ₗ latticeCoordinateAdjoint (d := d) L) = (LinearMap.id : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) := by
  let Amap : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) := (latticeCoordinateTransport (d := d) (L := L)).toLinearMap
  let Bmap : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) := (latticeCoordinateTransport (d := d) (L := L)).symm.toLinearMap
  have hcomp : Amap ∘ₗ Bmap = (LinearMap.id : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) := by
    ext x
    simp [Amap, Bmap]
  calc
    dualCoordinateTransport (d := d) L ∘ₗ latticeCoordinateAdjoint (d := d) L = Bmap.adjoint ∘ₗ Amap.adjoint := by
      simp [dualCoordinateTransport, latticeCoordinateAdjoint, Amap, Bmap]
    _ = (Amap ∘ₗ Bmap).adjoint := by
      exact (LinearMap.adjoint_comp Amap Bmap).symm
    _ = (LinearMap.id : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) := by simp [hcomp]
lemma coordinate_adjoint_comp_dual_transport :
    (latticeCoordinateAdjoint (d := d) L ∘ₗ dualCoordinateTransport (d := d) L) = (LinearMap.id : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) := by
  let Amap : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) := (latticeCoordinateTransport (d := d) (L := L)).toLinearMap
  let Bmap : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) := (latticeCoordinateTransport (d := d) (L := L)).symm.toLinearMap
  have hcomp : Bmap ∘ₗ Amap = (LinearMap.id : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) := by
    ext x
    simp [Amap, Bmap]
  calc
    latticeCoordinateAdjoint (d := d) L ∘ₗ dualCoordinateTransport (d := d) L = Amap.adjoint ∘ₗ Bmap.adjoint := by
      simp [dualCoordinateTransport, latticeCoordinateAdjoint, Amap, Bmap]
    _ = (Bmap ∘ₗ Amap).adjoint := by
      exact (LinearMap.adjoint_comp Bmap Amap).symm
    _ = (LinearMap.id : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) := by simp [hcomp]
noncomputable def dualAdjointCoordinateEquiv : (EuclideanSpace ℝ (Fin d)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) :=
  { toLinearMap := dualCoordinateTransport (d := d) L
    invFun := latticeCoordinateAdjoint (d := d) L
    left_inv := by
      intro x
      have h := coordinate_adjoint_comp_dual_transport (d := d) (L := L)
      simpa using! congrArg (fun f : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) => f x) h
    right_inv := by
      intro x
      have h := dual_transport_comp_coordinate_adjoint (d := d) (L := L)
      simpa using! congrArg (fun f : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) => f x) h }
lemma dual_coordinate_transport_maps_reference_lattice :
    Submodule.map ((dualCoordinateTransport (d := d) L).restrictScalars ℤ) (referenceIntegerLattice d) =
      polarIntegerLattice (d := d) L := by
  ext x
  have hdualStd : polarIntegerLattice (d := d) (referenceIntegerLattice d) = referenceIntegerLattice d := by
    simpa [polarIntegerLattice] using! (PoissonSummation.Standard.reference_lattice_dual_self (d := d))
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro z hz
    rcases (show (z : (EuclideanSpace ℝ (Fin d))) ∈
        Submodule.map ((latticeCoordinateTransport (d := d) L).toLinearMap.restrictScalars ℤ) (referenceIntegerLattice d) by
      simpa [latticeCoordinateTransport, coordinate_transport_maps_reference_lattice (d := d) L] using! hz) with ⟨w, hw, rfl⟩
    have hydual : y ∈ polarIntegerLattice (d := d) (referenceIntegerLattice d) := by
      simpa [hdualStd] using! hy
    have hinter :
        inner ℝ ((dualCoordinateTransport (d := d) L) y) ((latticeCoordinateTransport (d := d) (L := L)) w) = inner ℝ y w := by
      simpa [dualCoordinateTransport, latticeCoordinateTransport] using!
        (LinearMap.adjoint_inner_left ((latticeCoordinateTransport (d := d) (L := L)).symm.toLinearMap)
          ((latticeCoordinateTransport (d := d) (L := L)) w) y)
    simpa [polarIntegerLattice, innerₗ_apply_apply, hinter] using! hydual w hw
  · intro hx
    refine ⟨(latticeCoordinateAdjoint (d := d) L) x, ?_, ?_⟩
    · have hydual : (latticeCoordinateAdjoint (d := d) L) x ∈ polarIntegerLattice (d := d) (referenceIntegerLattice d) := by
        intro w hw
        have hwL : (latticeCoordinateTransport (d := d) (L := L)) w ∈ L := by
          have : (latticeCoordinateTransport (d := d) (L := L)) w ∈
              Submodule.map (((latticeCoordinateTransport (d := d) (L := L)).toLinearMap).restrictScalars ℤ)
                (referenceIntegerLattice d) :=
            ⟨w, hw, rfl⟩
          simpa [latticeCoordinateTransport, coordinate_transport_maps_reference_lattice (d := d) L] using! this
        have hinner :
            inner ℝ ((latticeCoordinateAdjoint (d := d) L) x) w = inner ℝ x ((latticeCoordinateTransport (d := d) (L := L)) w) := by
          simpa [latticeCoordinateAdjoint, latticeCoordinateTransport] using!
            (LinearMap.adjoint_inner_left ((latticeCoordinateTransport (d := d) (L := L)).toLinearMap) w x)
        simpa [polarIntegerLattice, innerₗ_apply_apply, hinner] using!
          hx ((latticeCoordinateTransport (d := d) (L := L)) w) hwL
      simpa [hdualStd] using! hydual
    ·
      have h := dual_transport_comp_coordinate_adjoint (d := d) (L := L)
      simpa using! congrArg (fun f : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) => f x) h
noncomputable def referenceLatticePolarEquiv :
    SchwartzMap.referenceIntegerLattice d ≃ₗ[ℤ] polarIntegerLattice (d := d) L :=
  (LinearEquiv.restrictScalars ℤ (dualAdjointCoordinateEquiv (d := d) (L := L))).ofSubmodules
    (SchwartzMap.referenceIntegerLattice d) (polarIntegerLattice (d := d) L)
    (by
      simpa [LinearEquiv.restrictScalars_apply] using!
        (dual_coordinate_transport_maps_reference_lattice (d := d) (L := L)))
noncomputable def integerVectorPolarLatticeEquiv : (Fin d → ℤ) ≃ polarIntegerLattice (d := d) L :=
  (PoissonSummation.Standard.integerVectorLatticeEquiv (d := d)).trans
    (referenceLatticePolarEquiv (d := d) L).toEquiv
@[simp]
lemma reference_lattice_polar_equiv_apply (x : SchwartzMap.referenceIntegerLattice d) :
    ((referenceLatticePolarEquiv (d := d) L x : polarIntegerLattice (d := d) L) : (EuclideanSpace ℝ (Fin d))) =
      (dualCoordinateTransport (d := d) L) x := by simp [referenceLatticePolarEquiv, dualAdjointCoordinateEquiv]
@[simp]
lemma integer_vector_polar_equiv_coe (n : Fin d → ℤ) :
    ((integerVectorPolarLatticeEquiv (d := d) L n : polarIntegerLattice (d := d) L) : (EuclideanSpace ℝ (Fin d))) =
      (dualCoordinateTransport (d := d) L) (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n) := by
  simp [integerVectorPolarLatticeEquiv, PoissonSummation.Standard.integerVectorLatticeEquiv]
end SchwartzMap.PoissonSummationLattices
end
section
variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
instance instNonemptyFinOfPositiveDimension : Nonempty (Fin d) := ⟨0, Fact.out⟩
noncomputable section
open scoped BigOperators FourierTransform
namespace SchwartzMap
section FourierSchwartz
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
  (f : 𝓢(V, E))
@[simp]
theorem schwartz_fourier_inverse_identity : 𝓕⁻ (𝓕 ⇑f) = f := by
  simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] using
    congrArg (fun g : 𝓢(V, E) => (g : V → E))
      (show (𝓕⁻ (𝓕 f : 𝓢(V, E)) : 𝓢(V, E)) = f from
        FourierTransform.fourierInv_fourier_eq f)
end FourierSchwartz
end SchwartzMap
section Positivity_on_Nhd
variable {E : Type*} [TopologicalSpace E]
open MeasureTheory
variable [MeasureSpace E] [BorelSpace E]
end Positivity_on_Nhd
section Integration
open MeasureTheory Filter
variable {E : Type*} [NormedAddCommGroup E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [MeasureSpace E] [BorelSpace E]
variable [(volume : Measure E).IsAddLeftInvariant] [(volume : Measure E).Regular]
  [NeZero (volume : Measure E)]
instance : (volume : Measure E).IsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_regular
end Integration
section Misc
instance : DecidableEq (EuclideanSpace ℝ (Fin d)) := inferInstance
omit [Fact (0 < d)]
end Misc
end
end
section
open scoped RealInnerProductSpace
open Module
namespace SpherePacking.CohnElkies
variable {d : ℕ}
instance (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] :
    DiscreteTopology
      (LinearMap.BilinForm.dualSubmodule (B := innerₗ (EuclideanSpace ℝ (Fin d))) Λ) := by
  let ι := Module.Free.ChooseBasisIndex ℤ Λ
  let bZ : Basis ι ℤ Λ := Module.Free.chooseBasis ℤ Λ
  let bR : Basis ι ℝ (EuclideanSpace ℝ (Fin d)) := bZ.ofZLatticeBasis ℝ Λ
  have hB :
      LinearMap.BilinForm.Nondegenerate (innerₗ (EuclideanSpace ℝ (Fin d)) :
        LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin d))) := by
    constructor <;> intro x hx
    all_goals
      have : ⟪x, x⟫ = (0 : ℝ) := by
        simpa [innerₗ_apply_apply] using! hx x
      exact inner_self_eq_zero.1 this
  have hdual :
      LinearMap.BilinForm.dualSubmodule (B := innerₗ (EuclideanSpace ℝ (Fin d))) Λ =
        Submodule.span ℤ
          (Set.range
            (LinearMap.BilinForm.dualBasis
              (B := innerₗ (EuclideanSpace ℝ (Fin d))) hB bR)) := by
    simpa [bR, bZ.ofZLatticeBasis_span (K := ℝ) (L := Λ)] using!
      (LinearMap.BilinForm.dualSubmodule_span_of_basis (B := innerₗ (EuclideanSpace ℝ (Fin d)))
        (R := ℤ) (S := ℝ) (M := EuclideanSpace ℝ (Fin d)) hB bR)
  exact hdual ▸
    (inferInstance :
      DiscreteTopology (Submodule.span ℤ
        (Set.range
          (LinearMap.BilinForm.dualBasis (B := innerₗ (EuclideanSpace ℝ (Fin d))) hB bR))))
end SpherePacking.CohnElkies
end
section
open scoped SchwartzMap
open scoped FourierTransform
open BigOperators
namespace SpherePacking.CohnElkies
variable {d : ℕ}
namespace LPBoundAux
section ZLatticeSummability
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
end SpherePacking.CohnElkies.LPBoundAux.ZLatticeSummability
end
section
open scoped Real
open scoped SchwartzMap FourierTransform
namespace SpherePacking.CohnElkies
noncomputable def centerFourierExponentialSum {d : ℕ} (P : PeriodicSpherePacking d)
    (D : Set (EuclideanSpace ℝ (Fin d))) :
    ↥(SchwartzMap.polarIntegerLattice (d := d) P.lattice) → ℂ :=
  fun m =>
    ∑' x : ↑(P.centers ∩ D),
      Complex.exp (2 * π * Complex.I * ⟪(x : EuclideanSpace ℝ (Fin d)),
        (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])
end SpherePacking.CohnElkies
end
section
open scoped BigOperators FourierTransform SchwartzMap Real
open Complex MeasureTheory
namespace SpherePacking.CohnElkies
variable {d : ℕ}
end SpherePacking.CohnElkies
end
section
open scoped BigOperators
open scoped SchwartzMap
namespace SpherePacking.CohnElkies
variable {d : ℕ}
namespace LPBoundSummability
open SpherePacking.CohnElkies.LPBoundAux
section ZLattice
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (a : EuclideanSpace ℝ (Fin d))
end SpherePacking.CohnElkies.LPBoundSummability.ZLattice
end
section
namespace SpherePacking.CohnElkies
noncomputable section
open scoped BigOperators SchwartzMap
variable {d : ℕ}
def fundamentalCentersLatticeProductEquiv (P : PeriodicSpherePacking d) [Nonempty P.centers]
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) :
    (↑(P.centers ∩ D) × P.lattice) ≃ P.centers := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  refine
    { toFun := fun z =>
        ⟨(z.2 : E) + (z.1 : E),
          P.lattice_action z.2.property z.1.property.1⟩
      invFun := fun x =>
        let g := Classical.choose (hD_unique_covers (x : E))
        (⟨(g : E) + (x : E),
            P.lattice_action g.property x.property,
            (Classical.choose_spec (hD_unique_covers (x : E))).1⟩,
          -g)
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨x, g⟩
    let k := Classical.choose (hD_unique_covers ((g : E) + (x : E)))
    have hk : k = -g := by
      symm
      apply (Classical.choose_spec
        (hD_unique_covers ((g : E) + (x : E)))).2
      simpa [Submodule.vadd_def, vadd_eq_add, add_assoc] using x.property.2
    change
      (⟨(k : E) + ((g : E) + (x : E)), _⟩, -k) = (x, g)
    apply Prod.ext
    · apply Subtype.ext
      change (k : E) + ((g : E) + (x : E)) = (x : E)
      simp [hk]
    · change -k = g
      simp [hk]
  · intro x
    let g := Classical.choose (hD_unique_covers (x : E))
    change
      (⟨((-g : P.lattice) : E) + ((g : E) + (x : E)), _⟩ : P.centers) = x
    apply Subtype.ext
    simp
end
end SpherePacking.CohnElkies
end
section
open scoped BigOperators SchwartzMap
namespace SpherePacking.CohnElkies
variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}
section FundamentalDomain
variable {P : PeriodicSpherePacking d}
variable {D : Set (EuclideanSpace ℝ (Fin d))}
end FundamentalDomain
end SpherePacking.CohnElkies
end
section
open scoped FourierTransform ENNReal SchwartzMap BigOperators
open SpherePacking MeasureTheory Complex Real Bornology Module
variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
section Complex_Function_Helpers
theorem imaginary_part_vanishes_of_real_valued (g : EuclideanSpace ℝ (Fin d) → ℂ) :
  (∀ x : EuclideanSpace ℝ (Fin d), ↑(g x).re = (g x)) →
  (∀ x : EuclideanSpace ℝ (Fin d), (g x).im = 0) := by
  intro hIsReal x
  simpa [eq_comm] using! congrArg Complex.im (hIsReal x)
include hRealFourier in
@[simp]
theorem fourier_imaginary_component_vanishes : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).im = 0 :=
  imaginary_part_vanishes_of_real_valued (𝓕 ⇑f) hRealFourier
end Complex_Function_Helpers
section Nonnegativity
end Nonnegativity
section Fundamental_Domain_Dependent
variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
end Fundamental_Domain_Dependent
section Main_Theorem_For_One_Packing
variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ P hP D hD_isBounded
  hD_unique_covers
end Main_Theorem_For_One_Packing
section Main_Theorem
include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂
end Main_Theorem
end
end
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped FourierTransform SchwartzMap Topology
namespace PackingBounds.RadialMain
end PackingBounds.RadialMain
end
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal FourierTransform SchwartzMap Topology
namespace PackingBounds.PackingBridge
end PackingBounds.PackingBridge
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap Topology
namespace PackingBounds
structure FullAdmissible (d : ℕ) where
  function : CohnElkies.TestFunction d
  real : ∀ x : CohnElkies.Euclidean d, (function x).im = 0
  fourier_real :
    ∀ x : CohnElkies.Euclidean d, ((𝓕 function) x).im = 0
  fourier_nonneg :
    ∀ x : CohnElkies.Euclidean d, 0 ≤ ((𝓕 function) x).re
  fourier_zero_pos :
    0 < ((𝓕 function) (0 : CohnElkies.Euclidean d)).re
  outside_nonpos :
    ∀ x : CohnElkies.Euclidean d, 1 ≤ ‖x‖ → (function x).re ≤ 0
def fullQuotient {d : ℕ} (f : FullAdmissible d) : ℝ :=
  (f.function (0 : CohnElkies.Euclidean d)).re /
    ((𝓕 f.function) (0 : CohnElkies.Euclidean d)).re
def fullQuotientSet (d : ℕ) : Set ℝ :=
  Set.range (fullQuotient (d := d))
def fullLinearProgram (d : ℕ) : ℝ :=
  CohnElkies.unitBallVolume d / (2 : ℝ) ^ d *
    sInf (fullQuotientSet d)
def radialToFull {d : ℕ}
    (f : CohnElkies.Admissible d) : FullAdmissible d where
  function := f.function
  real := f.real
  fourier_real := f.fourier_real
  fourier_nonneg := f.fourier_nonneg
  fourier_zero_pos := f.fourier_zero_pos
  outside_nonpos := f.outside_nonpos
end PackingBounds
end
end
noncomputable section
open scoped FourierTransform Real Topology
namespace SpherePacking.Alternative
abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Schwartz (d : ℕ) := SchwartzMap (Ambient d) ℂ
def IsRealValued {d : ℕ} (f : Schwartz d) : Prop :=
  ∀ x, (f x).im = 0
def IsRadial {d : ℕ} (f : Schwartz d) : Prop :=
  ∀ x y : Ambient d, ‖x‖ = ‖y‖ → f x = f y
def fourierReal {d : ℕ} (f : Schwartz d) (x : Ambient d) : ℝ :=
  ((𝓕 f : Schwartz d) x).re
structure IsAdmissible {d : ℕ} (f : Schwartz d) : Prop where
  real_valued : IsRealValued f
  radial : IsRadial f
  fourier_real_valued : IsRealValued (𝓕 f : Schwartz d)
  fourier_zero_pos : 0 < fourierReal f 0
  fourier_nonneg : ∀ x, 0 ≤ fourierReal f x
  eventually_nonpos : ∀ x : Ambient d, 1 ≤ ‖x‖ → (f x).re ≤ 0
def quotient {d : ℕ} (f : Schwartz d) : ℝ :=
  (f 0).re / fourierReal f 0
end SpherePacking.Alternative
end
noncomputable section
open Set Matrix MeasureTheory
namespace SpherePacking.Alternative
abbrev OrthogonalGroup (d : ℕ) := Matrix.orthogonalGroup (Fin d) ℝ
theorem orthogonal_entry_abs_le_one {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin d) ℝ) (i j : Fin d) :
    |A i j| ≤ (1 : ℝ) := by
  have hdiag := congrArg (fun B : Matrix (Fin d) (Fin d) ℝ => B i i)
    ((Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).mp hA)
  have hsum : (∑ k : Fin d, A i k * A i k) = (1 : ℝ) := by
    simpa [Matrix.mul_apply] using hdiag
  have hterm : A i j * A i j ≤ ∑ k : Fin d, A i k * A i k := by
    exact Finset.single_le_sum (fun k _ => mul_self_nonneg (A i k))
      (Finset.mem_univ j)
  exact (abs_le_one_iff_mul_self_le_one).2 (hterm.trans_eq hsum)
theorem orthogonal_isCompact (d : ℕ) :
    IsCompact (Matrix.orthogonalGroup (Fin d) ℝ :
      Set (Matrix (Fin d) (Fin d) ℝ)) := by
  refine ((isCompact_Icc (a := (-1 : ℝ)) (b := (1 : ℝ))).matrix).of_isClosed_subset
    isClosed_unitary ?_
  intro A hA
  change ∀ i j, A i j ∈ Set.Icc (-1 : ℝ) 1
  intro i j
  exact abs_le.mp (orthogonal_entry_abs_le_one hA i j)
instance orthogonalGroupCompactSpace (d : ℕ) :
    CompactSpace (OrthogonalGroup d) :=
  isCompact_iff_compactSpace.mp (orthogonal_isCompact d)
instance orthogonalGroupMeasurableSpace (d : ℕ) :
    MeasurableSpace (OrthogonalGroup d) :=
  borel (OrthogonalGroup d)
instance orthogonalGroupBorelSpace (d : ℕ) :
    BorelSpace (OrthogonalGroup d) :=
  ⟨rfl⟩
def orthogonalAction {d : ℕ} (U : OrthogonalGroup d) (x : Ambient d) : Ambient d :=
  Matrix.toLpLin 2 2 (U : Matrix (Fin d) (Fin d) ℝ) x
@[simp] theorem orthogonalAction_one {d : ℕ} (x : Ambient d) :
    orthogonalAction (1 : OrthogonalGroup d) x = x := by
  change Matrix.toLpLin 2 2 (1 : Matrix (Fin d) (Fin d) ℝ) x = x
  rw [Matrix.toLpLin_one]
  rfl
@[simp] theorem orthogonalAction_mul {d : ℕ}
    (U V : OrthogonalGroup d) (x : Ambient d) :
    orthogonalAction (U * V) x = orthogonalAction U (orthogonalAction V x) := by
  change Matrix.toLpLin 2 2
    ((U : Matrix (Fin d) (Fin d) ℝ) * (V : Matrix (Fin d) (Fin d) ℝ)) x =
      Matrix.toLpLin 2 2 (U : Matrix (Fin d) (Fin d) ℝ)
        (Matrix.toLpLin 2 2 (V : Matrix (Fin d) (Fin d) ℝ) x)
  rw [Matrix.toLpLin_mul_same]
  rfl
@[simp] theorem orthogonalAction_zero {d : ℕ} (U : OrthogonalGroup d) :
    orthogonalAction U (0 : Ambient d) = 0 := by
  exact map_zero (Matrix.toLpLin 2 2 (U : Matrix (Fin d) (Fin d) ℝ))
def orthogonalIsometryEquiv (d : ℕ) :
    OrthogonalGroup d ≃* (Ambient d ≃ₗᵢ[ℝ] Ambient d) :=
  (Unitary.mapEquiv (StarMulEquiv.ofClass
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)))).toMulEquiv.trans
      Unitary.linearIsometryEquiv
def orthogonalLinearIsometry {d : ℕ} (U : OrthogonalGroup d) :
    Ambient d ≃ₗᵢ[ℝ] Ambient d :=
  orthogonalIsometryEquiv d U
@[simp] theorem orthogonalLinearIsometry_apply {d : ℕ}
    (U : OrthogonalGroup d) (x : Ambient d) :
    orthogonalLinearIsometry U x = orthogonalAction U x := by
  rfl
theorem orthogonalAction_continuous {d : ℕ} (x : Ambient d) :
    Continuous (fun U : OrthogonalGroup d => orthogonalAction U x) := by
  change Continuous (fun U : OrthogonalGroup d =>
    WithLp.toLp 2 ((U : Matrix (Fin d) (Fin d) ℝ) *ᵥ WithLp.ofLp x))
  exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp
    (continuous_subtype_val.matrix_mulVec continuous_const)
theorem continuous_orthogonalAction_apply {d : ℕ} (x : Ambient d) :
    Continuous (fun U : OrthogonalGroup d => orthogonalAction U x) :=
  orthogonalAction_continuous x
theorem orthogonalAction_joint_continuous (d : ℕ) :
    Continuous (fun p : OrthogonalGroup d × Ambient d =>
      orthogonalAction p.1 p.2) := by
  change Continuous (fun p : OrthogonalGroup d × Ambient d =>
    WithLp.toLp 2
      (((p.1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ WithLp.ofLp p.2)))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
    ((continuous_subtype_val.comp continuous_fst).matrix_mulVec
      ((PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).comp continuous_snd))
def orthogonalMatrixOfIsometry {d : ℕ}
    (A : Ambient d ≃ₗᵢ[ℝ] Ambient d) : OrthogonalGroup d :=
  ⟨A.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis,
    A.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin d) ℝ)
      (EuclideanSpace.basisFun (Fin d) ℝ)⟩
@[simp] theorem orthogonalMatrixOfIsometry_action {d : ℕ}
    (A : Ambient d ≃ₗᵢ[ℝ] Ambient d) (x : Ambient d) :
    orthogonalAction (orthogonalMatrixOfIsometry A) x = A x := by
  change (Matrix.toLpLin 2 2)
    ((LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
      A.toLinearEquiv.toLinearMap) x = A x
  rw [Matrix.toLpLin_eq_toLin]
  change (Matrix.toLin (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
      ((LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
        A.toLinearEquiv.toLinearMap) x = A x
  rw [Matrix.toLin_toMatrix]
  rfl
theorem orthogonal_transitive {d : ℕ} {x y : Ambient d}
    (hxy : ‖x‖ = ‖y‖) :
    ∃ U : OrthogonalGroup d, orthogonalAction U x = y := by
  let A : Ambient d ≃ₗᵢ[ℝ] Ambient d :=
    Submodule.reflection (ℝ ∙ (x - y))ᗮ
  refine ⟨orthogonalMatrixOfIsometry A, ?_⟩
  rw [orthogonalMatrixOfIsometry_action]
  exact Submodule.reflection_sub hxy
def orthogonalPositiveCompacts (d : ℕ) :
    TopologicalSpace.PositiveCompacts (OrthogonalGroup d) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
def radialOrthogonalHaar (d : ℕ) : Measure (OrthogonalGroup d) :=
  Measure.haarMeasure (orthogonalPositiveCompacts d)
@[simp] theorem radialOrthogonalHaar_univ (d : ℕ) :
    radialOrthogonalHaar d Set.univ = 1 := by
  simpa [radialOrthogonalHaar, orthogonalPositiveCompacts] using
    (Measure.haarMeasure_self (K₀ := orthogonalPositiveCompacts d))
instance radialOrthogonalHaar_probability (d : ℕ) :
    IsProbabilityMeasure (radialOrthogonalHaar d) :=
  ⟨radialOrthogonalHaar_univ d⟩
instance radialOrthogonalHaar_isHaar (d : ℕ) :
    (radialOrthogonalHaar d).IsHaarMeasure := by
  unfold radialOrthogonalHaar
  infer_instance
instance radialOrthogonalHaar_leftInvariant (d : ℕ) :
    (radialOrthogonalHaar d).IsMulLeftInvariant := by
  unfold radialOrthogonalHaar
  infer_instance
instance radialOrthogonalHaar_finite (d : ℕ) :
    IsFiniteMeasure (radialOrthogonalHaar d) := by
  infer_instance
end SpherePacking.Alternative
end
noncomputable section
open Filter MeasureTheory
open scoped ContDiff Topology
namespace SpherePacking.Alternative
noncomputable def radialIsometrySchwartzOrbit {d : ℕ}
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Schwartz d) : Schwartz d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    U.toContinuousLinearEquiv f
@[simp]
theorem radialIsometrySchwartzOrbit_apply {d : ℕ}
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Schwartz d)
    (x : Ambient d) :
    radialIsometrySchwartzOrbit U f x = f (U x) := by
  rfl
@[simp]
theorem radialIsometrySchwartzOrbit_symm_apply {d : ℕ}
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Schwartz d) :
    radialIsometrySchwartzOrbit U.symm
      (radialIsometrySchwartzOrbit U f) = f := by
  ext x
  simp
theorem radialIsometrySchwartzOrbit_iteratedFDeriv_norm {d : ℕ}
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Schwartz d)
    (n : ℕ) (x : Ambient d) :
    ‖iteratedFDeriv ℝ n
        (radialIsometrySchwartzOrbit U f : Ambient d → ℂ) x‖ =
      ‖iteratedFDeriv ℝ n (f : Ambient d → ℂ) (U x)‖ := by
  change
    ‖iteratedFDeriv ℝ n
      ((f : Ambient d → ℂ) ∘ (U : Ambient d → Ambient d)) x‖ = _
  exact U.norm_iteratedFDeriv_comp_right (f : Ambient d → ℂ) x n
theorem radialIsometrySchwartzOrbit_iteratedFDeriv {d : ℕ}
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Schwartz d)
    (n : ℕ) (x : Ambient d) :
    iteratedFDeriv ℝ n
        (radialIsometrySchwartzOrbit U f : Ambient d → ℂ) x =
      (iteratedFDeriv ℝ n (f : Ambient d → ℂ) (U x)).compContinuousLinearMap
        (fun _ ↦ U.toContinuousLinearMap) := by
  change
    iteratedFDeriv ℝ n
        ((f : Ambient d → ℂ) ∘ (U : Ambient d → Ambient d)) x = _
  exact U.toContinuousLinearMap.iteratedFDeriv_comp_right
    (f.smooth ⊤) x (mod_cast le_top)
theorem radialIsometrySchwartzOrbit_weighted_iteratedFDeriv_le
    {d : ℕ} (U : Ambient d ≃ₗᵢ[ℝ] Ambient d)
    (f : Schwartz d) (k n : ℕ) (x : Ambient d) :
    ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (radialIsometrySchwartzOrbit U f : Ambient d → ℂ) x‖ ≤
      SchwartzMap.seminorm ℂ k n f := by
  rw [radialIsometrySchwartzOrbit_iteratedFDeriv_norm,
    ← U.norm_map x]
  exact SchwartzMap.le_seminorm ℂ k n f (U x)
theorem radialIsometrySchwartzOrbit_seminorm_le {d : ℕ}
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Schwartz d)
    (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (radialIsometrySchwartzOrbit U f) ≤
      SchwartzMap.seminorm ℂ k n f := by
  apply SchwartzMap.seminorm_le_bound ℂ k n
    (radialIsometrySchwartzOrbit U f)
    (apply_nonneg (SchwartzMap.seminorm ℂ k n) f)
  exact radialIsometrySchwartzOrbit_weighted_iteratedFDeriv_le U f k n
theorem radialIsometrySchwartzOrbit_seminorm_eq {d : ℕ}
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Schwartz d)
    (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (radialIsometrySchwartzOrbit U f) =
      SchwartzMap.seminorm ℂ k n f := by
  apply le_antisymm (radialIsometrySchwartzOrbit_seminorm_le U f k n)
  have h := radialIsometrySchwartzOrbit_seminorm_le U.symm
    (radialIsometrySchwartzOrbit U f) k n
  simpa using h
end SpherePacking.Alternative
end
noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Real Topology
namespace SpherePacking.Alternative
theorem orthogonalLinearIsometry_continuousLinearMap_continuous
    (d : ℕ) :
    Continuous (fun U : OrthogonalGroup d =>
      (orthogonalLinearIsometry U).toContinuousLinearMap) := by
  change Continuous (fun U : OrthogonalGroup d =>
    Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)
      (U : Matrix (Fin d) (Fin d) ℝ))
  exact
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap
      |>.continuous_of_finiteDimensional
      |>.comp continuous_subtype_val
theorem orthogonalSchwartzIteratedFDeriv_continuous
    {d : ℕ} (f : Schwartz d) (n : ℕ) (x : Ambient d) :
    Continuous (fun U : OrthogonalGroup d =>
      iteratedFDeriv ℝ n
        (radialIsometrySchwartzOrbit
          (orthogonalLinearIsometry U) f : Ambient d → ℂ) x) := by
  have hderiv :
      Continuous (fun U : OrthogonalGroup d =>
        iteratedFDeriv ℝ n (f : Ambient d → ℂ)
          (orthogonalAction U x)) :=
    ((f.smooth ⊤).continuous_iteratedFDeriv
      (mod_cast le_top)).comp (orthogonalAction_continuous x)
  have hmaps :
      Continuous (fun U : OrthogonalGroup d =>
        fun _ : Fin n =>
          (orthogonalLinearIsometry U).toContinuousLinearMap) :=
    continuous_pi fun _ =>
      orthogonalLinearIsometry_continuousLinearMap_continuous d
  have hcomp :
      Continuous
        (fun p :
          ContinuousMultilinearMap ℝ
              (fun _ : Fin n => Ambient d) ℂ ×
            (Fin n → Ambient d →L[ℝ] Ambient d) =>
          p.1.compContinuousLinearMap p.2) := by
    exact continuous_iff_continuousAt.2 fun p =>
      (ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
        p).continuousAt
  have h := hcomp.comp (hderiv.prodMk hmaps)
  simpa [Function.comp_def, radialIsometrySchwartzOrbit_iteratedFDeriv,
    orthogonalLinearIsometry_apply] using h
theorem orthogonalSchwartzInverseIteratedFDeriv_continuous
    {d : ℕ} (f : Schwartz d) (n : ℕ) (x : Ambient d) :
    Continuous (fun U : OrthogonalGroup d =>
      iteratedFDeriv ℝ n
        (radialIsometrySchwartzOrbit
          (orthogonalLinearIsometry U⁻¹) f : Ambient d → ℂ) x) :=
  (orthogonalSchwartzIteratedFDeriv_continuous f n x).comp continuous_inv
theorem orthogonalSchwartzInverseIteratedFDeriv_aestronglyMeasurable
    {d : ℕ} (f : Schwartz d) (n : ℕ) (x : Ambient d) :
    AEStronglyMeasurable
      (fun U : OrthogonalGroup d =>
        iteratedFDeriv ℝ n
          (radialIsometrySchwartzOrbit
            (orthogonalLinearIsometry U⁻¹) f : Ambient d → ℂ) x)
      (radialOrthogonalHaar d) :=
  (orthogonalSchwartzInverseIteratedFDeriv_continuous
    f n x).aestronglyMeasurable_of_compactSpace
end SpherePacking.Alternative
namespace SpherePacking.Alternative
section ProbabilityAverage
variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α) [IsProbabilityMeasure μ]
variable {d : ℕ} (g : α → Schwartz d) (C : ℕ → ℕ → ℝ)
theorem radialSchwartzParametricDerivativeIntegrable
    (hmeas : ∀ (n : ℕ) (x : Ambient d),
      AEStronglyMeasurable
        (fun a : α ↦ iteratedFDeriv ℝ n
          (g a : Ambient d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ),
      SchwartzMap.seminorm ℂ k n (g a) ≤ C k n)
    (n : ℕ) (x : Ambient d) :
    Integrable
      (fun a : α ↦ iteratedFDeriv ℝ n
        (g a : Ambient d → ℂ) x) μ := by
  apply Integrable.of_bound (hmeas n x) (C 0 n)
  filter_upwards [] with a
  exact
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (g a) n x).trans
      (hbound a 0 n)
theorem radialSchwartzParametric_hasFDerivAt_iteratedIntegral
    (hmeas : ∀ (n : ℕ) (x : Ambient d),
      AEStronglyMeasurable
        (fun a : α ↦ iteratedFDeriv ℝ n
          (g a : Ambient d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ),
      SchwartzMap.seminorm ℂ k n (g a) ≤ C k n)
    (n : ℕ) (x : Ambient d) :
    HasFDerivAt
      (fun y : Ambient d ↦
        ∫ a : α, iteratedFDeriv ℝ n
          (g a : Ambient d → ℂ) y ∂μ)
      (∫ a : α, fderiv ℝ
        (iteratedFDeriv ℝ n (g a : Ambient d → ℂ)) x ∂μ)
      x := by
  have hderiv_meas :
      AEStronglyMeasurable
        (fun a : α ↦
          fderiv ℝ
            (iteratedFDeriv ℝ n (g a : Ambient d → ℂ)) x) μ := by
    have h :=
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) ↦ Ambient d) ℂ).continuous.comp_aestronglyMeasurable
          (hmeas (n + 1) x)
    simpa only [fderiv_iteratedFDeriv, Function.comp_apply] using h
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ)
    (F := fun y : Ambient d ↦ fun a : α ↦
      iteratedFDeriv ℝ n (g a : Ambient d → ℂ) y)
    (F' := fun y : Ambient d ↦ fun a : α ↦
      fderiv ℝ (iteratedFDeriv ℝ n (g a : Ambient d → ℂ)) y)
    (bound := fun _ : α ↦ C 0 (n + 1))
    (s := Set.univ)
    Filter.univ_mem
    (Filter.Eventually.of_forall (fun y ↦ hmeas n y))
    (radialSchwartzParametricDerivativeIntegrable μ g C
      hmeas hbound n x)
    hderiv_meas
    (by
      filter_upwards [] with a y _
      calc
        ‖fderiv ℝ
          (iteratedFDeriv ℝ n (g a : Ambient d → ℂ)) y‖ =
          ‖iteratedFDeriv ℝ (n + 1)
            (g a : Ambient d → ℂ) y‖ :=
            norm_fderiv_iteratedFDeriv
        _ ≤ SchwartzMap.seminorm ℂ 0 (n + 1) (g a) :=
          SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ
            (g a) (n + 1) y
        _ ≤ C 0 (n + 1) := hbound a 0 (n + 1))
    (integrable_const (C 0 (n + 1)))
  filter_upwards [] with a y _
  exact
    (((g a).smooth ⊤).differentiable_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop
        (le_refl _) n)).differentiableAt.hasFDerivAt
theorem radialSchwartzParametric_iteratedFDeriv_integral
    (hmeas : ∀ (n : ℕ) (x : Ambient d),
      AEStronglyMeasurable
        (fun a : α ↦ iteratedFDeriv ℝ n
          (g a : Ambient d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ),
      SchwartzMap.seminorm ℂ k n (g a) ≤ C k n)
    (n : ℕ) (x : Ambient d) :
    iteratedFDeriv ℝ n
        (fun y : Ambient d ↦ ∫ a : α, (g a) y ∂μ) x =
      ∫ a : α, iteratedFDeriv ℝ n
        (g a : Ambient d → ℂ) x ∂μ := by
  induction n generalizing x with
  | zero =>
      ext v
      rw [ContinuousMultilinearMap.integral_apply
        (radialSchwartzParametricDerivativeIntegrable μ g C
          hmeas hbound 0 x)]
      simp
  | succ n ih =>
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      have hprevious :
          iteratedFDeriv ℝ n
              (fun y : Ambient d ↦ ∫ a : α, (g a) y ∂μ) =
            fun y : Ambient d ↦
              ∫ a : α, iteratedFDeriv ℝ n
                (g a : Ambient d → ℂ) y ∂μ := by
        funext y
        exact ih y
      rw [hprevious,
        (radialSchwartzParametric_hasFDerivAt_iteratedIntegral
          μ g C hmeas hbound n x).fderiv]
      calc
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (n + 1) ↦ Ambient d) ℂ).symm
            (∫ a : α, fderiv ℝ
              (iteratedFDeriv ℝ n (g a : Ambient d → ℂ)) x ∂μ) =
            ∫ a : α,
              (continuousMultilinearCurryLeftEquiv ℝ
                (fun _ : Fin (n + 1) ↦ Ambient d) ℂ).symm
                  (fderiv ℝ
                    (iteratedFDeriv ℝ n (g a : Ambient d → ℂ)) x)
                  ∂μ := by
              exact
                (LinearIsometry.integral_comp_comm
                  (𝕜 := ℝ)
                  (LinearIsometryEquiv.toLinearIsometry
                    ((continuousMultilinearCurryLeftEquiv ℝ
                      (fun _ : Fin (n + 1) ↦ Ambient d) ℂ).symm))
                  (fun a : α ↦ fderiv ℝ
                    (iteratedFDeriv ℝ n
                      (g a : Ambient d → ℂ)) x)).symm
        _ = ∫ a : α, iteratedFDeriv ℝ (n + 1)
              (g a : Ambient d → ℂ) x ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with a
              rw [iteratedFDeriv_succ_eq_comp_left]
              rfl
end ProbabilityAverage
end SpherePacking.Alternative
end
noncomputable section
open MeasureTheory
open scoped Topology
namespace SpherePacking.Alternative
def radialSymmetrizationAverage {d : ℕ}
    (f : Schwartz d) (x : Ambient d) : ℂ :=
  ∫ U : OrthogonalGroup d,
    f (orthogonalAction U⁻¹ x) ∂radialOrthogonalHaar d
theorem radialSymmetrizationAverage_integrable {d : ℕ}
    (f : Schwartz d) (x : Ambient d) :
    Integrable (fun U : OrthogonalGroup d ↦
      f (orthogonalAction U⁻¹ x)) (radialOrthogonalHaar d) := by
  have hcontinuous : Continuous
      (fun U : OrthogonalGroup d ↦ f (orthogonalAction U⁻¹ x)) :=
    f.continuous.comp ((continuous_orthogonalAction_apply x).comp continuous_inv)
  simpa using hcontinuous.continuousOn.integrableOn_compact isCompact_univ
theorem radialSymmetrizationAverage_comp_orthogonal {d : ℕ}
    (f : Schwartz d) (A : OrthogonalGroup d) (x : Ambient d) :
    radialSymmetrizationAverage f (orthogonalAction A x) =
      radialSymmetrizationAverage f x := by
  unfold radialSymmetrizationAverage
  calc
    (∫ U : OrthogonalGroup d,
        f (orthogonalAction U⁻¹ (orthogonalAction A x))
          ∂radialOrthogonalHaar d) =
      ∫ U : OrthogonalGroup d,
        f (orthogonalAction (A * U)⁻¹ (orthogonalAction A x))
          ∂radialOrthogonalHaar d :=
      (integral_mul_left_eq_self
        (μ := radialOrthogonalHaar d)
        (fun U : OrthogonalGroup d ↦
          f (orthogonalAction U⁻¹ (orthogonalAction A x))) A).symm
    _ = ∫ U : OrthogonalGroup d,
        f (orthogonalAction U⁻¹ x) ∂radialOrthogonalHaar d := by
      apply integral_congr_ae
      filter_upwards with U
      simp only [mul_inv_rev, orthogonalAction_mul]
      rw [← orthogonalAction_mul A⁻¹ A x]
      simp
theorem radialSymmetrizationAverage_eq_of_norm_eq {d : ℕ}
    (f : Schwartz d) {x y : Ambient d} (hxy : ‖x‖ = ‖y‖) :
    radialSymmetrizationAverage f x = radialSymmetrizationAverage f y := by
  obtain ⟨A, hA⟩ := orthogonal_transitive hxy
  rw [← hA]
  exact (radialSymmetrizationAverage_comp_orthogonal f A x).symm
@[simp] theorem radialSymmetrizationAverage_zero {d : ℕ}
    (f : Schwartz d) :
    radialSymmetrizationAverage f 0 = f 0 := by
  simp [radialSymmetrizationAverage]
end SpherePacking.Alternative
end
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace SpherePacking.Alternative
theorem scalarProbabilityAverage_weighted_iteratedFDeriv_le
    {ι : Type*} [MeasurableSpace ι]
    (μ : Measure ι) [IsProbabilityMeasure μ]
    {d : ℕ} (F : ι → Schwartz d) (C : ℕ → ℕ → ℝ)
    (hbound : ∀ (k n : ℕ) (a : ι) (x : Ambient d),
      ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (fun y : Ambient d ↦ F a y) x‖ ≤ C k n)
    (hderiv : ∀ (n : ℕ) (x : Ambient d),
      iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ ∫ a, F a y ∂μ) x =
        ∫ a, iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ F a y) x ∂μ)
    (k n : ℕ) (x : Ambient d) :
    ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ ∫ a, F a y ∂μ) x‖ ≤ C k n := by
  rw [hderiv n x]
  calc
    ‖x‖ ^ k *
        ‖∫ a, iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ F a y) x ∂μ‖
        ≤ ‖x‖ ^ k *
          ∫ a, ‖iteratedFDeriv ℝ n
            (fun y : Ambient d ↦ F a y) x‖ ∂μ :=
          mul_le_mul_of_nonneg_left
            (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ a, ‖x‖ ^ k *
          ‖iteratedFDeriv ℝ n
            (fun y : Ambient d ↦ F a y) x‖ ∂μ := by
          rw [integral_const_mul]
    _ ≤ ∫ _a : ι, C k n ∂μ := by
          apply integral_mono_of_nonneg
          · exact Eventually.of_forall (fun _ ↦ by positivity)
          · exact integrable_const _
          · exact Eventually.of_forall (fun a ↦ hbound k n a x)
    _ = C k n := by simp
noncomputable def scalarProbabilitySchwartzAverage
    {ι : Type*} [MeasurableSpace ι]
    (μ : Measure ι) [IsProbabilityMeasure μ]
    {d : ℕ} (F : ι → Schwartz d) (C : ℕ → ℕ → ℝ)
    (hsmooth : ContDiff ℝ ∞
      (fun x : Ambient d ↦ ∫ a, F a x ∂μ))
    (hderiv : ∀ (n : ℕ) (x : Ambient d),
      iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ ∫ a, F a y ∂μ) x =
        ∫ a, iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ F a y) x ∂μ)
    (hbound : ∀ (k n : ℕ) (a : ι) (x : Ambient d),
      ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (fun y : Ambient d ↦ F a y) x‖ ≤ C k n) :
    Schwartz d where
  toFun x := ∫ a, F a x ∂μ
  smooth' := hsmooth
  decay' k n :=
    ⟨C k n,
      scalarProbabilityAverage_weighted_iteratedFDeriv_le
        μ F C hbound hderiv k n⟩
noncomputable def radialSymmetrization {d : ℕ}
    (f : Schwartz d) : Schwartz d := by
  let F : OrthogonalGroup d → Schwartz d :=
    fun U ↦ radialIsometrySchwartzOrbit
      (orthogonalLinearIsometry U⁻¹) f
  let C : ℕ → ℕ → ℝ :=
    fun k n ↦ SchwartzMap.seminorm ℂ k n f
  have hmeas : ∀ (n : ℕ) (x : Ambient d),
      AEStronglyMeasurable
        (fun U : OrthogonalGroup d ↦ iteratedFDeriv ℝ n
          (F U : Ambient d → ℂ) x)
        (radialOrthogonalHaar d) := by
    intro n x
    exact orthogonalSchwartzInverseIteratedFDeriv_aestronglyMeasurable
      f n x
  have hseminorm : ∀ (U : OrthogonalGroup d) (k n : ℕ),
      SchwartzMap.seminorm ℂ k n (F U) ≤ C k n := by
    intro U k n
    exact (radialIsometrySchwartzOrbit_seminorm_eq
      (orthogonalLinearIsometry U⁻¹) f k n).le
  have hderiv : ∀ (n : ℕ) (x : Ambient d),
      iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ ∫ U, F U y ∂radialOrthogonalHaar d) x =
        ∫ U, iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ F U y) x ∂radialOrthogonalHaar d := by
    intro n x
    exact radialSchwartzParametric_iteratedFDeriv_integral
      (radialOrthogonalHaar d) F C hmeas hseminorm n x
  have hsmooth : ContDiff ℝ ∞
      (fun x : Ambient d ↦ ∫ U, F U x ∂radialOrthogonalHaar d) := by
    refine contDiff_of_differentiable_iteratedFDeriv ?_
    intro n _
    have heq := funext (hderiv n)
    rw [heq]
    intro x
    exact (radialSchwartzParametric_hasFDerivAt_iteratedIntegral
      (radialOrthogonalHaar d) F C hmeas hseminorm n x).differentiableAt
  have hweighted : ∀ (k n : ℕ) (U : OrthogonalGroup d)
      (x : Ambient d),
      ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (fun y : Ambient d ↦ F U y) x‖ ≤ C k n := by
    intro k n U x
    exact radialIsometrySchwartzOrbit_weighted_iteratedFDeriv_le
      (orthogonalLinearIsometry U⁻¹) f k n x
  exact scalarProbabilitySchwartzAverage
    (radialOrthogonalHaar d) F C hsmooth hderiv hweighted
@[simp]
theorem radialSymmetrization_apply {d : ℕ}
    (f : Schwartz d) (x : Ambient d) :
    radialSymmetrization f x = radialSymmetrizationAverage f x := by
  rfl
end SpherePacking.Alternative
end
noncomputable section
open MeasureTheory
open scoped FourierTransform Topology
namespace SpherePacking.Alternative
def orthogonalScalarAverage
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    (μ : Measure G)
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    (f : Schwartz d) (x : Ambient d) : ℂ :=
  ∫ U : G, f (A U x) ∂μ
theorem orthogonalScalarAverage_im_eq_zero
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    {μ : Measure G}
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    {f : Schwartz d} (hf : IsRealValued f)
    (x : Ambient d)
    (hint : Integrable (fun U : G ↦ f (A U x)) μ) :
    (orthogonalScalarAverage μ A f x).im = 0 := by
  unfold orthogonalScalarAverage
  calc
    (∫ U : G, f (A U x) ∂μ).im =
        ∫ U : G, (f (A U x)).im ∂μ := (integral_im hint).symm
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with U
      exact hf (A U x)
theorem orthogonalScalarAverage_re
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    {μ : Measure G}
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    (f : Schwartz d) (x : Ambient d)
    (hint : Integrable (fun U : G ↦ f (A U x)) μ) :
    (orthogonalScalarAverage μ A f x).re =
      ∫ U : G, (f (A U x)).re ∂μ := by
  unfold orthogonalScalarAverage
  exact (integral_re hint).symm
theorem orthogonalScalarAverage_nonneg_of_nonneg
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    {μ : Measure G}
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    {f : Schwartz d}
    (hf : ∀ y : Ambient d, 0 ≤ (f y).re)
    (x : Ambient d)
    (hint : Integrable (fun U : G ↦ f (A U x)) μ) :
    0 ≤ (orthogonalScalarAverage μ A f x).re := by
  rw [orthogonalScalarAverage_re A f x hint]
  exact integral_nonneg (fun U ↦ hf (A U x))
theorem orthogonalScalarAverage_nonpos_of_norm_ge
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    {μ : Measure G}
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    {f : Schwartz d} {R : ℝ}
    (hf : ∀ y : Ambient d, R ≤ ‖y‖ → (f y).re ≤ 0)
    {x : Ambient d} (hx : R ≤ ‖x‖)
    (hint : Integrable (fun U : G ↦ f (A U x)) μ) :
    (orthogonalScalarAverage μ A f x).re ≤ 0 := by
  rw [orthogonalScalarAverage_re A f x hint]
  apply integral_nonpos
  intro U
  apply hf (A U x)
  simpa only [(A U).norm_map] using hx
theorem radialSymmetrizationAverage_eq_orthogonalScalarAverage
    {d : ℕ} (f : Schwartz d) (x : Ambient d) :
    radialSymmetrizationAverage f x =
      orthogonalScalarAverage (radialOrthogonalHaar d)
        (fun U : OrthogonalGroup d ↦ orthogonalLinearIsometry U⁻¹) f x := by
  rfl
theorem radialSymmetrizationAverage_im_eq_zero
    {d : ℕ} {f : Schwartz d} (hf : IsRealValued f)
    (x : Ambient d) :
    (radialSymmetrizationAverage f x).im = 0 := by
  rw [radialSymmetrizationAverage_eq_orthogonalScalarAverage]
  exact orthogonalScalarAverage_im_eq_zero
    (fun U : OrthogonalGroup d ↦ orthogonalLinearIsometry U⁻¹)
    hf x (radialSymmetrizationAverage_integrable f x)
theorem radialSymmetrizationAverage_nonneg_of_nonneg
    {d : ℕ} {f : Schwartz d}
    (hf : ∀ y : Ambient d, 0 ≤ (f y).re)
    (x : Ambient d) :
    0 ≤ (radialSymmetrizationAverage f x).re := by
  rw [radialSymmetrizationAverage_eq_orthogonalScalarAverage]
  exact orthogonalScalarAverage_nonneg_of_nonneg
    (fun U : OrthogonalGroup d ↦ orthogonalLinearIsometry U⁻¹)
    hf x (radialSymmetrizationAverage_integrable f x)
theorem radialSymmetrizationAverage_nonpos_of_norm_ge
    {d : ℕ} {f : Schwartz d} {R : ℝ}
    (hf : ∀ y : Ambient d, R ≤ ‖y‖ → (f y).re ≤ 0)
    {x : Ambient d} (hx : R ≤ ‖x‖) :
    (radialSymmetrizationAverage f x).re ≤ 0 := by
  rw [radialSymmetrizationAverage_eq_orthogonalScalarAverage]
  exact orthogonalScalarAverage_nonpos_of_norm_ge
    (fun U : OrthogonalGroup d ↦ orthogonalLinearIsometry U⁻¹)
    hf hx (radialSymmetrizationAverage_integrable f x)
theorem radialSymmetrizationAverage_nonpos_of_one_le_norm
    {d : ℕ} {f : Schwartz d}
    (hf : ∀ y : Ambient d, 1 ≤ ‖y‖ → (f y).re ≤ 0)
    {x : Ambient d} (hx : 1 ≤ ‖x‖) :
    (radialSymmetrizationAverage f x).re ≤ 0 :=
  radialSymmetrizationAverage_nonpos_of_norm_ge hf hx
end SpherePacking.Alternative
end
noncomputable section
open MeasureTheory
open scoped FourierTransform Real Topology
namespace SpherePacking.Alternative
theorem IsRadial.neg_apply {d : ℕ} {f : Schwartz d}
    (hf : IsRadial f) (x : Ambient d) : f (-x) = f x := by
  exact hf (-x) x (norm_neg x)
theorem IsRealValued.fourier_conj {d : ℕ} {f : Schwartz d}
    (hf : IsRealValued f) (x : Ambient d) :
    (starRingEnd ℂ) ((𝓕 f : Schwartz d) x) =
      (𝓕 f : Schwartz d) (-x) := by
  change (starRingEnd ℂ) (𝓕 (f : Ambient d → ℂ) x) =
    𝓕 (f : Ambient d → ℂ) (-x)
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  apply integral_congr_ae
  filter_upwards with y
  have hy : (starRingEnd ℂ) (f y) = f y :=
    Complex.conj_eq_iff_im.mpr (hf y)
  simp [smul_eq_mul, ← Complex.exp_conj, hy, real_inner_comm, map_ofNat]
theorem IsRadial.fourier_realValued {d : ℕ} {f : Schwartz d}
    (hradial : IsRadial f) (hreal : IsRealValued f) :
    IsRealValued (𝓕 f : Schwartz d) := by
  intro x
  apply Complex.conj_eq_iff_im.mp
  rw [hreal.fourier_conj x]
  change 𝓕 (f : Ambient d → ℂ) (-x) = 𝓕 (f : Ambient d → ℂ) x
  rw [Real.fourier_eq', Real.fourier_eq']
  have hneg :
      (fun y : Ambient d ↦
        Complex.exp ((↑(-2 * Real.pi * @inner ℝ _ _ y (-x)) : ℂ) * Complex.I) * f y) =
        (fun y : Ambient d ↦
          Complex.exp ((↑(-2 * Real.pi * @inner ℝ _ _ (-y) x) : ℂ) * Complex.I) *
            f (-y)) := by
    funext y
    rw [hradial.neg_apply y]
    congr 2
    simp
  simp only [smul_eq_mul]
  rw [hneg]
  exact (LinearIsometryEquiv.neg ℝ (E := Ambient d)).measurePreserving.integral_comp
    (LinearIsometryEquiv.neg ℝ (E := Ambient d)).toHomeomorph.measurableEmbedding
    (fun y : Ambient d ↦
      Complex.exp ((↑(-2 * Real.pi * @inner ℝ _ _ y x) : ℂ) * Complex.I) * f y)
end SpherePacking.Alternative
end
noncomputable section
open Filter MeasureTheory
open scoped FourierTransform Real Topology
namespace SpherePacking.Alternative
def radialFourierCharacter {d : ℕ}
    (ξ x : Ambient d) : ℂ :=
  Complex.exp
    (((-2 * Real.pi * @inner ℝ _ _ x ξ : ℝ) : ℂ) * Complex.I)
theorem radialFourierCharacter_continuous {d : ℕ} (ξ : Ambient d) :
    Continuous (radialFourierCharacter ξ) := by
  unfold radialFourierCharacter
  fun_prop
theorem radialFourierCharacter_norm {d : ℕ}
    (ξ x : Ambient d) :
    ‖radialFourierCharacter ξ x‖ = 1 := by
  unfold radialFourierCharacter
  exact Complex.norm_exp_ofReal_mul_I _
def radialFourierOrbitAverage
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    (μ : Measure G)
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    (f : Schwartz d) (x : Ambient d) : ℂ :=
  ∫ g : G, f (A g x) ∂μ
def radialFourierOrbitKernel
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    (f : Schwartz d) (ξ : Ambient d)
    (p : G × Ambient d) : ℂ :=
  radialFourierCharacter ξ p.2 * f (A p.1 p.2)
theorem radialFourier_orthogonalOrbit_integrable
    {d : ℕ} (f : Schwartz d)
    (A : Ambient d ≃ₗᵢ[ℝ] Ambient d) :
    Integrable (fun x : Ambient d ↦ f (A x)) := by
  change Integrable ((f : Ambient d → ℂ) ∘ A)
  exact (A.measurePreserving.integrable_comp_emb
    A.toHomeomorph.measurableEmbedding).2 f.integrable
theorem radialFourier_orthogonalCharacterOrbit_integrable
    {d : ℕ} (f : Schwartz d) (ξ : Ambient d)
    (A : Ambient d ≃ₗᵢ[ℝ] Ambient d) :
    Integrable
      (fun x : Ambient d ↦
        radialFourierCharacter ξ x * f (A x)) := by
  refine (radialFourier_orthogonalOrbit_integrable f A).bdd_mul
    (c := (1 : ℝ))
    (radialFourierCharacter_continuous ξ).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [radialFourierCharacter_norm]
theorem radialFourier_orthogonalCharacterOrbit_integral_norm
    {d : ℕ} (f : Schwartz d) (ξ : Ambient d)
    (A : Ambient d ≃ₗᵢ[ℝ] Ambient d) :
    (∫ x : Ambient d,
      ‖radialFourierCharacter ξ x * f (A x)‖) =
      ∫ x : Ambient d, ‖f x‖ := by
  calc
    (∫ x : Ambient d,
      ‖radialFourierCharacter ξ x * f (A x)‖) =
        ∫ x : Ambient d, ‖f (A x)‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [norm_mul, radialFourierCharacter_norm, one_mul]
    _ = ∫ x : Ambient d, ‖f x‖ :=
      A.measurePreserving.integral_comp
        A.toHomeomorph.measurableEmbedding
        (fun x : Ambient d ↦ ‖f x‖)
theorem radialFourier_orthogonalCharacterOrbit_integral
    {d : ℕ} (f : Schwartz d) (ξ : Ambient d)
    (A : Ambient d ≃ₗᵢ[ℝ] Ambient d) :
    (∫ x : Ambient d,
      radialFourierCharacter ξ x * f (A x)) =
      (𝓕 f : Schwartz d) (A ξ) := by
  rw [congrFun (SchwartzMap.fourier_coe f) (A ξ)]
  rw [← Real.fourier_comp_linearIsometry A
    (f : Ambient d → ℂ) ξ]
  rw [Real.fourier_eq']
  rfl
theorem radialFourierOrbitKernel_integrable
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasure μ]
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    (f : Schwartz d) (ξ : Ambient d)
    (horbit :
      Measurable (fun p : G × Ambient d ↦ f (A p.1 p.2))) :
    Integrable (radialFourierOrbitKernel A f ξ)
      (μ.prod volume) := by
  have hcharacter :
      Measurable
        (fun p : G × Ambient d ↦
          radialFourierCharacter ξ p.2) :=
    (radialFourierCharacter_continuous ξ).measurable.comp
      measurable_snd
  have hmeas :
      AEStronglyMeasurable
        (radialFourierOrbitKernel A f ξ)
        (μ.prod volume) := by
    exact (hcharacter.mul horbit).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [] with g
    exact radialFourier_orthogonalCharacterOrbit_integrable
      f ξ (A g)
  · have hconstant :
        (fun g : G ↦
          ∫ x : Ambient d,
            ‖radialFourierOrbitKernel A f ξ (g, x)‖) =
          fun _ : G ↦ ∫ x : Ambient d, ‖f x‖ := by
      funext g
      exact radialFourier_orthogonalCharacterOrbit_integral_norm
        f ξ (A g)
    rw [hconstant]
    exact integrable_const _
theorem radialFourierOrbitAverage_fourier
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasure μ]
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    (f : Schwartz d) (ξ : Ambient d)
    (horbit :
      Measurable (fun p : G × Ambient d ↦ f (A p.1 p.2))) :
    (𝓕 (radialFourierOrbitAverage μ A f) : Ambient d → ℂ) ξ =
      ∫ g : G, (𝓕 f : Schwartz d) (A g ξ) ∂μ := by
  have hprod :=
    radialFourierOrbitKernel_integrable μ A f ξ horbit
  have hprod' :
      Integrable
        (Function.uncurry
          (fun g : G ↦ fun x : Ambient d ↦
            radialFourierCharacter ξ x * f (A g x)))
        (μ.prod volume) := hprod
  calc
    (𝓕 (radialFourierOrbitAverage μ A f) : Ambient d → ℂ) ξ =
        ∫ x : Ambient d,
          radialFourierCharacter ξ x *
            (∫ g : G, f (A g x) ∂μ) := by
      rw [Real.fourier_eq']
      rfl
    _ = ∫ x : Ambient d,
          ∫ g : G,
            radialFourierCharacter ξ x * f (A g x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [integral_const_mul]
    _ = ∫ g : G,
          (∫ x : Ambient d,
            radialFourierCharacter ξ x * f (A g x)) ∂μ := by
      exact (integral_integral_swap hprod').symm
    _ = ∫ g : G, (𝓕 f : Schwartz d) (A g ξ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      exact radialFourier_orthogonalCharacterOrbit_integral
        f ξ (A g)
theorem radialOrthogonalHaarOrbit_measurable
    {d : ℕ} (f : Schwartz d) :
    Measurable
      (fun p : OrthogonalGroup d × Ambient d ↦
        f (orthogonalLinearIsometry (p.1⁻¹) p.2)) := by
  have hforward :
      Measurable
        (fun p : OrthogonalGroup d × Ambient d ↦
          f (orthogonalAction p.1 p.2)) :=
    (f.continuous.comp (orthogonalAction_joint_continuous d)).measurable
  have hinverse :
      Measurable
        (fun p : OrthogonalGroup d × Ambient d ↦
          (p.1⁻¹, p.2)) :=
    ((continuous_inv.comp continuous_fst).prodMk
      continuous_snd).measurable
  have hcomposed :
      Measurable
        ((fun p : OrthogonalGroup d × Ambient d ↦
            f (orthogonalAction p.1 p.2)) ∘
          (fun p : OrthogonalGroup d × Ambient d ↦
            (p.1⁻¹, p.2))) :=
    hforward.comp hinverse
  have heq :
      ((fun p : OrthogonalGroup d × Ambient d ↦
            f (orthogonalAction p.1 p.2)) ∘
          (fun p : OrthogonalGroup d × Ambient d ↦
            (p.1⁻¹, p.2))) =
        (fun p : OrthogonalGroup d × Ambient d ↦
          f (orthogonalLinearIsometry (p.1⁻¹) p.2)) := by
    funext p
    simp only [Function.comp_apply, orthogonalLinearIsometry_apply]
  rw [← heq]
  exact hcomposed
theorem radialOrthogonalHaar_radialFourierOrbitAverage_eq
    {d : ℕ} (f : Schwartz d) :
    radialFourierOrbitAverage
        (radialOrthogonalHaar d)
        (fun U : OrthogonalGroup d ↦
          orthogonalLinearIsometry (U⁻¹)) f =
      fun x : Ambient d ↦
        ∫ U : OrthogonalGroup d,
          f (orthogonalAction (U⁻¹) x)
            ∂radialOrthogonalHaar d := by
  funext x
  simp only [radialFourierOrbitAverage,
    orthogonalLinearIsometry_apply]
theorem radialOrthogonalHaar_fourier_average
    {d : ℕ} (f : Schwartz d) (ξ : Ambient d) :
    (𝓕 (fun x : Ambient d ↦
      ∫ U : OrthogonalGroup d,
        f (orthogonalAction (U⁻¹) x)
          ∂radialOrthogonalHaar d) : Ambient d → ℂ) ξ =
      ∫ U : OrthogonalGroup d,
        (𝓕 f : Schwartz d) (orthogonalAction (U⁻¹) ξ)
          ∂radialOrthogonalHaar d := by
  have h := radialFourierOrbitAverage_fourier
    (radialOrthogonalHaar d)
    (fun U : OrthogonalGroup d ↦ orthogonalLinearIsometry (U⁻¹))
    f ξ (radialOrthogonalHaarOrbit_measurable f)
  rw [radialOrthogonalHaar_radialFourierOrbitAverage_eq] at h
  simpa only [orthogonalLinearIsometry_apply] using h
theorem fourier_radialSymmetrizationAverage
    {d : ℕ} (f : Schwartz d) (ξ : Ambient d) :
    (𝓕 (radialSymmetrizationAverage f) : Ambient d → ℂ) ξ =
      radialSymmetrizationAverage (𝓕 f : Schwartz d) ξ := by
  change
    (𝓕 (fun x : Ambient d ↦
      ∫ U : OrthogonalGroup d,
        f (orthogonalAction (U⁻¹) x)
          ∂radialOrthogonalHaar d) : Ambient d → ℂ) ξ =
      ∫ U : OrthogonalGroup d,
        (𝓕 f : Schwartz d) (orthogonalAction (U⁻¹) ξ)
          ∂radialOrthogonalHaar d
  exact radialOrthogonalHaar_fourier_average f ξ
end SpherePacking.Alternative
end
section
namespace CohnElkies
open Real
end CohnElkies
end
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace CohnElkies
end CohnElkies
end
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
structure SharpCohnElkiesManuscriptConclusions : Prop where
  root_before_infimum :
    Tendsto
      (fun d : ℕ =>
        sInf {q : ℝ | ∃ f : Admissible d,
          quotient f ^ ((d : ℝ)⁻¹) = q} /
          Real.sqrt (d : ℝ))
      atTop (𝓝 (1 / Real.pi))
  root_before_infimum_vanishing_error :
    ∃ err : ℕ → ℝ,
      Tendsto err atTop (𝓝 0) ∧
      ∀ d : ℕ, 0 < d →
        sInf {q : ℝ | ∃ f : Admissible d,
          quotient f ^ ((d : ℝ)⁻¹) = q} =
          (1 / Real.pi + err d) * Real.sqrt (d : ℝ)
  linear_program_root :
    Tendsto
      (fun d : ℕ => (linearProgram d) ^ ((d : ℝ)⁻¹))
      atTop (𝓝 (Real.sqrt (Real.exp 1 / (2 * Real.pi))))
  natural_logarithmic_rate :
    Tendsto
      (fun d : ℕ => Real.log (linearProgram d) / (d : ℝ))
      atTop
      (𝓝 ((1 / 2 : ℝ) * Real.log (Real.exp 1 / (2 * Real.pi))))
  natural_vanishing_exponential_error :
    ∃ err : ℕ → ℝ,
      Tendsto err atTop (𝓝 0) ∧
      (∀ᶠ d : ℕ in atTop,
        linearProgram d =
          (Real.sqrt (Real.exp 1 / (2 * Real.pi)) + err d) ^ d)
  universal_nonnegative_delta :
    ∃ δ : ℕ → ℝ,
      Tendsto δ atTop (𝓝 0) ∧
      (∀ d : ℕ, 0 ≤ δ d) ∧
      (∀ᶠ d : ℕ in atTop, ∀ f : Admissible d,
        (2 : ℝ) ^ d / unitBallVolume d *
          (Real.sqrt (Real.exp 1 / (2 * Real.pi)) - δ d) ^ d ≤
            quotient f)
  base_two_exponent_positive :
    0 < (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1)
  base_two_decimal_certificate :
    (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1) ∈
      Set.Ioo
        (0.604400544291677695341677307053 : ℝ)
        0.604400544291677695341677307054
  base_two_logarithmic_rate :
    Tendsto
      (fun d : ℕ => Real.logb 2 (linearProgram d) / (d : ℝ))
      atTop
      (𝓝 (-((1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1))))
  base_two_vanishing_exponential_error :
    ∃ err : ℕ → ℝ,
      Tendsto err atTop (𝓝 0) ∧
      (∀ᶠ d : ℕ in atTop,
        linearProgram d =
          (2 : ℝ) ^
            (-((1 / 2 : ℝ) *
                Real.logb 2 (2 * Real.pi / Real.exp 1) + err d) *
              (d : ℝ)))
end CohnElkies
end
noncomputable section
open MeasureTheory
open scoped FourierTransform Real Topology
namespace SpherePacking.Alternative
structure IsUnrestrictedAdmissible {d : ℕ} (f : Schwartz d) : Prop where
  real_valued : IsRealValued f
  fourier_real_valued : IsRealValued (𝓕 f : Schwartz d)
  fourier_zero_pos : 0 < fourierReal f 0
  fourier_nonneg : ∀ x, 0 ≤ fourierReal f x
  eventually_nonpos : ∀ x : Ambient d, 1 ≤ ‖x‖ → (f x).re ≤ 0
end SpherePacking.Alternative
namespace SpherePacking.Alternative
theorem IsUnrestrictedAdmissible.radialAdmissible_of_average_data
    {d : ℕ} {f g : Schwartz d}
    (hf : IsUnrestrictedAdmissible f)
    (hreal : IsRealValued g)
    (hradial : IsRadial g)
    (hfourier_zero : fourierReal g 0 = fourierReal f 0)
    (hfourier_nonneg : ∀ x : Ambient d, 0 ≤ fourierReal g x)
    (hexterior : ∀ x : Ambient d, 1 ≤ ‖x‖ → (g x).re ≤ 0) :
    IsAdmissible g where
  real_valued := hreal
  radial := hradial
  fourier_real_valued := hradial.fourier_realValued hreal
  fourier_zero_pos := hfourier_zero.symm ▸ hf.fourier_zero_pos
  fourier_nonneg := hfourier_nonneg
  eventually_nonpos := hexterior
theorem radial_of_radialSymmetrizationAverage
    {d : ℕ} {f g : Schwartz d}
    (haverage : ∀ x : Ambient d,
      g x = radialSymmetrizationAverage f x) :
    IsRadial g := by
  intro x y hxy
  rw [haverage x, haverage y]
  exact radialSymmetrizationAverage_eq_of_norm_eq f hxy
theorem radialSymmetrizationAverage_fourier_zero
    {d : ℕ} {f g : Schwartz d}
    (hfourier : ∀ x : Ambient d,
      (𝓕 g : Schwartz d) x =
        radialSymmetrizationAverage (𝓕 f : Schwartz d) x) :
    fourierReal g 0 = fourierReal f 0 := by
  unfold fourierReal
  rw [hfourier 0, radialSymmetrizationAverage_zero]
theorem IsUnrestrictedAdmissible.radialAdmissible_of_radialSymmetrizationAverage
    {d : ℕ} {f g : Schwartz d}
    (hf : IsUnrestrictedAdmissible f)
    (haverage : ∀ x : Ambient d,
      g x = radialSymmetrizationAverage f x)
    (hfourier : ∀ x : Ambient d,
      (𝓕 g : Schwartz d) x =
        radialSymmetrizationAverage (𝓕 f : Schwartz d) x) :
    IsAdmissible g := by
  apply hf.radialAdmissible_of_average_data
  · intro x
    rw [haverage x]
    exact radialSymmetrizationAverage_im_eq_zero hf.real_valued x
  · exact radial_of_radialSymmetrizationAverage haverage
  · exact radialSymmetrizationAverage_fourier_zero hfourier
  · intro x
    change 0 ≤ ((𝓕 g : Schwartz d) x).re
    rw [hfourier x]
    apply radialSymmetrizationAverage_nonneg_of_nonneg
    intro y
    exact hf.fourier_nonneg y
  · intro x hx
    rw [haverage x]
    exact radialSymmetrizationAverage_nonpos_of_one_le_norm
      hf.eventually_nonpos hx
theorem radialSymmetrization_fourier_average_apply_for_admissibility
    {d : ℕ} (f : Schwartz d) (x : Ambient d) :
    (𝓕 (radialSymmetrization f) : Schwartz d) x =
      radialSymmetrizationAverage (𝓕 f : Schwartz d) x := by
  have hfun : (radialSymmetrization f : Ambient d → ℂ) =
      radialSymmetrizationAverage f := by
    funext y
    exact radialSymmetrization_apply f y
  calc
    (𝓕 (radialSymmetrization f) : Schwartz d) x =
        (𝓕 (radialSymmetrization f : Ambient d → ℂ)) x :=
      congrFun (SchwartzMap.fourier_coe (radialSymmetrization f)) x
    _ = (𝓕 (radialSymmetrizationAverage f) : Ambient d → ℂ) x := by
      rw [hfun]
    _ = radialSymmetrizationAverage (𝓕 f : Schwartz d) x :=
      fourier_radialSymmetrizationAverage f x
theorem IsUnrestrictedAdmissible.radialSymmetrization_admissible
    {d : ℕ} {f : Schwartz d}
    (hf : IsUnrestrictedAdmissible f) :
    IsAdmissible (radialSymmetrization f) := by
  exact hf.radialAdmissible_of_radialSymmetrizationAverage
    (radialSymmetrization_apply f)
    (radialSymmetrization_fourier_average_apply_for_admissibility f)
end SpherePacking.Alternative
namespace SpherePacking.Alternative
def schwartzDilation {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (f : Schwartz d) : Schwartz d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 a ha)) f
end SpherePacking.Alternative
end
noncomputable section
open Filter
open scoped FourierTransform SchwartzMap Topology
namespace PackingBounds
theorem FullAdmissible.toAlternative {d : ℕ} (f : FullAdmissible d) :
    SpherePacking.Alternative.IsUnrestrictedAdmissible f.function where
  real_valued := f.real
  fourier_real_valued := f.fourier_real
  fourier_zero_pos := f.fourier_zero_pos
  fourier_nonneg := f.fourier_nonneg
  eventually_nonpos := f.outside_nonpos
def FullAdmissible.ofAlternative {d : ℕ}
    {f : SpherePacking.Alternative.Schwartz d}
    (hf : SpherePacking.Alternative.IsUnrestrictedAdmissible f) :
    FullAdmissible d where
  function := f
  real := hf.real_valued
  fourier_real := hf.fourier_real_valued
  fourier_nonneg := hf.fourier_nonneg
  fourier_zero_pos := hf.fourier_zero_pos
  outside_nonpos := hf.eventually_nonpos
def FullAdmissible.radialization {d : ℕ} (f : FullAdmissible d) :
    CohnElkies.Admissible d :=
  let hf := f.toAlternative
  let g := SpherePacking.Alternative.radialSymmetrization f.function
  let hg := hf.radialSymmetrization_admissible
  { function := g
    real := hg.real_valued
    radial := hg.radial
    fourier_real := hg.fourier_real_valued
    fourier_nonneg := hg.fourier_nonneg
    fourier_zero_pos := hg.fourier_zero_pos
    outside_nonpos := hg.eventually_nonpos }
namespace FullMain
end FullMain
end PackingBounds
end
noncomputable section
open Filter
open scoped Topology
namespace PackingBounds
structure SharpFullCohnElkiesManuscriptConclusions : Prop where
  root_before_infimum :
    Tendsto
      (fun d : ℕ =>
        sInf {q : ℝ | ∃ f : FullAdmissible d,
          fullQuotient f ^ ((d : ℝ)⁻¹) = q} /
          Real.sqrt (d : ℝ))
      atTop (𝓝 (1 / Real.pi))
  root_before_infimum_vanishing_error :
    ∃ err : ℕ → ℝ,
      Tendsto err atTop (𝓝 0) ∧
      ∀ d : ℕ, 0 < d →
        sInf {q : ℝ | ∃ f : FullAdmissible d,
          fullQuotient f ^ ((d : ℝ)⁻¹) = q} =
          (1 / Real.pi + err d) * Real.sqrt (d : ℝ)
  linear_program_root :
    Tendsto
      (fun d : ℕ => (fullLinearProgram d) ^ ((d : ℝ)⁻¹))
      atTop (𝓝 (Real.sqrt (Real.exp 1 / (2 * Real.pi))))
  natural_logarithmic_rate :
    Tendsto
      (fun d : ℕ => Real.log (fullLinearProgram d) / (d : ℝ))
      atTop
      (𝓝 ((1 / 2 : ℝ) * Real.log (Real.exp 1 / (2 * Real.pi))))
  natural_vanishing_exponential_error :
    ∃ err : ℕ → ℝ,
      Tendsto err atTop (𝓝 0) ∧
      (∀ᶠ d : ℕ in atTop,
        fullLinearProgram d =
          (Real.sqrt (Real.exp 1 / (2 * Real.pi)) + err d) ^ d)
  universal_nonnegative_delta :
    ∃ δ : ℕ → ℝ,
      Tendsto δ atTop (𝓝 0) ∧
      (∀ d : ℕ, 0 ≤ δ d) ∧
      (∀ᶠ d : ℕ in atTop, ∀ f : FullAdmissible d,
        (2 : ℝ) ^ d / CohnElkies.unitBallVolume d *
          (Real.sqrt (Real.exp 1 / (2 * Real.pi)) - δ d) ^ d ≤
            fullQuotient f)
  base_two_exponent_positive :
    0 < (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1)
  base_two_decimal_certificate :
    (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1) ∈
      Set.Ioo
        (0.604400544291677695341677307053 : ℝ)
        0.604400544291677695341677307054
  base_two_logarithmic_rate :
    Tendsto
      (fun d : ℕ => Real.logb 2 (fullLinearProgram d) / (d : ℝ))
      atTop
      (𝓝 (-((1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1))))
  base_two_vanishing_exponential_error :
    ∃ err : ℕ → ℝ,
      Tendsto err atTop (𝓝 0) ∧
      (∀ᶠ d : ℕ in atTop,
        fullLinearProgram d =
          (2 : ℝ) ^
            (-((1 / 2 : ℝ) *
                Real.logb 2 (2 * Real.pi / Real.exp 1) + err d) *
              (d : ℝ)))
end PackingBounds
end


