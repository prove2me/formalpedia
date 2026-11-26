-- Prove2me | solution 1 for Auto.aux_multilinear_input_deformation_properties
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:06:24.062522+00:00
-- url     : https://prove2.me/submissions/7b25bd5f-5c55-453e-9180-7d15b5aab6ee

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Definitions.Def_LeanNct_Auto_MultilinearInterpolation
section
@[expose] public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
namespace Auto
private theorem integrable_map_of_integrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) (hf : Integrable f μ) (φ : ℂ → ℂ) (hφ : φ 0 = 0) :
    Integrable (f.map φ : X → ℂ) μ :=
  (SimpleFunc.integrable_iff_finMeasSupp.mp hf).map hφ |>.integrable
private theorem re_affine_im_mul_ofReal
    (a b l t : ℝ) :
    (((a : ℂ) * ((t : ℂ) * Complex.I) + (b : ℂ)) * (l : ℂ)).re = b * l := by
  simp [Complex.mul_re]
private theorem re_affine_one_im_mul_ofReal
    (a b l t : ℝ) :
    (((a : ℂ) * (1 + (t : ℂ) * Complex.I) + (b : ℂ)) * (l : ℂ)).re =
      (a + b) * l := by
  simp [Complex.mul_re]
private theorem input_deformation_at_theta
    {a₀ a₁ θ : ℝ}
    (hθ : a₀ + θ * (a₁ - a₀) = 1) (c : ℂ) :
    (if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (θ : ℂ) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))) = c := by
  by_cases hc : c = 0
  · simp [hc]
  · simp only [if_neg hc]
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have harg :
        ((((a₁ - a₀ : ℝ) : ℂ) * (θ : ℂ) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ)) =
          ((Real.log ‖c‖ : ℝ) : ℂ) := by
      norm_cast
      have hcoef : (a₁ - a₀) * θ + a₀ = 1 := by linarith [hθ]
      rw [hcoef]
      ring
    rw [harg, ← Complex.ofReal_exp, Real.exp_log hcn]
    field_simp [hcn.ne']
private theorem norm_input_deformation_left_coeff
    {a₀ a₁ t : ℝ} (ha₀ : 0 < a₀) (c : ℂ) :
    ‖if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * ((t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))‖ =
      ‖c‖ ^ a₀ := by
  by_cases hc : c = 0
  · simp [hc, Real.zero_rpow ha₀.ne']
  · rw [if_neg hc, norm_mul, norm_div, Complex.norm_exp]
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [div_self hcn.ne', one_mul,
      re_affine_im_mul_ofReal (a₁ - a₀) a₀ (Real.log ‖c‖) t,
      Real.rpow_def_of_pos hcn]
    ring_nf
private theorem norm_input_deformation_right_coeff
    {a₀ a₁ t : ℝ} (ha₁ : 0 < a₁) (c : ℂ) :
    ‖if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))‖ =
      ‖c‖ ^ a₁ := by
  by_cases hc : c = 0
  · simp [hc, Real.zero_rpow ha₁.ne']
  · rw [if_neg hc, norm_mul, norm_div, Complex.norm_exp]
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [div_self hcn.ne', one_mul,
      re_affine_one_im_mul_ofReal (a₁ - a₀) a₀ (Real.log ‖c‖) t,
      Real.rpow_def_of_pos hcn]
    congr 1
    ring
private theorem eLpNorm_simpleFunc_map_of_norm_rpow
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (φ : ℂ → ℂ) (hφ : ∀ c : ℂ, ‖φ c‖ = ‖c‖ ^ (r / s)) :
    eLpNorm (f.map φ : X → ℂ) (ENNReal.ofReal s) μ =
      eLpNorm (f : X → ℂ) (ENNReal.ofReal r) μ ^ (r / s) := by
  have hrs : 0 ≤ r / s := (div_pos hr hs).le
  have hleft_int :
      (∫⁻ x, ‖(f.map φ : X → ℂ) x‖ₑ ^ s ∂μ) =
        ∫⁻ x, ‖(f : X → ℂ) x‖ₑ ^ r ∂μ := by
    apply lintegral_congr
    intro x
    rw [SimpleFunc.map_apply, ← ofReal_norm, hφ, ← ofReal_norm]
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hrs]
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp [hr.ne', hs.ne']
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
  · rw [ENNReal.toReal_ofReal hs.le, hleft_int]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
    · rw [ENNReal.toReal_ofReal hr.le, ← ENNReal.rpow_mul]
      congr 1
      field_simp [hr.ne', hs.ne']
    · exact ne_of_gt ((ENNReal.ofReal_pos).mpr hr)
    · exact ENNReal.ofReal_ne_top
  · exact ne_of_gt ((ENNReal.ofReal_pos).mpr hs)
  · exact ENNReal.ofReal_ne_top
private theorem real_inv_interpolation
    {p p₀ p₁ : ENNReal} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) :
    p.toReal⁻¹ = (1 - θ) * p₀.toReal⁻¹ + θ * p₁.toReal⁻¹ := by
  have hθ0 : 0 ≤ θ := hθ.1.le
  have h1θ0 : 0 ≤ 1 - θ := by linarith [hθ.2]
  have hp₀0 : p₀ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp₀)
  have hp₁0 : p₁ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp₁)
  have hleft_top : ENNReal.ofReal (1 - θ) * p₀⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hp₀0)
  have hright_top : ENNReal.ofReal θ * p₁⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hp₁0)
  have h := congrArg ENNReal.toReal hp
  rw [ENNReal.toReal_inv, ENNReal.toReal_add hleft_top hright_top,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_inv] at h
  simpa [ENNReal.toReal_ofReal h1θ0, ENNReal.toReal_ofReal hθ0] using h
private theorem input_coeff_at_theta_of_interp_general
    {p p₀ p₁ : ENNReal} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp : 1 ≤ p) (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hp_top : p ≠ ∞)
    (hint : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    (p.toReal * p₀⁻¹.toReal) + θ *
      (p.toReal * p₁⁻¹.toReal - p.toReal * p₀⁻¹.toReal) = 1 := by
  have hreal := real_inv_interpolation hθ hint hp₀ hp₁
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hrpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have halg :
      (1 - θ) * p₀.toReal⁻¹ + θ * p₁.toReal⁻¹ =
        p₀.toReal⁻¹ + θ * (p₁.toReal⁻¹ - p₀.toReal⁻¹) := by
    ring
  rw [halg] at hreal
  simp only [ENNReal.toReal_inv]
  calc
    p.toReal * p₀.toReal⁻¹ + θ *
        (p.toReal * p₁.toReal⁻¹ - p.toReal * p₀.toReal⁻¹) =
        p.toReal * (p₀.toReal⁻¹ + θ * (p₁.toReal⁻¹ - p₀.toReal⁻¹)) := by ring
    _ = p.toReal * p.toReal⁻¹ := by rw [hreal]
    _ = 1 := mul_inv_cancel₀ hrpos.ne'
private theorem simpleFunc_input_deformation_at_theta
    {X : Type*} [MeasurableSpace X] (f : SimpleFunc X ℂ)
    {a₀ a₁ θ : ℝ} (hθ : a₀ + θ * (a₁ - a₀) = 1) :
    f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (θ : ℂ) + (a₀ : ℂ)) *
          ((Real.log ‖c‖ : ℝ) : ℂ))) = f := by
  ext x
  rw [SimpleFunc.map_apply]
  exact input_deformation_at_theta hθ (f x)
private theorem norm_input_deformation_left_coeff_zero
    {a₀ a₁ t : ℝ} (ha₀ : a₀ = 0) (c : ℂ) :
    ‖if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * ((t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [if_neg hc, norm_mul, norm_div, Complex.norm_exp]
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [div_self hcn.ne', one_mul,
      re_affine_im_mul_ofReal (a₁ - a₀) a₀ (Real.log ‖c‖) t, ha₀]
    norm_num
private theorem norm_input_deformation_right_coeff_zero
    {a₀ a₁ t : ℝ} (ha₁ : a₁ = 0) (c : ℂ) :
    ‖if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [if_neg hc, norm_mul, norm_div, Complex.norm_exp]
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [div_self hcn.ne', one_mul,
      re_affine_one_im_mul_ofReal (a₁ - a₀) a₀ (Real.log ‖c‖) t]
    have hsum : a₁ - a₀ + a₀ = 0 := by linarith
    rw [hsum]
    norm_num
private theorem eLpNorm_input_deformation_left_coeff_top
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {a₀ a₁ t : ℝ} (ha₀ : a₀ = 0) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * ((t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ) ∞ μ ≤ 1 := by
  rw [eLpNorm_exponent_top]
  convert eLpNormEssSup_le_of_ae_bound (μ := μ)
    (f := (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * ((t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ))
    (ae_of_all _ fun x ↦ by
      rw [SimpleFunc.map_apply]
      exact norm_input_deformation_left_coeff_zero ha₀ (f x)) using 1; norm_num
private theorem eLpNorm_input_deformation_right_coeff_top
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {a₀ a₁ t : ℝ} (ha₁ : a₁ = 0) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ) ∞ μ ≤ 1 := by
  rw [eLpNorm_exponent_top]
  convert eLpNormEssSup_le_of_ae_bound (μ := μ)
    (f := (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ))
    (ae_of_all _ fun x ↦ by
      rw [SimpleFunc.map_apply]
      exact norm_input_deformation_right_coeff_zero ha₁ (f x)) using 1; norm_num
private theorem eLpNorm_input_deformation_left_coeff
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {r s a₀ a₁ t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ha₀ : a₀ = r / s) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * ((t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ)
      (ENNReal.ofReal s) μ =
      eLpNorm (f : X → ℂ) (ENNReal.ofReal r) μ ^ (r / s) := by
  apply eLpNorm_simpleFunc_map_of_norm_rpow f hr hs
  intro c
  rw [norm_input_deformation_left_coeff (by rw [ha₀]; exact div_pos hr hs)]
  rw [ha₀]
private theorem eLpNorm_input_deformation_right_coeff
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {r s a₀ a₁ t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ha₁ : a₁ = r / s) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ)
      (ENNReal.ofReal s) μ =
      eLpNorm (f : X → ℂ) (ENNReal.ofReal r) μ ^ (r / s) := by
  apply eLpNorm_simpleFunc_map_of_norm_rpow f hr hs
  intro c
  rw [norm_input_deformation_right_coeff (by rw [ha₁]; exact div_pos hr hs)]
  rw [ha₁]
private theorem toReal_mul_toReal_inv_eq_div (r s : ENNReal) :
    r.toReal * (s⁻¹).toReal = r.toReal / s.toReal := by
  rw [ENNReal.toReal_inv, div_eq_mul_inv]
private theorem eLpNorm_input_deformation_left_coeff_le_one
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {r s a₀ a₁ t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ha₀ : a₀ = r / s)
    (hf : eLpNorm (f : X → ℂ) (ENNReal.ofReal r) μ ≤ 1) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * ((t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ)
      (ENNReal.ofReal s) μ ≤ 1 := by
  rw [eLpNorm_input_deformation_left_coeff f hr hs ha₀]
  exact ENNReal.rpow_le_one hf (div_nonneg hr.le hs.le)
private theorem eLpNorm_input_deformation_right_coeff_le_one
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {r s a₀ a₁ t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ha₁ : a₁ = r / s)
    (hf : eLpNorm (f : X → ℂ) (ENNReal.ofReal r) μ ≤ 1) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ)
      (ENNReal.ofReal s) μ ≤ 1 := by
  rw [eLpNorm_input_deformation_right_coeff f hr hs ha₁]
  exact ENNReal.rpow_le_one hf (div_nonneg hr.le hs.le)
private theorem eLpNorm_input_deformation_left_coeff_ennreal_le_one
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {p p₀ : ENNReal} {a₀ a₁ t : ℝ}
    (hp : 1 ≤ p) (hp₀ : 1 ≤ p₀) (hp_top : p ≠ ∞)
    (ha₀ : a₀ = p.toReal * (p₀⁻¹).toReal)
    (hf : eLpNorm (f : X → ℂ) p μ ≤ 1) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * ((t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ) p₀ μ ≤ 1 := by
  by_cases hp₀_top : p₀ = ∞
  · have ha₀_zero : a₀ = 0 := by simpa [hp₀_top] using ha₀
    simpa [hp₀_top] using
      eLpNorm_input_deformation_left_coeff_top (μ := μ) f (a₁ := a₁) (t := t) ha₀_zero
  · have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
    have hp₀0 : p₀ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp₀)
    have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
    have hs : 0 < p₀.toReal := ENNReal.toReal_pos hp₀0 hp₀_top
    have ha₀' : a₀ = p.toReal / p₀.toReal := by
      rw [← toReal_mul_toReal_inv_eq_div]
      exact ha₀
    rw [← ENNReal.ofReal_toReal hp₀_top]
    apply eLpNorm_input_deformation_left_coeff_le_one f hr hs ha₀'
    simpa only [ENNReal.ofReal_toReal hp_top] using hf
private theorem eLpNorm_input_deformation_right_coeff_ennreal_le_one
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) {p p₁ : ENNReal} {a₀ a₁ t : ℝ}
    (hp : 1 ≤ p) (hp₁ : 1 ≤ p₁) (hp_top : p ≠ ∞)
    (ha₁ : a₁ = p.toReal * (p₁⁻¹).toReal)
    (hf : eLpNorm (f : X → ℂ) p μ ≤ 1) :
    eLpNorm (f.map (fun c ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I) +
          (a₀ : ℂ)) * ((Real.log ‖c‖ : ℝ) : ℂ))): X → ℂ) p₁ μ ≤ 1 := by
  by_cases hp₁_top : p₁ = ∞
  · have ha₁_zero : a₁ = 0 := by simpa [hp₁_top] using ha₁
    simpa [hp₁_top] using
      eLpNorm_input_deformation_right_coeff_top (μ := μ) f (a₀ := a₀) (t := t) ha₁_zero
  · have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
    have hp₁0 : p₁ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp₁)
    have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
    have hs : 0 < p₁.toReal := ENNReal.toReal_pos hp₁0 hp₁_top
    have ha₁' : a₁ = p.toReal / p₁.toReal := by
      rw [← toReal_mul_toReal_inv_eq_div]
      exact ha₁
    rw [← ENNReal.ofReal_toReal hp₁_top]
    apply eLpNorm_input_deformation_right_coeff_le_one f hr hs ha₁'
    simpa only [ENNReal.ofReal_toReal hp_top] using hf
section
end
end Auto
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution
    {m : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p₀ p₁ p : Fin (m + 1) → ENNReal} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp₀ : ∀ i, 1 ≤ p₀ i) (hp₁ : ∀ i, 1 ≤ p₁ i) (hp : ∀ i, 1 ≤ p i)
    (hp_top : ∀ i, p i ≠ ∞)
    (hint : ∀ i, (p i)⁻¹ = ENNReal.ofReal (1 - θ) * (p₀ i)⁻¹ +
      ENNReal.ofReal θ * (p₁ i)⁻¹)
    (g : Fin m → SimpleFunc X ℂ)
    (hg : ∀ i, Integrable (g i : X → ℂ) μ)
    (hgnorm : ∀ i, eLpNorm (g i : X → ℂ) (p i.succ) μ ≤ 1) :
    (∀ i, aux_multilinear_input_deformation p₀ p₁ p g (θ : ℂ) i = g i) ∧
    (∀ (z : verticalClosedStrip 0 1) i,
      Integrable (aux_multilinear_input_deformation p₀ p₁ p g z i : X → ℂ) μ) ∧
    (∀ (t : ℝ) i, eLpNorm
      (aux_multilinear_input_deformation p₀ p₁ p g ((t : ℂ) * Complex.I) i : X → ℂ)
        (p₀ i.succ) μ ≤ 1) ∧
    (∀ (t : ℝ) i, eLpNorm
      (aux_multilinear_input_deformation p₀ p₁ p g (1 + (t : ℂ) * Complex.I) i : X → ℂ)
        (p₁ i.succ) μ ≤ 1) := by
  constructor
  · intro i
    dsimp only [aux_multilinear_input_deformation]
    apply simpleFunc_input_deformation_at_theta
    apply input_coeff_at_theta_of_interp_general hθ (hp i.succ) (hp₀ i.succ)
      (hp₁ i.succ) (hp_top i.succ) (hint i.succ)
  constructor
  · intro z i
    apply integrable_map_of_integrable (g i) (hg i)
    simp
  constructor
  · intro t i
    dsimp only [aux_multilinear_input_deformation]
    apply eLpNorm_input_deformation_left_coeff_ennreal_le_one
      (p := p i.succ) (p₀ := p₀ i.succ)
    · exact hp i.succ
    · exact hp₀ i.succ
    · exact hp_top i.succ
    · rfl
    · exact hgnorm i
  · intro t i
    dsimp only [aux_multilinear_input_deformation]
    apply eLpNorm_input_deformation_right_coeff_ennreal_le_one
      (p := p i.succ) (p₁ := p₁ i.succ)
    · exact hp i.succ
    · exact hp₁ i.succ
    · exact hp_top i.succ
    · rfl
    · exact hgnorm i
end Auto
