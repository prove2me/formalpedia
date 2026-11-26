-- Prove2me | solution 1 for Auto.stein_interpolation_constant_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:08:39.957696+00:00
-- url     : https://prove2.me/submissions/8430aee5-781c-44b3-99cf-ca78fd118823

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
public import Theorems.Thm_Auto_stein_interpolation
section
@[expose] public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
namespace Auto
private theorem affine_kernel (c s : ℝ) (hs : 0 < s) :
    (∫ u in Ioi 0, ((u - c) ^ 2 + s ^ 2)⁻¹) =
      s⁻¹ * (Real.pi / 2 - Real.arctan (-c / s)) := by
  let φ : ℝ → ℝ := fun x => s * x + c
  have hφ_image : φ '' Ioi (-c / s) = Ioi 0 := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      change -c / s < x at hx
      dsimp [φ]
      have hzero : s * (-c / s) + c = 0 := by
        field_simp
        ring
      have hmul := mul_lt_mul_of_pos_left hx hs
      calc
        0 = s * (-c / s) + c := hzero.symm
        _ < s * x + c := by linarith
    · intro hu
      change 0 < u at hu
      refine ⟨(u - c) / s, ?_, ?_⟩
      · change -c / s < (u - c) / s
        rw [div_lt_div_iff_of_pos_right hs]
        linarith
      · dsimp [φ]
        field_simp
        ring
  have hφ_deriv : ∀ x ∈ Ioi (-c / s),
      HasDerivWithinAt φ s (Ioi (-c / s)) x := by
    intro x hx
    exact (hasDerivAt_const_mul (x := x) s).add_const c |>.hasDerivWithinAt
  have hcv := integral_image_eq_integral_abs_deriv_smul
    (s := Ioi (-c / s)) measurableSet_Ioi hφ_deriv (fun x _ y _ hxy => by
      dsimp [φ] at hxy
      apply mul_left_cancel₀ hs.ne'
      linarith) (fun u : ℝ => ((u - c) ^ 2 + s ^ 2)⁻¹)
  rw [hφ_image] at hcv
  calc
    (∫ u in Ioi 0, ((u - c) ^ 2 + s ^ 2)⁻¹) =
        ∫ x in Ioi (-c / s), |s| • ((φ x - c) ^ 2 + s ^ 2)⁻¹ := hcv
    _ = ∫ x in Ioi (-c / s), s⁻¹ * (1 + x ^ 2)⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp [φ]
      rw [abs_of_pos hs]
      field_simp [hs.ne']
      ring
    _ = s⁻¹ * (Real.pi / 2 - Real.arctan (-c / s)) := by
      rw [integral_const_mul, integral_Ioi_inv_one_add_sq]
private theorem kernel_left_raw (a : ℝ) (ha0 : 0 < a) (hapi : a < Real.pi) :
    (∫ t : ℝ, (Real.cosh (Real.pi * t) - Real.cos a)⁻¹) =
      2 * (Real.pi - a) / (Real.pi * Real.sin a) := by
  let ψ : ℝ → ℝ := fun t => Real.exp (Real.pi * t)
  have hψ_image : ψ '' Set.univ = Set.Ioi 0 := by
    ext u
    constructor
    · rintro ⟨t, -, rfl⟩
      exact Real.exp_pos _
    · intro hu
      refine ⟨Real.log u / Real.pi, Set.mem_univ _, ?_⟩
      dsimp [ψ]
      rw [mul_div_cancel₀ _ Real.pi_ne_zero, Real.exp_log hu]
  have hψ_deriv : ∀ t ∈ Set.univ,
      HasDerivWithinAt ψ (Real.exp (Real.pi * t) * Real.pi) Set.univ t := by
    intro t ht
    exact ((Real.hasDerivAt_exp (Real.pi * t)).comp t
      (hasDerivAt_const_mul (x := t) Real.pi)).hasDerivWithinAt
  have hψ_inj : Set.InjOn ψ Set.univ := by
    intro x hx y hy hxy
    dsimp [ψ] at hxy
    have hxy' := Real.exp_injective hxy
    nlinarith [Real.pi_pos]
  let g : ℝ → ℝ := fun u => 2 / (Real.pi * (u ^ 2 - 2 * Real.cos a * u + 1))
  have hcv := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) MeasurableSet.univ hψ_deriv hψ_inj g
  rw [hψ_image] at hcv
  have hsin : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hchange :
      (∫ t : ℝ, (Real.cosh (Real.pi * t) - Real.cos a)⁻¹) =
        ∫ t in Set.univ, |Real.exp (Real.pi * t) * Real.pi| • g (ψ t) := by
    rw [← setIntegral_univ]
    apply integral_congr_ae
    filter_upwards with t
    let u : ℝ := Real.exp (Real.pi * t)
    have hu : 0 < u := Real.exp_pos _
    have hD : 0 < u ^ 2 - 2 * Real.cos a * u + 1 := by
      calc
        u ^ 2 - 2 * Real.cos a * u + 1 = (u - Real.cos a) ^ 2 + (Real.sin a) ^ 2 := by
          nlinarith [Real.sin_sq_add_cos_sq a]
        _ > 0 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hsin)
    have hcosh : Real.cosh (Real.pi * t) - Real.cos a =
        (u ^ 2 - 2 * Real.cos a * u + 1) / (2 * u) := by
      dsimp [u]
      rw [Real.cosh_eq, Real.exp_neg]
      field_simp [hu.ne']
      ring
    change (Real.cosh (Real.pi * t) - Real.cos a)⁻¹ =
      |Real.exp (Real.pi * t) * Real.pi| * g (Real.exp (Real.pi * t))
    dsimp [g]
    rw [abs_of_pos (mul_pos hu Real.pi_pos)]
    change (Real.cosh (Real.pi * t) - Real.cos a)⁻¹ =
      (u * Real.pi) * (2 / (Real.pi * (u ^ 2 - 2 * Real.cos a * u + 1)))
    rw [hcosh]
    field_simp [hu.ne', hD.ne', Real.pi_ne_zero]
  calc
    (∫ t : ℝ, (Real.cosh (Real.pi * t) - Real.cos a)⁻¹) =
        ∫ t in Set.univ, |Real.exp (Real.pi * t) * Real.pi| • g (ψ t) := hchange
    _ = ∫ u in Set.Ioi 0, g u := hcv.symm
    _ = ∫ u in Set.Ioi 0, (2 / Real.pi) *
        ((u - Real.cos a) ^ 2 + (Real.sin a) ^ 2)⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp [g]
      have hD : u ^ 2 - 2 * Real.cos a * u + 1 =
          (u - Real.cos a) ^ 2 + (Real.sin a) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq a]
      rw [hD]
      field_simp [Real.pi_ne_zero]
    _ = (2 / Real.pi) * (∫ u in Set.Ioi 0,
        ((u - Real.cos a) ^ 2 + (Real.sin a) ^ 2)⁻¹) := by
      rw [integral_const_mul]
    _ = (2 / Real.pi) *
        ((Real.sin a)⁻¹ * (Real.pi / 2 - Real.arctan (-Real.cos a / Real.sin a))) := by
      rw [affine_kernel (Real.cos a) (Real.sin a) hsin]
    _ = 2 * (Real.pi - a) / (Real.pi * Real.sin a) := by
      have harctan : Real.arctan (-Real.cos a / Real.sin a) = a - Real.pi / 2 := by
        calc
          Real.arctan (-Real.cos a / Real.sin a) =
              Real.arctan (Real.tan (a - Real.pi / 2)) := by
            congr 1
            rw [show a - Real.pi / 2 = -(Real.pi / 2 - a) by ring,
              Real.tan_neg, Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos]
            field_simp [hsin.ne']
          _ = a - Real.pi / 2 := Real.arctan_tan (by linarith [Real.pi_pos])
            (by linarith [Real.pi_pos])
      rw [harctan]
      field_simp [hsin.ne', Real.pi_ne_zero]
      ring
private theorem kernel_left_normalized {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) :
    (Real.sin (Real.pi * θ) / 2) *
        (∫ t : ℝ, (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))⁻¹) =
      1 - θ := by
  have ha0 : 0 < Real.pi * θ := mul_pos Real.pi_pos hθ.1
  have hapi : Real.pi * θ < Real.pi := by
    calc
      Real.pi * θ < Real.pi * 1 := mul_lt_mul_of_pos_left hθ.2 Real.pi_pos
      _ = Real.pi := mul_one _
  have hsin : 0 < Real.sin (Real.pi * θ) :=
    Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  rw [kernel_left_raw (Real.pi * θ) ha0 hapi]
  field_simp [hsin.ne', Real.pi_ne_zero]
private theorem kernel_right_normalized {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) :
    (Real.sin (Real.pi * θ) / 2) *
        (∫ t : ℝ, (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))⁻¹) =
      θ := by
  have hθ' : 1 - θ ∈ Set.Ioo 0 1 := by
    constructor <;> linarith [hθ.1, hθ.2]
  have h := kernel_left_normalized hθ'
  have harg : Real.pi * (1 - θ) = Real.pi - Real.pi * θ := by ring
  rw [harg, Real.sin_pi_sub, Real.cos_pi_sub] at h
  simpa [sub_neg_eq_add, sub_sub] using h
private theorem integrable_kernel_left {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) :
    Integrable (fun t : ℝ =>
      (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))⁻¹) := by
  have ha0 : 0 < Real.pi * θ := mul_pos Real.pi_pos hθ.1
  have hapi : Real.pi * θ < Real.pi := by
    calc
      Real.pi * θ < Real.pi * 1 := mul_lt_mul_of_pos_left hθ.2 Real.pi_pos
      _ = Real.pi := mul_one _
  have hsin : 0 < Real.sin (Real.pi * θ) :=
    Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  by_contra h
  have hzero := integral_undef h
  rw [kernel_left_raw (Real.pi * θ) ha0 hapi] at hzero
  have hpos : 0 < 2 * (Real.pi - Real.pi * θ) /
      (Real.pi * Real.sin (Real.pi * θ)) := by positivity
  linarith
private theorem integrable_kernel_right {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1) :
    Integrable (fun t : ℝ =>
      (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))⁻¹) := by
  have hθ' : 1 - θ ∈ Set.Ioo 0 1 := by
    constructor <;> linarith [hθ.1, hθ.2]
  have harg : Real.pi * (1 - θ) = Real.pi - Real.pi * θ := by ring
  have h := integrable_kernel_left hθ'
  rw [harg, Real.cos_pi_sub] at h
  simpa only [sub_neg_eq_add] using h
private theorem constant_kernel_factor {θ M₀ M₁ : ℝ} (hθ : θ ∈ Set.Ioo 0 1)
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) :
    Real.exp
        ((Real.sin (Real.pi * θ) / 2) *
          ∫ t : ℝ,
            Real.log M₀ / (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)) +
              Real.log M₁ / (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) =
      Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ := by
  have hk₀ := integrable_kernel_left hθ
  have hk₁ := integrable_kernel_right hθ
  have h₀ : Integrable (fun t : ℝ =>
      Real.log M₀ / (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) := by
    simpa only [div_eq_mul_inv] using hk₀.const_mul (Real.log M₀)
  have h₁ : Integrable (fun t : ℝ =>
      Real.log M₁ / (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
    simpa only [div_eq_mul_inv] using hk₁.const_mul (Real.log M₁)
  rw [integral_add h₀ h₁]
  simp only [div_eq_mul_inv, integral_const_mul]
  let I₀ : ℝ := ∫ t : ℝ,
    (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))⁻¹
  let I₁ : ℝ := ∫ t : ℝ,
    (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))⁻¹
  change Real.exp
      ((Real.sin (Real.pi * θ) * (2 : ℝ)⁻¹) *
        (Real.log M₀ * I₀ + Real.log M₁ * I₁)) =
    Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ
  have hleft := kernel_left_normalized hθ
  have hright := kernel_right_normalized hθ
  change (Real.sin (Real.pi * θ) / 2) * I₀ = 1 - θ at hleft
  change (Real.sin (Real.pi * θ) / 2) * I₁ = θ at hright
  have hcombine :
      (Real.sin (Real.pi * θ) * (2 : ℝ)⁻¹) *
          (Real.log M₀ * I₀ + Real.log M₁ * I₁) =
        Real.log M₀ * ((Real.sin (Real.pi * θ) / 2) * I₀) +
          Real.log M₁ * ((Real.sin (Real.pi * θ) / 2) * I₁) := by ring
  rw [hcombine, hleft, hright, Real.exp_add,
    ← Real.rpow_def_of_pos hM₀, ← Real.rpow_def_of_pos hM₁]
  rfl
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
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    {p₀ p₁ p q₀ q₁ q : ENNReal} {θ M₀ M₁ : ℝ}
    (T : ℂ → SimpleFunc X ℂ → Y → ℂ)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (hT_add : ∀ (z : verticalClosedStrip 0 1) (f g : SimpleFunc X ℂ),
      Integrable f μ → Integrable g μ → T z (f + g) = T z f + T z g)
    (hT_smul : ∀ (z : verticalClosedStrip 0 1) (c : ℂ) (f : SimpleFunc X ℂ),
      Integrable f μ → T z (c • f) = c • T z f)
    (hT_measurable : ∀ (z : verticalClosedStrip 0 1) (f : SimpleFunc X ℂ),
      Integrable f μ → Measurable (T z f))
    (hpair_integrable : ∀ (z : verticalClosedStrip 0 1)
      (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable f μ → Integrable g ν → Integrable (fun y ↦ T z f y * g y) ν)
    (hanalytic : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable f μ → Integrable g ν →
      DiffContOnCl ℂ (fun z ↦ ∫ y, T z f y * g y ∂ν) (verticalStrip 0 1))
    (hfamily_growth : ∃ a : ℝ, a < Real.pi ∧
      ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
        Integrable f μ → Integrable g ν →
        ∃ C : ℝ, ∀ z : verticalClosedStrip 0 1,
          ‖∫ y, T z f y * g y ∂ν‖ ≤ exp (C * exp (a * |(z : ℂ).im|)))
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hbound₀ : ∀ (t : ℝ) (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T ((t : ℂ) * Complex.I) f) q₀ ν ≤
        ENNReal.ofReal M₀ * eLpNorm (f : X → ℂ) p₀ μ)
    (hbound₁ : ∀ (t : ℝ) (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T (1 + (t : ℂ) * Complex.I) f) q₁ ν ≤
        ENNReal.ofReal M₁ * eLpNorm (f : X → ℂ) p₁ μ) :
    ∀ f : SimpleFunc X ℂ, Integrable f μ →
      MemLp (T (θ : ℂ) f) q ν ∧
      eLpNorm (T (θ : ℂ) f) q ν ≤
        ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
          eLpNorm (f : X → ℂ) p μ := by
  intro f hf
  obtain ⟨hmem, hnorm⟩ := stein_interpolation T hp₀ hp₁ hq₀ hq₁ hθ hp hq hT_add hT_smul
    hT_measurable hpair_integrable hanalytic hfamily_growth
    ⟨measurable_const, measurable_const⟩ (fun t ↦ ⟨hM₀, hM₁⟩)
    ⟨0, max |Real.log M₀| |Real.log M₁|, Real.pi_pos,
      fun t ↦ by simp⟩
    (fun t g hg ↦ by simpa using hbound₀ t g hg)
    (fun t g hg ↦ by simpa using hbound₁ t g hg) f hf
  refine ⟨hmem, ?_⟩
  simpa [constant_kernel_factor hθ hM₀ hM₁] using hnorm
end Auto
