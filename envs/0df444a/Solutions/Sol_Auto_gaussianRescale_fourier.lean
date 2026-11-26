-- Prove2me | solution 1 for Auto.gaussianRescale_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:09:28.217949+00:00
-- url     : https://prove2.me/submissions/cc1218ca-1ba6-4231-8b82-01ad85380f1d

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_Notation
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Definitions.Def_LeanNct_Auto_Preliminaries_Gaussians

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (a : ℝ) (ha : 0 < a) :
    FourierTransform.fourier (fun x : ℝ => (gaussianRescale a x : ℂ)) =
      fun ξ : ℝ => (gaussian (a * ξ) : ℂ) := by
  let b : ℂ := ((a⁻¹ ^ 2 : ℝ) : ℂ)
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb : 0 < b.re := by
    dsimp [b]
    positivity
  have hinput : (fun x : ℝ => (gaussianRescale a x : ℂ)) =
      (a⁻¹ : ℂ) • (fun x : ℝ => Complex.exp (-Real.pi * b * (x : ℂ) ^ 2)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    simp [gaussianRescale, gaussian, Auto.gaussian, b, Complex.ofReal_exp, ha0]
    congr 1
    ring
  rw [hinput]
  calc
    FourierTransform.fourier
        ((a⁻¹ : ℂ) • fun x : ℝ => Complex.exp (-Real.pi * b * (x : ℂ) ^ 2)) =
        (a⁻¹ : ℂ) • FourierTransform.fourier
          (fun x : ℝ => Complex.exp (-Real.pi * b * (x : ℂ) ^ 2)) := by
      change VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
          ((a⁻¹ : ℂ) • fun x : ℝ => Complex.exp (-Real.pi * b * (x : ℂ) ^ 2)) =
        (a⁻¹ : ℂ) • VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
          (fun x : ℝ => Complex.exp (-Real.pi * b * (x : ℂ) ^ 2))
      rw [VectorFourier.fourierIntegral_const_smul]
    _ = (a⁻¹ : ℂ) • (fun ξ : ℝ =>
        1 / b ^ (1 / 2 : ℂ) * Complex.exp (-Real.pi / b * (ξ : ℂ) ^ 2)) := by
      rw [fourier_gaussian_pi hb]
    _ = fun ξ : ℝ => (gaussian (a * ξ) : ℂ) := by
      funext ξ
      dsimp [b]
      have hpow_real : (a⁻¹ ^ 2 : ℝ) ^ ((1 : ℝ) / 2) = a⁻¹ := by
        rw [← Real.sqrt_eq_rpow]
        rw [Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr ha)]
      have hpow : ((a⁻¹ ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (a⁻¹ : ℂ) := by
        have hpow' := Complex.ofReal_cpow (sq_nonneg a⁻¹) ((1 : ℝ) / 2)
        have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
        rw [hhalf, ← hpow']
        exact_mod_cast hpow_real
      have hexp : -Real.pi / ((a⁻¹ ^ 2 : ℝ) : ℂ) * (ξ : ℂ) ^ 2 =
          (-Real.pi * (a * ξ) ^ 2 : ℝ) := by
        push_cast
        field_simp
      rw [hpow, hexp]
      simp [gaussian, Auto.gaussian, Complex.ofReal_exp, ha0]
end Auto
