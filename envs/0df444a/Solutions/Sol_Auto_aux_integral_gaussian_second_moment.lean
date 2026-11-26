-- Prove2me | solution 1 for Auto.aux_integral_gaussian_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:54.328106+00:00
-- url     : https://prove2.me/submissions/403a5b81-2120-4503-8cdd-f6efd163d6c9

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
public import Theorems.Thm_Auto_aux_gaussian_hasDerivAt
public import Theorems.Thm_Auto_aux_gaussian_integrable
public import Theorems.Thm_Auto_aux_integral_gaussian
public import Theorems.Thm_Auto_aux_sq_mul_gaussian_integrable

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    (∫ x : ℝ, x ^ 2 * gaussian x) = (2 * Real.pi)⁻¹ := by
  have hlin : Integrable (fun x : ℝ => x * gaussian x) := by
    simpa [gaussian, Auto.gaussian] using
      (integrable_mul_exp_neg_mul_sq (b := Real.pi) Real.pi_pos)
  have hderiv : Integrable (fun x : ℝ => x * (fderiv ℝ gaussian x) 1) := by
    convert aux_sq_mul_gaussian_integrable.const_mul (-(2 * Real.pi)) using 1
    funext x
    rw [(aux_gaussian_hasDerivAt x).hasFDerivAt.fderiv]
    simp [smul_eq_mul]
    ring
  have hfirst : Integrable (fun x : ℝ => (fderiv ℝ id x) 1 * gaussian x) := by
    convert aux_gaussian_integrable using 1
    funext x
    simp
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := id) (g := gaussian) (v := (1 : ℝ))
    hfirst hderiv hlin
    (fun x _ => differentiableAt_id)
    (fun x _ => (aux_gaussian_hasDerivAt x).differentiableAt)
  simp only [id, fderiv_id, ContinuousLinearMap.id_apply, one_mul] at hparts
  simp_rw [(aux_gaussian_hasDerivAt _).hasFDerivAt.fderiv] at hparts
  simp only [neg_mul, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_neg,
    one_mul] at hparts
  rw [integral_neg, aux_integral_gaussian] at hparts
  have hmul : (∫ x : ℝ, x * (2 * Real.pi * x * gaussian x)) = 1 := by
    linarith
  have hmoment : (2 * Real.pi) * ∫ x : ℝ, x ^ 2 * gaussian x = 1 := by
    calc
      (2 * Real.pi) * ∫ x : ℝ, x ^ 2 * gaussian x =
          ∫ x : ℝ, x * (2 * Real.pi * x * gaussian x) := by
        rw [← integral_const_mul]
        congr 1
        funext x
        ring
      _ = 1 := hmul
  have hp : 2 * Real.pi ≠ 0 := by positivity
  field_simp [hp]
  linarith [hmoment]
end Auto
