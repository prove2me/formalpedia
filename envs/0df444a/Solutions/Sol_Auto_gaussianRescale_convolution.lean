-- Prove2me | solution 1 for Auto.gaussianRescale_convolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:09:23.882254+00:00
-- url     : https://prove2.me/submissions/71bd2f57-87d5-42fc-b38c-2bd40216e991

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
public import Theorems.Thm_Auto_aux_gaussianRescale_complete_square
public import Theorems.Thm_Auto_aux_integral_gaussian_shift

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (a μ : ℝ) (ha : 0 < a) (hμ : 0 < μ) (x : ℝ) :
    (∫ y : ℝ, gaussianRescale a (x - y) * gaussianRescale μ y) =
      gaussianRescale (Real.sqrt (a ^ 2 + μ ^ 2)) x := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hspos : 0 < a ^ 2 + μ ^ 2 := by positivity
  have hs0 : a ^ 2 + μ ^ 2 ≠ 0 := ne_of_gt hspos
  let B : ℝ := Real.pi * (a ^ 2 + μ ^ 2) / (a ^ 2 * μ ^ 2)
  let c : ℝ := μ ^ 2 / (a ^ 2 + μ ^ 2) * x
  let C : ℝ := a⁻¹ * μ⁻¹ * Real.exp (-Real.pi * x ^ 2 / (a ^ 2 + μ ^ 2))
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hpoint (y : ℝ) : gaussianRescale a (x - y) * gaussianRescale μ y =
      C * Real.exp (-B * (y - c) ^ 2) := by
    dsimp [B, c, C]
    exact aux_gaussianRescale_complete_square a μ x y ha hμ
  have hshift : (∫ y : ℝ, Real.exp (-B * (y - c) ^ 2)) =
      ∫ y : ℝ, Real.exp (-B * y ^ 2) := aux_integral_gaussian_shift B c
  have hint : (∫ y : ℝ, Real.exp (-B * (y - c) ^ 2)) =
      Real.sqrt (Real.pi / B) := by
    rw [hshift]
    exact integral_gaussian B
  calc
    (∫ y : ℝ, gaussianRescale a (x - y) * gaussianRescale μ y) =
        ∫ y : ℝ, C * Real.exp (-B * (y - c) ^ 2) := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact hpoint y
    _ = C * ∫ y : ℝ, Real.exp (-B * (y - c) ^ 2) :=
      integral_const_mul C _
    _ = C * Real.sqrt (Real.pi / B) := by rw [hint]
    _ = gaussianRescale (Real.sqrt (a ^ 2 + μ ^ 2)) x := by
      dsimp [B, C]
      have hsqrtpos : 0 < Real.sqrt (a ^ 2 + μ ^ 2) := Real.sqrt_pos.2 hspos
      have hsqrt0 : Real.sqrt (a ^ 2 + μ ^ 2) ≠ 0 := ne_of_gt hsqrtpos
      have hinside : Real.pi / (Real.pi * (a ^ 2 + μ ^ 2) / (a ^ 2 * μ ^ 2)) =
          (a * μ / Real.sqrt (a ^ 2 + μ ^ 2)) ^ 2 := by
        field_simp
        rw [Real.sq_sqrt hspos.le]
      rw [hinside, Real.sqrt_sq_eq_abs,
        abs_of_pos (div_pos (mul_pos ha hμ) hsqrtpos)]
      unfold gaussianRescale
      simp only [gaussian, Auto.gaussian]
      have hexp : -Real.pi * x ^ 2 / (a ^ 2 + μ ^ 2) =
          -Real.pi * ((Real.sqrt (a ^ 2 + μ ^ 2))⁻¹ * x) ^ 2 := by
        field_simp
        rw [Real.sq_sqrt hspos.le]
      rw [hexp]
      field_simp
end Auto
