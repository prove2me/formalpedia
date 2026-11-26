-- Prove2me | solution 1 for Auto.aux_gaussianRescale_complete_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:56:24.016813+00:00
-- url     : https://prove2.me/submissions/cdbc93d4-0a66-4fe9-81bc-be454ef0121c

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
theorem _root_.solution (a μ x y : ℝ) (ha : 0 < a) (hμ : 0 < μ) :
    gaussianRescale a (x - y) * gaussianRescale μ y =
      (a⁻¹ * μ⁻¹ * Real.exp (-Real.pi * x ^ 2 / (a ^ 2 + μ ^ 2))) *
        Real.exp (-(Real.pi * (a ^ 2 + μ ^ 2) / (a ^ 2 * μ ^ 2)) *
          (y - μ ^ 2 / (a ^ 2 + μ ^ 2) * x) ^ 2) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hs : a ^ 2 + μ ^ 2 ≠ 0 := by positivity
  unfold gaussianRescale
  simp only [gaussian, Auto.gaussian]
  calc
    a⁻¹ * Real.exp (-Real.pi * (a⁻¹ * (x - y)) ^ 2) *
          (μ⁻¹ * Real.exp (-Real.pi * (μ⁻¹ * y) ^ 2)) =
        a⁻¹ * μ⁻¹ * Real.exp
          (-Real.pi * (a⁻¹ * (x - y)) ^ 2 + -Real.pi * (μ⁻¹ * y) ^ 2) := by
      calc
        _ = a⁻¹ * μ⁻¹ *
            (Real.exp (-Real.pi * (a⁻¹ * (x - y)) ^ 2) *
              Real.exp (-Real.pi * (μ⁻¹ * y) ^ 2)) := by ring
        _ = _ := by rw [← Real.exp_add]
    _ = a⁻¹ * μ⁻¹ * (Real.exp (-Real.pi * x ^ 2 / (a ^ 2 + μ ^ 2)) *
        Real.exp (-(Real.pi * (a ^ 2 + μ ^ 2) / (a ^ 2 * μ ^ 2)) *
          (y - μ ^ 2 / (a ^ 2 + μ ^ 2) * x) ^ 2)) := by
      rw [← Real.exp_add]
      congr 2
      field_simp
      ring
    _ = (a⁻¹ * μ⁻¹ * Real.exp (-Real.pi * x ^ 2 / (a ^ 2 + μ ^ 2))) *
        Real.exp (-(Real.pi * (a ^ 2 + μ ^ 2) / (a ^ 2 * μ ^ 2)) *
          (y - μ ^ 2 / (a ^ 2 + μ ^ 2) * x) ^ 2) := by ring
end Auto
