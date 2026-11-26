-- Prove2me | solution 1 for Auto.sqrtOneMinusGaussian_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:10:19.272871+00:00
-- url     : https://prove2.me/submissions/e9311914-3578-4f46-8ee0-85d5507c1747

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
public import Theorems.Thm_Auto_aux_one_sub_gaussian_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) (_hx : 1 / 2 ≤ |x|) :
    1 - gaussian x ≤ sqrtOneMinusGaussian x ∧ sqrtOneMinusGaussian x ≤ 1 := by
  let y := 1 - gaussian x
  have hy0 : 0 ≤ y := aux_one_sub_gaussian_nonneg x
  have hy1 : y ≤ 1 := by
    dsimp [y]
    have hgpos : 0 < gaussian x := by
      rw [show gaussian x = Real.exp (-Real.pi * x ^ 2) by rfl]
      exact Real.exp_pos _
    linarith
  have hsqrt : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
  have hsqrtnonneg : 0 ≤ Real.sqrt y := Real.sqrt_nonneg _
  constructor
  · change y ≤ Real.sqrt y
    nlinarith
  · change Real.sqrt y ≤ 1
    nlinarith
end Auto
