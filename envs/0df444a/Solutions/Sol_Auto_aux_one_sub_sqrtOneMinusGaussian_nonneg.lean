-- Prove2me | solution 1 for Auto.aux_one_sub_sqrtOneMinusGaussian_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:45:02.266449+00:00
-- url     : https://prove2.me/submissions/d9a3e0e6-d01a-432d-85af-9e72f525c255

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
public import Theorems.Thm_Auto_aux_gaussian_pos
public import Theorems.Thm_Auto_aux_one_sub_gaussian_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    0 ≤ 1 - sqrtOneMinusGaussian x := by
  have hrad : 0 ≤ 1 - gaussian x := aux_one_sub_gaussian_nonneg x
  have hsquare : sqrtOneMinusGaussian x ^ 2 = 1 - gaussian x :=
    Real.sq_sqrt hrad
  have hsqrt : 0 ≤ sqrtOneMinusGaussian x := Real.sqrt_nonneg _
  have hgauss : 0 < gaussian x := aux_gaussian_pos x
  nlinarith
end Auto
