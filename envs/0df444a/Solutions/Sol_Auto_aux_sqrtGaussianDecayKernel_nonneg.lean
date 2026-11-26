-- Prove2me | solution 1 for Auto.aux_sqrtGaussianDecayKernel_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:06:39.431671+00:00
-- url     : https://prove2.me/submissions/af099d9c-317d-4835-a145-c568e524ea1f

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
public import Theorems.Thm_Auto_aux_sqrtGaussianCoefficient_nonneg
public import Theorems.Thm_Auto_aux_sqrtGaussianDecayKernel_hasSum

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    0 ≤ aux_sqrtGaussianDecayKernel x := by
  rw [← (aux_sqrtGaussianDecayKernel_hasSum x).tsum_eq]
  apply tsum_nonneg
  intro n
  unfold gaussianRescale
  exact mul_nonneg (aux_sqrtGaussianCoefficient_nonneg n)
    (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (aux_gaussian_pos _).le)
end Auto
