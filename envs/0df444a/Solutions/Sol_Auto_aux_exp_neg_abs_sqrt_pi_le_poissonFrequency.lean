-- Prove2me | solution 1 for Auto.aux_exp_neg_abs_sqrt_pi_le_poissonFrequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:42:38.102002+00:00
-- url     : https://prove2.me/submissions/b2461c70-ece2-43bd-8d22-16042df02ac2

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
theorem _root_.solution (x : ℝ) :
    Real.exp (-|Real.sqrt Real.pi * x|) ≤ aux_poissonFrequency x := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt Real.pi ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  have hsqrt_ge_one : 1 ≤ Real.sqrt Real.pi := by
    nlinarith [Real.pi_gt_three]
  unfold aux_poissonFrequency
  apply Real.exp_le_exp.mpr
  rw [abs_mul, abs_of_nonneg hsqrt_nonneg]
  nlinarith [abs_nonneg x]
end Auto
