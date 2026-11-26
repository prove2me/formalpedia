-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBDerivative_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:46.378823+00:00
-- url     : https://prove2.me/submissions/a76bf943-6f56-47d7-bde8-a5c4953ad8ca

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
public import Theorems.Thm_Auto_aux_poissonFrequency_integrable
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_continuous
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_norm_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    Integrable auxiliaryFunctionBDerivative := by
  have hgaussian : Integrable (fun x : ℝ =>
      Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)) := by
    simpa using
      (integrable_exp_neg_mul_sq (by positivity : 0 < Real.pi / 2)).const_mul
        (Real.sqrt Real.pi)
  have habel : Integrable (fun x : ℝ =>
      Real.sqrt Real.pi * aux_poissonFrequency x) := by
    simpa using aux_poissonFrequency_integrable.const_mul (Real.sqrt Real.pi)
  have hmajorant : Integrable (fun x : ℝ =>
      Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.sqrt Real.pi * aux_poissonFrequency x) := hgaussian.add habel
  exact hmajorant.mono' aux_auxiliaryFunctionBDerivative_continuous.aestronglyMeasurable
    (ae_of_all _ aux_auxiliaryFunctionBDerivative_norm_le)
end Auto
