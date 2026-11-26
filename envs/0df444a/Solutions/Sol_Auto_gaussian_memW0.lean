-- Prove2me | solution 1 for Auto.gaussian_memW0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:09:18.847642+00:00
-- url     : https://prove2.me/submissions/7a254bcf-a3c9-4787-b7e7-a2aa796409f8

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
public import Theorems.Thm_Auto_gaussian_continuous
public import Theorems.Thm_Auto_aux_wienerEnvelope_gaussian_le
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_continuous_wienerEnvelope


set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution : MemW0 gaussian := by
  refine ⟨gaussian_continuous, ?_⟩
  have hmajorant : Integrable (fun x : ℝ =>
      Real.exp Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < Real.pi / 2)).const_mul (Real.exp Real.pi)
  refine hmajorant.mono_nonneg
    (continuous_wienerEnvelope gaussian_continuous 1).aestronglyMeasurable
    (ae_of_all _ fun x => aux_wienerEnvelope_nonneg gaussian_continuous zero_le_one x)
    (ae_of_all _ aux_wienerEnvelope_gaussian_le)
end Auto
