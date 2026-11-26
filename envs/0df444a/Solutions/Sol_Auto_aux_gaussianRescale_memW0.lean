-- Prove2me | solution 1 for Auto.aux_gaussianRescale_memW0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:09:19.35999+00:00
-- url     : https://prove2.me/submissions/77319633-40cc-4b8d-9e7d-8805d3b08742

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
public import Theorems.Thm_Auto_aux_wienerEnvelope_gaussianRescale_le
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
theorem _root_.solution {t : ℝ} (ht : 0 < t) : MemW0 (gaussianRescale t) := by
  have hcontinuous : Continuous (gaussianRescale t) := by
    unfold gaussianRescale
    exact continuous_const.mul
      (gaussian_continuous.comp (continuous_const.mul continuous_id))
  refine ⟨hcontinuous, ?_⟩
  have hcoefficient : 0 < Real.pi / 2 * t⁻¹ ^ 2 := by
    positivity
  have hmajorant : Integrable (fun x : ℝ =>
      t⁻¹ * Real.exp (Real.pi * t⁻¹ ^ 2) *
        Real.exp (-(Real.pi / 2) * (t⁻¹ * x) ^ 2)) := by
    have hbase := (integrable_exp_neg_mul_sq hcoefficient).const_mul
      (t⁻¹ * Real.exp (Real.pi * t⁻¹ ^ 2))
    convert hbase using 1
    funext x
    congr 2
    ring
  refine hmajorant.mono_nonneg
    (continuous_wienerEnvelope hcontinuous 1).aestronglyMeasurable
    (ae_of_all _ fun x => aux_wienerEnvelope_nonneg hcontinuous zero_le_one x)
    (ae_of_all _ fun x => aux_wienerEnvelope_gaussianRescale_le ht x)
end Auto
