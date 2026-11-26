-- Prove2me | solution 1 for Auto.aux_poissonKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:55.427101+00:00
-- url     : https://prove2.me/submissions/41d74a81-db1d-4c82-be5a-66861d058297

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
public import Theorems.Thm_Auto_aux_poissonKernel_continuous

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution : Integrable poissonKernel := by
  have hmajorant : Integrable (fun x : ℝ => 2 * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 2
  refine hmajorant.mono_nonneg aux_poissonKernel_continuous.aestronglyMeasurable
    (ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · unfold poissonKernel
    positivity
  · unfold poissonKernel
    have hscale : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hsq : x ^ 2 ≤ (2 * Real.pi * x) ^ 2 := by
      calc
        x ^ 2 = 1 * x ^ 2 := by ring
        _ ≤ (2 * Real.pi) ^ 2 * x ^ 2 := by
          gcongr
          nlinarith [sq_nonneg (2 * Real.pi - 1)]
        _ = (2 * Real.pi * x) ^ 2 := by ring
    have hden : 1 + x ^ 2 ≤ 1 + (2 * Real.pi * x) ^ 2 := by linarith
    have hdenpos : 0 < 1 + x ^ 2 := by positivity
    have hinv : (1 + (2 * Real.pi * x) ^ 2)⁻¹ ≤ (1 + x ^ 2)⁻¹ :=
      by simpa only [one_div] using one_div_le_one_div_of_le hdenpos hden
    gcongr
end Auto
