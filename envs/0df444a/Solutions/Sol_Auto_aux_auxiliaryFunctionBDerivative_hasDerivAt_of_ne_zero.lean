-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBDerivative_hasDerivAt_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:03:12.937558+00:00
-- url     : https://prove2.me/submissions/56135bc0-6076-4b23-a69b-428733d67372

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
public import Theorems.Thm_Auto_aux_BDerivative_gaussianTerm_hasDerivAt
public import Theorems.Thm_Auto_aux_BDerivative_abelTerm_hasDerivAt

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt auxiliaryFunctionBDerivative (auxiliaryFunctionBSecondDerivative x) x := by
  have hq := aux_BDerivative_gaussianTerm_hasDerivAt hx
  have ha := aux_BDerivative_abelTerm_hasDerivAt hx
  have hsum := hq.add ha
  have heq : auxiliaryFunctionBDerivative =ᶠ[𝓝 x]
      (fun y : ℝ =>
        (-2 * Real.pi * y * gaussian y) / (2 * sqrtOneMinusGaussian y) +
          Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * y) : ℝ) *
            Real.exp (-|Real.sqrt Real.pi * y|)) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [auxiliaryFunctionBDerivative, hy]
  have hsum' := hsum.congr_of_eventuallyEq heq
  have hcoef :
      (((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)) +
        (-Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)) =
      ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3) -
        Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
    ring
  rw [hcoef] at hsum'
  have hsecond : auxiliaryFunctionBSecondDerivative x =
      ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3) -
        Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
    simp [auxiliaryFunctionBSecondDerivative, hx]
  rw [hsecond]
  exact hsum'
end Auto
