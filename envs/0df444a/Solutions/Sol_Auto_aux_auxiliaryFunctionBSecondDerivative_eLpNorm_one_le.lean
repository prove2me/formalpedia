-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBSecondDerivative_eLpNorm_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:04:02.240474+00:00
-- url     : https://prove2.me/submissions/6afb61e9-4d16-41dd-b427-4b5d8d193f36

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
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBSecondDerivative_norm_le_sharp
public import Theorems.Thm_Auto_aux_BSecondSharpMajorant_integrable
public import Theorems.Thm_Auto_aux_BSecondSharpMajorant_integral_le_fiftySix
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBSecondDerivative_integrable

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    eLpNorm auxiliaryFunctionBSecondDerivative 1 volume ≤ ENNReal.ofReal 56 := by
  have hnorm_bound : (∫ x : ℝ, ‖auxiliaryFunctionBSecondDerivative x‖) ≤ 56 := by
    calc
      (∫ x : ℝ, ‖auxiliaryFunctionBSecondDerivative x‖) ≤
          ∫ x : ℝ,
            26 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
                (fun _ : ℝ => (1 : ℝ)) x +
              2 * Real.pi * gaussian x + 12 * Real.pi ^ 2 * x ^ 2 * gaussian x +
                Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
        apply integral_mono aux_auxiliaryFunctionBSecondDerivative_integrable.norm
          aux_BSecondSharpMajorant_integrable
        intro x
        exact aux_auxiliaryFunctionBSecondDerivative_norm_le_sharp x
      _ ≤ 56 := aux_BSecondSharpMajorant_integral_le_fiftySix
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm aux_auxiliaryFunctionBSecondDerivative_integrable]
  exact ENNReal.ofReal_le_ofReal hnorm_bound
end Auto
