-- Prove2me | solution 1 for Auto.auxiliaryFunctionB_properties
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:11:51.230982+00:00
-- url     : https://prove2.me/submissions/70611c38-4b25-4f10-975c-a9d275f12cfd

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
public import Theorems.Thm_Auto_aux_auxiliaryFunctionB_continuous
public import Theorems.Thm_Auto_aux_auxiliaryFunctionB_hasDerivAt_of_ne_zero
public import Theorems.Thm_Auto_aux_auxiliaryFunctionB_smoothOffZero
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_continuous
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_integrable
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_eLpNorm_one_le
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_hasDerivAt_of_ne_zero
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBSecondDerivative_measurable
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBSecondDerivative_integrable
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBSecondDerivative_eLpNorm_one_le
public import Theorems.Thm_Auto_aux_auxiliaryFunctionB_eLpNorm_one_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    Continuous auxiliaryFunctionB ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) auxiliaryFunctionB ({0}ᶜ : Set ℝ) ∧
      (∀ x : ℝ, x ≠ 0 →
        HasDerivAt auxiliaryFunctionB (auxiliaryFunctionBDerivative x) x) ∧
      Continuous auxiliaryFunctionBDerivative ∧
      Integrable auxiliaryFunctionBDerivative ∧
      (∀ x : ℝ, x ≠ 0 →
        HasDerivAt auxiliaryFunctionBDerivative (auxiliaryFunctionBSecondDerivative x) x) ∧
      Measurable auxiliaryFunctionBSecondDerivative ∧
      Integrable auxiliaryFunctionBSecondDerivative ∧
      eLpNorm auxiliaryFunctionB 1 volume ≤ ENNReal.ofReal 6 ∧
      eLpNorm auxiliaryFunctionBDerivative 1 volume ≤ ENNReal.ofReal 12 ∧
      eLpNorm auxiliaryFunctionBSecondDerivative 1 volume ≤ ENNReal.ofReal 56 := by
  exact ⟨aux_auxiliaryFunctionB_continuous, aux_auxiliaryFunctionB_smoothOffZero,
    fun x hx ↦ aux_auxiliaryFunctionB_hasDerivAt_of_ne_zero hx,
    aux_auxiliaryFunctionBDerivative_continuous, aux_auxiliaryFunctionBDerivative_integrable,
    fun x hx ↦ aux_auxiliaryFunctionBDerivative_hasDerivAt_of_ne_zero hx,
    aux_auxiliaryFunctionBSecondDerivative_measurable,
    aux_auxiliaryFunctionBSecondDerivative_integrable,
    aux_auxiliaryFunctionB_eLpNorm_one_le, aux_auxiliaryFunctionBDerivative_eLpNorm_one_le,
    aux_auxiliaryFunctionBSecondDerivative_eLpNorm_one_le⟩
end Auto
