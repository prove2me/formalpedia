-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBDerivative_continuousAt_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:57:41.081078+00:00
-- url     : https://prove2.me/submissions/0acf6d38-5bb5-4690-acd4-7e9a06ab8959

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
public import Theorems.Thm_Auto_aux_auxiliaryFunctionB_hasDerivAt_of_ne_zero
public import Theorems.Thm_Auto_aux_auxiliaryFunctionB_smoothOffZero

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt auxiliaryFunctionBDerivative x := by
  have hmem : x ∈ ({0}ᶜ : Set ℝ) := by simpa using hx
  have hopen : ({0}ᶜ : Set ℝ) ∈ 𝓝 x :=
    (isOpen_compl_singleton : IsOpen ({0}ᶜ : Set ℝ)).mem_nhds hmem
  have hBdiff : ContDiffAt ℝ (↑(⊤ : ℕ∞)) auxiliaryFunctionB x :=
    (aux_auxiliaryFunctionB_smoothOffZero x hmem).contDiffAt hopen
  have hderiv : ContinuousAt (deriv auxiliaryFunctionB) x :=
    (hBdiff.derivWithin (m := 0) (by simp)).continuousAt
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact (aux_auxiliaryFunctionB_hasDerivAt_of_ne_zero hy).deriv.symm
end Auto
