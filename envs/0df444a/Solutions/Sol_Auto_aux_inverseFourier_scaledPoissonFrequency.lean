-- Prove2me | solution 1 for Auto.aux_inverseFourier_scaledPoissonFrequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:35.765231+00:00
-- url     : https://prove2.me/submissions/a2096d83-fb86-4585-88ef-2d5abe472a91

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
public import Theorems.Thm_Auto_aux_inverseFourier_poissonFrequency
public import Theorems.Thm_Auto_aux_inverseFourier_comp_mul_pos

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => (aux_scaledPoissonFrequency ξ : ℂ)) x =
      (aux_scaledPoissonKernel x : ℂ) := by
  change FourierTransformInv.fourierInv
    (fun ξ : ℝ => (aux_poissonFrequency (Real.sqrt Real.pi * ξ) : ℂ)) x = _
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [aux_inverseFourier_comp_mul_pos (fun ξ : ℝ => (aux_poissonFrequency ξ : ℂ))
    (Real.sqrt Real.pi) x hsqrt]
  rw [aux_inverseFourier_poissonFrequency]
  simp [aux_scaledPoissonKernel]
end Auto
