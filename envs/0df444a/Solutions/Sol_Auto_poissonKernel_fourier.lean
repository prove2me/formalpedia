-- Prove2me | solution 1 for Auto.poissonKernel_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:53.685604+00:00
-- url     : https://prove2.me/submissions/791718e5-3aab-4622-b4a6-fbd23b771268

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
public import Theorems.Thm_Auto_aux_poissonKernel_integrable
public import Theorems.Thm_Auto_aux_poissonFrequency_continuous
public import Theorems.Thm_Auto_aux_poissonFrequency_integrable
public import Theorems.Thm_Auto_aux_inverseFourier_poissonFrequency

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    FourierTransform.fourier (fun x : ℝ => (poissonKernel x : ℂ)) =
      fun ξ : ℝ => (aux_poissonFrequency ξ : ℂ) := by
  let q : ℝ → ℂ := fun ξ => (aux_poissonFrequency ξ : ℂ)
  have hq_continuous : Continuous q :=
    Complex.continuous_ofReal.comp aux_poissonFrequency_continuous
  have hq_integrable : Integrable q := by
    change Integrable (fun ξ : ℝ => (aux_poissonFrequency ξ : ℂ))
    exact aux_poissonFrequency_integrable.ofReal
  have hinv : FourierTransformInv.fourierInv q =
      fun x : ℝ => (poissonKernel x : ℂ) := by
    funext x
    simpa [q] using aux_inverseFourier_poissonFrequency x
  have hq_neg : (fun x : ℝ => q (-x)) = q := by
    funext x
    simp [q, aux_poissonFrequency]
  have hinv_eq_fourier : FourierTransformInv.fourierInv q =
      FourierTransform.fourier q := by
    calc
      FourierTransformInv.fourierInv q =
          FourierTransform.fourier (fun x : ℝ => q (-x)) :=
        Real.fourierInv_eq_fourier_comp_neg q
      _ = FourierTransform.fourier q := by rw [hq_neg]
  have hqFourierIntegrable : Integrable (FourierTransform.fourier q) := by
    rw [← hinv_eq_fourier, hinv]
    exact aux_poissonKernel_integrable.ofReal
  rw [← hinv]
  exact hq_continuous.fourier_fourierInv_eq hq_integrable hqFourierIntegrable
end Auto
