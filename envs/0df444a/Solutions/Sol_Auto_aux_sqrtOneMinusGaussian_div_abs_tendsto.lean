-- Prove2me | solution 1 for Auto.aux_sqrtOneMinusGaussian_div_abs_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:54.816889+00:00
-- url     : https://prove2.me/submissions/32ccc82f-fd6b-471d-a135-de6871880ec6

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
public import Theorems.Thm_Auto_aux_one_sub_gaussian_nonneg
public import Theorems.Thm_Auto_aux_one_sub_gaussian_div_sq_tendsto

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    Tendsto (fun x : ℝ => sqrtOneMinusGaussian x / |x|)
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 (Real.sqrt Real.pi)) := by
  refine aux_one_sub_gaussian_div_sq_tendsto.sqrt.congr' ?_
  exact Filter.Eventually.of_forall fun x => by
    change Real.sqrt ((1 - gaussian x) / x ^ 2) =
      sqrtOneMinusGaussian x / |x|
    unfold sqrtOneMinusGaussian
    rw [Real.sqrt_div (aux_one_sub_gaussian_nonneg x), Real.sqrt_sq_eq_abs]
end Auto
