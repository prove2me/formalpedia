-- Prove2me | solution 1 for Auto.aux_one_sub_gaussian_div_sq_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:57:28.41889+00:00
-- url     : https://prove2.me/submissions/7e29607b-52db-4081-b67d-5ac0093805ce

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
public import Theorems.Thm_Auto_aux_one_sub_gaussian_hasDerivAt

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    Tendsto (fun x : ℝ => (1 - gaussian x) / x ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 Real.pi) := by
  refine HasDerivAt.lhopital_zero_nhdsNE
    (f := fun x : ℝ => 1 - gaussian x)
    (g := fun x : ℝ => x ^ 2)
    (f' := fun x : ℝ => 2 * Real.pi * x * gaussian x)
    (g' := fun x : ℝ => 2 * x) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall aux_one_sub_gaussian_hasDerivAt
  · exact Filter.Eventually.of_forall fun x => by
      have hraw0 := (hasDerivAt_id x).mul (hasDerivAt_id x)
      have hscalar : 1 * x + x * 1 = 2 * x := by ring
      have hraw : HasDerivAt (fun y : ℝ => y * y) (2 * x) x := by
        rw [← hscalar]
        exact hraw0.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun y => by simp)
      simpa only [pow_two] using hraw
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact mul_ne_zero (by norm_num) hx0
  · have hcont : Continuous (fun x : ℝ => (1 : ℝ) - gaussian x) :=
      continuous_const.sub gaussian_continuous
    have h := hcont.tendsto (0 : ℝ)
    simpa [gaussian, Auto.gaussian] using h.mono_left nhdsWithin_le_nhds
  · have hcont : Continuous (fun x : ℝ => x ^ 2) := continuous_id.pow 2
    have h := hcont.tendsto (0 : ℝ)
    simpa using h.mono_left nhdsWithin_le_nhds
  · have hcont : Continuous (fun x : ℝ => Real.pi * gaussian x) :=
      continuous_const.mul gaussian_continuous
    have h : Tendsto (fun x : ℝ => Real.pi * gaussian x)
        (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 Real.pi) := by
      have h' := hcont.tendsto (0 : ℝ)
      simpa [gaussian, Auto.gaussian] using h'.mono_left nhdsWithin_le_nhds
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    field_simp [hx0]
end Auto
