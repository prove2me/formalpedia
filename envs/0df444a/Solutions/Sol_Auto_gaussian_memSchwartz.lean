-- Prove2me | solution 1 for Auto.gaussian_memSchwartz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:09:12.718428+00:00
-- url     : https://prove2.me/submissions/2a3d82bb-a26e-4432-898e-1326205ca719

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
public import Theorems.Thm_Auto_aux_gaussian_contDiff
public import Theorems.Thm_Auto_aux_gaussian_iteratedDeriv_polynomial
public import Theorems.Thm_Auto_aux_polynomial_gaussian_bound

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    ∃ G : SchwartzMap ℝ ℝ, ∀ x : ℝ, G x = gaussian x := by
  let G : SchwartzMap ℝ ℝ := {
    toFun := gaussian
    smooth' := aux_gaussian_contDiff
    decay' := by
      intro k n
      obtain ⟨p, hp⟩ := aux_gaussian_iteratedDeriv_polynomial n
      obtain ⟨C, hC⟩ := aux_polynomial_gaussian_bound p k
      refine ⟨C, ?_⟩
      intro x
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      simp only [Real.norm_eq_abs]
      rw [hp x]
      exact hC x
    }
  exact ⟨G, fun x => rfl⟩
end Auto
