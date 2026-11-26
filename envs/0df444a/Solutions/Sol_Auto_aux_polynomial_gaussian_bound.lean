-- Prove2me | solution 1 for Auto.aux_polynomial_gaussian_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:56:20.394777+00:00
-- url     : https://prove2.me/submissions/729b8e37-6180-4fd0-afd7-dc7c9eecf98e

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
public import Theorems.Thm_Auto_aux_gaussian_superpolynomialDecay

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (p : Polynomial ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |x| ^ k * |p.eval x * gaussian x| ≤ C := by
  have hspd := aux_gaussian_superpolynomialDecay.polynomial_mul p
  have htendsto := hspd k
  have hcont : Continuous (fun x : ℝ => x ^ k * (p.eval x * gaussian x)) := by
    fun_prop [gaussian, Auto.gaussian]
  have hbounded := hcont.isBounded_range_iff_isBigO.mpr (htendsto.isBigO_one ℝ)
  rw [isBounded_iff_forall_norm_le] at hbounded
  simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hbounded
  obtain ⟨C, hC⟩ := hbounded
  refine ⟨C, ?_⟩
  intro x
  simpa [Real.norm_eq_abs, abs_mul, abs_pow] using hC x
end Auto
