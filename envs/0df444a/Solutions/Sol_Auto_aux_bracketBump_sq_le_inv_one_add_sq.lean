-- Prove2me | solution 1 for Auto.aux_bracketBump_sq_le_inv_one_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:05:31.930354+00:00
-- url     : https://prove2.me/submissions/833b4f2a-c26b-4440-a83d-0be4af1ca6e5

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

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    bracketBump x ^ 2 ≤ (1 + x ^ 2)⁻¹ := by
  rw [bracketBump]
  have hA : 0 < (1 + |x|) ^ 2 := sq_pos_of_pos (by positivity)
  have hB : 0 < 1 + x ^ 2 := by positivity
  have hrewrite : (1 + |x|)⁻¹ ^ 2 = ((1 + |x|) ^ 2)⁻¹ := by field_simp
  rw [hrewrite]
  apply (inv_le_inv₀ hA hB).2
  calc
    1 + x ^ 2 = 1 + |x| ^ 2 := by rw [sq_abs]
    _ ≤ (1 + |x|) ^ 2 := by nlinarith [abs_nonneg x]
end Auto
