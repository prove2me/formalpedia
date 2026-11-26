-- Prove2me | solution 1 for Auto.aux_gaussian_deriv_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:00:56.380016+00:00
-- url     : https://prove2.me/submissions/a6fd964c-462f-4b18-9fe9-9dfd8e2a3b63

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
public import Theorems.Thm_Auto_aux_gaussian_hasDerivAt

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    HasDerivAt (fun y : ℝ => -2 * Real.pi * y * gaussian y)
      ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) x := by
  have h := ((hasDerivAt_id x).mul (aux_gaussian_hasDerivAt x)).const_mul
    (-2 * Real.pi)
  have hfun : (fun y : ℝ => -2 * Real.pi * y * gaussian y) =ᶠ[𝓝 x]
      (fun y : ℝ => -2 * Real.pi * ((id : ℝ → ℝ) * gaussian) y) := by
    filter_upwards [] with y
    simp only [Pi.mul_apply, id_eq]
    ring
  have h' := h.congr_of_eventuallyEq hfun
  have hcoef : -2 * Real.pi *
      (1 * gaussian x + id x * (-2 * Real.pi * x * gaussian x)) =
      (4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x := by
    simp only [id_eq, one_mul]
    ring
  rw [hcoef] at h'
  exact h'
end Auto
