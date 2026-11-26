-- Prove2me | solution 1 for Auto.aux_one_sub_gaussian_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:47:38.882776+00:00
-- url     : https://prove2.me/submissions/88f540da-22f6-4919-abc6-d392a4ccd34f

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
    HasDerivAt (fun y : ℝ => 1 - gaussian y)
      (2 * Real.pi * x * gaussian x) x := by
  have hraw0 := (hasDerivAt_const x (1 : ℝ)).sub (aux_gaussian_hasDerivAt x)
  have hscalar : 0 - (-2 * Real.pi * x * gaussian x) =
      2 * Real.pi * x * gaussian x := by ring
  rw [← hscalar]
  exact hraw0.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by simp)
end Auto
