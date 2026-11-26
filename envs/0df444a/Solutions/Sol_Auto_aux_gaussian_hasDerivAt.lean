-- Prove2me | solution 1 for Auto.aux_gaussian_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:37:18.118995+00:00
-- url     : https://prove2.me/submissions/1d8b1d29-7a4d-4248-a1f6-93bb009da89f

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
    HasDerivAt gaussian (-2 * Real.pi * x * gaussian x) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x)
  have hinner : HasDerivAt (fun y : ℝ => -Real.pi * y ^ 2) (-2 * Real.pi * x) x := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hpow.const_mul (-Real.pi)
  change HasDerivAt (fun y : ℝ => Real.exp (-Real.pi * y ^ 2))
    (-2 * Real.pi * x * Real.exp (-Real.pi * x ^ 2)) x
  convert (Real.hasDerivAt_exp (-Real.pi * x ^ 2)).comp x hinner using 1 <;> first | rfl | ring
end Auto
