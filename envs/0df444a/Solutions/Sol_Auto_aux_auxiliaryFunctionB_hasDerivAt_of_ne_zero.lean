-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionB_hasDerivAt_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:43:45.657066+00:00
-- url     : https://prove2.me/submissions/a31b3b67-f57c-46c7-9790-eee632f9755b

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
theorem _root_.solution {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt auxiliaryFunctionB (auxiliaryFunctionBDerivative x) x := by
  have hgauss_lt_one : gaussian x < 1 := by
    have hneg : -Real.pi * x ^ 2 < 0 := by
      nlinarith [Real.pi_pos, sq_pos_of_ne_zero hx]
    simpa [gaussian, Auto.gaussian] using (Real.exp_lt_exp.mpr hneg)
  have hrad_pos : 0 < 1 - gaussian x := sub_pos.mpr hgauss_lt_one
  have hrad_deriv : HasDerivAt (fun y : ℝ => 1 - gaussian y)
      (2 * Real.pi * x * gaussian x) x := by
    have hraw0 := (hasDerivAt_const x (1 : ℝ)).sub (aux_gaussian_hasDerivAt x)
    have hscalar : 0 - (-2 * Real.pi * x * gaussian x) =
        2 * Real.pi * x * gaussian x := by ring
    rw [← hscalar]
    exact hraw0.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp)
  have hsqrt : HasDerivAt sqrtOneMinusGaussian
      ((2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)) x := by
    unfold sqrtOneMinusGaussian
    exact hrad_deriv.sqrt (ne_of_gt hrad_pos)
  have hsqrtpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hlinear : HasDerivAt (fun y : ℝ => Real.sqrt Real.pi * y) (Real.sqrt Real.pi) x := by
    exact hasDerivAt_const_mul (x := x) (Real.sqrt Real.pi)
  have habs : HasDerivAt (fun y : ℝ => |Real.sqrt Real.pi * y|)
      ((SignType.sign (Real.sqrt Real.pi * x) : ℝ) * Real.sqrt Real.pi) x := by
    exact (hasDerivAt_abs (mul_ne_zero (ne_of_gt hsqrtpi) hx)).comp x hlinear
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-|Real.sqrt Real.pi * y|))
      (Real.exp (-|Real.sqrt Real.pi * x|) *
        (-((SignType.sign (Real.sqrt Real.pi * x) : ℝ) * Real.sqrt Real.pi))) x := by
    exact (Real.hasDerivAt_exp (-|Real.sqrt Real.pi * x|)).comp x habs.neg
  have hB := ((hasDerivAt_const x 1).sub hsqrt).sub hexp
  have hD : auxiliaryFunctionBDerivative x =
      0 - (2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x) -
        (Real.exp (-|Real.sqrt Real.pi * x|) *
          (-((SignType.sign (Real.sqrt Real.pi * x) : ℝ) * Real.sqrt Real.pi))) := by
    simp [auxiliaryFunctionBDerivative, hx]
    ring
  rw [hD]
  exact hB.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by simp [auxiliaryFunctionB])
end Auto
