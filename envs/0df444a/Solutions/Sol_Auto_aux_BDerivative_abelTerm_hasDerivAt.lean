-- Prove2me | solution 1 for Auto.aux_BDerivative_abelTerm_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:12.990192+00:00
-- url     : https://prove2.me/submissions/95e69f7d-f1ae-48ba-890a-47ae180311da

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
theorem _root_.solution {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ =>
      Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * y) : ℝ) *
        Real.exp (-|Real.sqrt Real.pi * y|))
      (-Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)) x := by
  have hsqrtpi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsquare : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := by
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hscale : Real.sqrt Real.pi * x < 0 :=
      mul_neg_of_pos_of_neg hsqrtpi_pos hneg
    have hlin : HasDerivAt (fun y : ℝ => Real.sqrt Real.pi * y)
        (Real.sqrt Real.pi) x := hasDerivAt_const_mul (x := x) _
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (Real.sqrt Real.pi * y))
        (Real.exp (Real.sqrt Real.pi * x) * Real.sqrt Real.pi) x :=
      (Real.hasDerivAt_exp _).comp x hlin
    have hbase := hexp.const_mul (-Real.sqrt Real.pi)
    have hbase' : HasDerivAt (fun y : ℝ =>
        -Real.sqrt Real.pi * Real.exp (Real.sqrt Real.pi * y))
        (-Real.pi * Real.exp (Real.sqrt Real.pi * x)) x := by
      have hderiv :
          -Real.sqrt Real.pi * (Real.exp (Real.sqrt Real.pi * x) * Real.sqrt Real.pi) =
            -Real.pi * Real.exp (Real.sqrt Real.pi * x) := by
        calc
          -Real.sqrt Real.pi * (Real.exp (Real.sqrt Real.pi * x) * Real.sqrt Real.pi) =
              -(Real.sqrt Real.pi * Real.sqrt Real.pi) *
                Real.exp (Real.sqrt Real.pi * x) := by ring
          _ = -Real.pi * Real.exp (Real.sqrt Real.pi * x) := by rw [hsquare]
      simpa only [neg_mul, hderiv] using hbase
    have hIio : Set.Iio (0 : ℝ) ∈ 𝓝 x := isOpen_Iio.mem_nhds hneg
    have heq : (fun y : ℝ =>
        Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * y) : ℝ) *
          Real.exp (-|Real.sqrt Real.pi * y|)) =ᶠ[𝓝 x]
        (fun y : ℝ => -Real.sqrt Real.pi * Real.exp (Real.sqrt Real.pi * y)) := by
      filter_upwards [hIio] with y hy
      have hy_scale : Real.sqrt Real.pi * y < 0 :=
        mul_neg_of_pos_of_neg hsqrtpi_pos hy
      have hsign : (SignType.sign (Real.sqrt Real.pi * y) : ℝ) = -1 := by
        simpa using congrArg (fun s : SignType => (s : ℝ)) (sign_neg hy_scale)
      rw [hsign, abs_of_neg hy_scale]
      ring_nf
    simpa [abs_of_neg hscale] using hbase'.congr_of_eventuallyEq heq
  · have hscale : 0 < Real.sqrt Real.pi * x := mul_pos hsqrtpi_pos hpos
    have hlin : HasDerivAt (fun y : ℝ => -Real.sqrt Real.pi * y)
        (-Real.sqrt Real.pi) x := hasDerivAt_const_mul (x := x) _
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-Real.sqrt Real.pi * y))
        (Real.exp (-Real.sqrt Real.pi * x) * (-Real.sqrt Real.pi)) x :=
      (Real.hasDerivAt_exp _).comp x hlin
    have hbase := hexp.const_mul (Real.sqrt Real.pi)
    have hbase' : HasDerivAt (fun y : ℝ =>
        Real.sqrt Real.pi * Real.exp (-Real.sqrt Real.pi * y))
        (-Real.pi * Real.exp (-Real.sqrt Real.pi * x)) x := by
      have hderiv :
          Real.sqrt Real.pi *
              (Real.exp (-Real.sqrt Real.pi * x) * (-Real.sqrt Real.pi)) =
            -Real.pi * Real.exp (-Real.sqrt Real.pi * x) := by
        calc
          Real.sqrt Real.pi *
              (Real.exp (-Real.sqrt Real.pi * x) * (-Real.sqrt Real.pi)) =
              -(Real.sqrt Real.pi * Real.sqrt Real.pi) *
                Real.exp (-Real.sqrt Real.pi * x) := by ring
          _ = -Real.pi * Real.exp (-Real.sqrt Real.pi * x) := by rw [hsquare]
      simpa only [hderiv] using hbase
    have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 x := isOpen_Ioi.mem_nhds hpos
    have heq : (fun y : ℝ =>
        Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * y) : ℝ) *
          Real.exp (-|Real.sqrt Real.pi * y|)) =ᶠ[𝓝 x]
        (fun y : ℝ => Real.sqrt Real.pi * Real.exp (-Real.sqrt Real.pi * y)) := by
      filter_upwards [hIoi] with y hy
      have hy_scale : 0 < Real.sqrt Real.pi * y := mul_pos hsqrtpi_pos hy
      have hsign : (SignType.sign (Real.sqrt Real.pi * y) : ℝ) = 1 := by
        simpa using congrArg (fun s : SignType => (s : ℝ)) (sign_pos hy_scale)
      rw [hsign, abs_of_pos hy_scale, mul_one]
      ring_nf
    simpa [abs_of_pos hscale, neg_mul] using hbase'.congr_of_eventuallyEq heq
end Auto
