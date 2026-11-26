-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBTrueSecondDerivative_continuousAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:16.670622+00:00
-- url     : https://prove2.me/submissions/ee65c683-b7fa-4390-bc38-efd28dd5b119

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
public import Theorems.Thm_Auto_aux_BSecondGaussianPart_abs_le_near_zero

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    ContinuousAt (fun x : ℝ =>
      if x = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative x) 0 := by
  unfold ContinuousAt
  simp only [if_pos]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hmajor : Tendsto (fun x : ℝ =>
      144 * |x| + Real.pi * |1 - Real.exp (-|Real.sqrt Real.pi * x|)|) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun x : ℝ =>
        144 * |x| + Real.pi * |1 - Real.exp (-|Real.sqrt Real.pi * x|)|) := by
      fun_prop
    have hcontAt : ContinuousAt (fun x : ℝ =>
        144 * |x| + Real.pi * |1 - Real.exp (-|Real.sqrt Real.pi * x|)|) 0 :=
      hcont.continuousAt
    simpa [ContinuousAt] using hcontAt
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hmajor
  filter_upwards [show Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ 𝓝 0 by
    exact isOpen_Ioo.mem_nhds ⟨by norm_num, by norm_num⟩] with x hx
  have hxabs : |x| ≤ 1 / 2 := by
    rw [abs_le]
    exact ⟨hx.1.le, hx.2.le⟩
  by_cases hx0 : x = 0
  · subst x
    simp
  · have hgaussian := aux_BSecondGaussianPart_abs_le_near_zero hx0 hxabs
    rw [Real.norm_eq_abs]
    simp only [if_neg hx0]
    have hrewrite :
        auxiliaryFunctionBSecondDerivative x - -Real.pi =
          (((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
              (2 * sqrtOneMinusGaussian x) +
            (-2 * Real.pi * x * gaussian x) ^ 2 /
              (4 * sqrtOneMinusGaussian x ^ 3)) +
            Real.pi * (1 - Real.exp (-|Real.sqrt Real.pi * x|)) := by
      simp [auxiliaryFunctionBSecondDerivative, hx0]
      ring
    rw [hrewrite]
    calc
      |(((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
              (2 * sqrtOneMinusGaussian x) +
            (-2 * Real.pi * x * gaussian x) ^ 2 /
              (4 * sqrtOneMinusGaussian x ^ 3)) +
            Real.pi * (1 - Real.exp (-|Real.sqrt Real.pi * x|))| ≤
          |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
              (2 * sqrtOneMinusGaussian x) +
            (-2 * Real.pi * x * gaussian x) ^ 2 /
              (4 * sqrtOneMinusGaussian x ^ 3)| +
            |Real.pi * (1 - Real.exp (-|Real.sqrt Real.pi * x|))| := abs_add_le _ _
      _ = |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
              (2 * sqrtOneMinusGaussian x) +
            (-2 * Real.pi * x * gaussian x) ^ 2 /
              (4 * sqrtOneMinusGaussian x ^ 3)| +
            Real.pi * |1 - Real.exp (-|Real.sqrt Real.pi * x|)| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
      _ ≤ 144 * |x| + Real.pi * |1 - Real.exp (-|Real.sqrt Real.pi * x|)| :=
        add_le_add hgaussian le_rfl
end Auto
