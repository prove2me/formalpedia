-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBDerivative_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:51.526383+00:00
-- url     : https://prove2.me/submissions/aec9b313-ae31-436e-8b22-8274c7d62753

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
public import Theorems.Thm_Auto_aux_exp_neg_abs_sqrt_pi_le_poissonFrequency
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_gaussianTerm_bound

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    ‖auxiliaryFunctionBDerivative x‖ ≤
      Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.sqrt Real.pi * aux_poissonFrequency x := by
  rw [Real.norm_eq_abs]
  by_cases hx : x = 0
  · subst x
    simp [auxiliaryFunctionBDerivative, aux_poissonFrequency]
  · rw [auxiliaryFunctionBDerivative, if_neg hx]
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · have hscale : Real.sqrt Real.pi * x < 0 :=
        mul_neg_of_pos_of_neg (Real.sqrt_pos.2 Real.pi_pos) hneg
      have habel :
          |Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
              Real.exp (-|Real.sqrt Real.pi * x|)| =
            Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
        rw [sign_neg hscale]
        simp [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.exp_pos _).le]
      calc
        |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x) +
            Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
              Real.exp (-|Real.sqrt Real.pi * x|)| ≤
            |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)| +
              |Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
                Real.exp (-|Real.sqrt Real.pi * x|)| := abs_add_le _ _
        _ = |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)| +
              Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by rw [habel]
        _ ≤ Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) +
              Real.sqrt Real.pi * aux_poissonFrequency x := by
          have hgaussian := aux_auxiliaryFunctionBDerivative_gaussianTerm_bound hx
          have hpoisson : Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) ≤
              Real.sqrt Real.pi * aux_poissonFrequency x :=
            mul_le_mul_of_nonneg_left (aux_exp_neg_abs_sqrt_pi_le_poissonFrequency x)
              (Real.sqrt_nonneg _)
          exact add_le_add hgaussian hpoisson
    · have hscale : 0 < Real.sqrt Real.pi * x :=
        mul_pos (Real.sqrt_pos.2 Real.pi_pos) hpos
      have habel :
          |Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
              Real.exp (-|Real.sqrt Real.pi * x|)| =
            Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
        have hsign :
            (SignType.sign (Real.sqrt Real.pi * x) : ℝ) = 1 := by
          simpa using congrArg (fun s : SignType => (s : ℝ)) (sign_pos hscale)
        have hnonneg : 0 ≤
            Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
        calc
          |Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
              Real.exp (-|Real.sqrt Real.pi * x|)| =
              |Real.sqrt Real.pi * 1 * Real.exp (-|Real.sqrt Real.pi * x|)| := by rw [hsign]
          _ = Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
            rw [mul_one, abs_of_nonneg hnonneg]
      calc
        |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x) +
            Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
              Real.exp (-|Real.sqrt Real.pi * x|)| ≤
            |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)| +
              |Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
                Real.exp (-|Real.sqrt Real.pi * x|)| := abs_add_le _ _
        _ = |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)| +
              Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by rw [habel]
        _ ≤ Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) +
              Real.sqrt Real.pi * aux_poissonFrequency x := by
          have hgaussian := aux_auxiliaryFunctionBDerivative_gaussianTerm_bound hx
          have hpoisson : Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) ≤
              Real.sqrt Real.pi * aux_poissonFrequency x :=
            mul_le_mul_of_nonneg_left (aux_exp_neg_abs_sqrt_pi_le_poissonFrequency x)
              (Real.sqrt_nonneg _)
          exact add_le_add hgaussian hpoisson
end Auto
