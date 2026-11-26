-- Prove2me | solution 1 for Auto.aux_sqrtOneMinusGaussian_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:42:44.313833+00:00
-- url     : https://prove2.me/submissions/c3b4b94d-219a-43a2-a883-91cee99e253b

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
public import Theorems.Thm_Auto_aux_one_sub_gaussian_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2) ≤
      sqrtOneMinusGaussian x := by
  let u : ℝ := Real.pi * x ^ 2
  have hu_nonneg : 0 ≤ u := by
    dsimp [u]
    positivity
  have hprod : (1 + u) * Real.exp (-u) ≤ 1 := by
    calc
      (1 + u) * Real.exp (-u) ≤ Real.exp u * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right
          (by simpa [add_comm] using Real.add_one_le_exp u) (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        norm_num
  have hu_exp : u * Real.exp (-u) ≤ 1 - Real.exp (-u) := by
    nlinarith
  have hrad : 0 ≤ 1 - gaussian x := aux_one_sub_gaussian_nonneg x
  have hleft_nonneg : 0 ≤
      Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2) := by
    positivity
  have hright_nonneg : 0 ≤ sqrtOneMinusGaussian x := Real.sqrt_nonneg _
  have hsqrtpi : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt (le_of_lt Real.pi_pos)
  have hhalf_sq : Real.exp (-(Real.pi / 2) * x ^ 2) ^ 2 =
      Real.exp (-(Real.pi * x ^ 2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq :
      (Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2)) ^ 2 ≤
        (sqrtOneMinusGaussian x) ^ 2 := by
    calc
      (Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2)) ^ 2 =
          u * Real.exp (-u) := by
        calc
          (Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2)) ^ 2 =
              (Real.sqrt Real.pi) ^ 2 * |x| ^ 2 *
                Real.exp (-(Real.pi / 2) * x ^ 2) ^ 2 := by ring
          _ = u * Real.exp (-u) := by
            rw [hsqrtpi, sq_abs, hhalf_sq]
      _ ≤ 1 - Real.exp (-u) := hu_exp
      _ = (sqrtOneMinusGaussian x) ^ 2 := by
        rw [sqrtOneMinusGaussian, Real.sq_sqrt hrad]
        simp [u, gaussian, Auto.gaussian]
  nlinarith
end Auto
