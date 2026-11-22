-- Prove2me | solution 1 for Auto.exp_sub_exp_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:01:18.213999+00:00
-- url     : https://prove2.me/submissions/745f6c54-7567-4751-ab92-df28239da34d

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution (θ : ℝ) :
    Complex.exp (θ * Complex.I) - Complex.exp ((-θ : ℝ) * Complex.I) =
      2 * Complex.I * (Real.sin θ : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg,
    Complex.sin_neg, Complex.ofReal_sin]
  ring
end Auto
