-- Prove2me | solution 1 for Auto.fourierCoeffOne_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:51:48.419211+00:00
-- url     : https://prove2.me/submissions/a96f6556-3038-422c-92ef-45bcb1313ca2

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution (k n : ℤ) :
    fourierCoeffOne (fun x => Complex.exp (2 * π * Complex.I * k * x)) n =
      if n = k then 1 else 0 := by
  unfold fourierCoeffOne
  have he : ∀ t : ℝ, Complex.exp (2 * π * Complex.I * k * t) *
      Complex.exp (-(2 * π * Complex.I * n * t)) =
      Complex.exp ((2 * π * Complex.I * (k - n)) * t) := fun t => by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp_rw [he]
  split_ifs with h
  · subst h
    simp
  · have hkn : (k : ℂ) - n ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (Ne.symm h)
    rw [integral_exp_mul_complex (by simp [Real.pi_ne_zero, Complex.I_ne_zero, hkn])]
    have h1 : Complex.exp (2 * π * Complex.I * (k - n) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show 2 * π * Complex.I * ((k : ℂ) - n) * ((1 : ℝ) : ℂ) =
        ((k - n : ℤ) : ℂ) * (2 * π * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [h1]
    simp
end Auto
