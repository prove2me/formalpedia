-- Prove2me | solution 1 for Auto.integrable_carlesonForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:49:21.792173+00:00
-- url     : https://prove2.me/submissions/8c373778-ce0c-433a-bf72-d0dd112a005e

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carlesonWeight_nonneg
public import Theorems.Thm_Auto_measurable_carlesonWeight
public import Theorems.Thm_Auto_integrable_carlesonWeight
public import Theorems.Thm_Auto_abs_sin_mul_div_le
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution {a ν : ℝ → ℝ} {g : ℝ → ℂ} {B : ℝ}
    (ha : Measurable a) (hν : Measurable ν) (hg : Measurable g) (hgB : ∀ x, ‖g x‖ ≤ B)
    (hi : Integrable fun x => a x ^ 2 * |ν x|) :
    Integrable fun p : ℝ × ℝ => (a p.1 : ℂ) ^ 2 * g (p.1 - p.2) *
      ((carlesonWeight p.2 * Real.sin (ν p.1 * p.2) / p.2 : ℝ) : ℂ) := by
  have hw := measurable_carlesonWeight
  refine ((hi.mul_prod integrable_carlesonWeight).const_mul B).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun p => ?_)
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_div_assoc, abs_mul, abs_of_nonneg (carlesonWeight_nonneg _)]
  have h₁ := abs_sin_mul_div_le (ν p.1) p.2
  have h₂ := hgB (p.1 - p.2)
  have h₃ := carlesonWeight_nonneg p.2
  calc |a p.1| ^ 2 * ‖g (p.1 - p.2)‖ * (carlesonWeight p.2 * |Real.sin (ν p.1 * p.2) / p.2|)
      ≤ |a p.1| ^ 2 * B * (carlesonWeight p.2 * |ν p.1|) := by
        have : 0 ≤ B := (norm_nonneg _).trans h₂
        gcongr
    _ = B * (a p.1 ^ 2 * |ν p.1| * carlesonWeight p.2) := by rw [sq_abs]; ring
end Auto
