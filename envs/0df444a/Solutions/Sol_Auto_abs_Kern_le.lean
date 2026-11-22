-- Prove2me | solution 1 for Auto.abs_Kern_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:43:04.014014+00:00
-- url     : https://prove2.me/submissions/8284a365-f591-4ed2-b6ca-3ea0043a9d29

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_Kern_eq
public import Theorems.Thm_Auto_abs_kernIntegrand_le

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution (m : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, ∀ t, |Kern m a b t| ≤ C := by
  obtain ⟨C, hC, h⟩ := abs_kernIntegrand_le m
  refine ⟨C / (a * √a) * (b - a), fun t => ?_⟩
  rw [Kern_eq]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun s => kernIntegrand m s t) (C := C / (a * √a)) ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at this
    exact this
  intro s hs
  rw [Set.uIoc_of_le hab] at hs
  have hs0 : 0 < s := ha.trans hs.1
  rw [Real.norm_eq_abs]
  refine (h s hs0 t).trans ?_
  have : a * √a ≤ s * √s := mul_le_mul hs.1.le (Real.sqrt_le_sqrt hs.1.le) (Real.sqrt_nonneg _)
    hs0.le
  exact div_le_div_of_nonneg_left hC (by positivity) this
end Auto
