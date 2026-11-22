-- Prove2me | solution 1 for Auto.triangular_truncation_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:58:52.142531+00:00
-- url     : https://prove2.me/submissions/c8446fb3-c845-4d78-b7d6-a03d0639856a

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangular_product_integrable

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
theorem _root_.solution (H F G : SchwartzMap (ℝ × ℝ) ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => if ε < |q.2| then H q.1 * triangularShiftProduct F G q.1
      q.2 / (q.2 : ℂ) else 0) := by
  have hi := (triangular_product_integrable H F G).mul_bdd (c := ε⁻¹)
    (g := fun q : (ℝ × ℝ) × ℝ => if ε < |q.2| then (q.2 : ℂ)⁻¹ else 0)
    (by
      apply Measurable.aestronglyMeasurable
      exact Measurable.ite (measurableSet_lt measurable_const measurable_snd.abs)
        (by fun_prop) measurable_const) (by
      filter_upwards [] with q
      split_ifs with h
      · simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs]
        exact inv_anti₀ hε h.le
      · simp; positivity)
  simpa only [mul_ite, mul_zero, div_eq_mul_inv] using hi
end Auto
