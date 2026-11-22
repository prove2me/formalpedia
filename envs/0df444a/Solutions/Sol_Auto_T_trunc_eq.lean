-- Prove2me | solution 1 for Auto.T_trunc_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:58:23.513522+00:00
-- url     : https://prove2.me/submissions/90461251-e6bc-46f9-8a57-c20942bd6472

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply

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
theorem _root_.solution (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) (ε : ℝ) :
    Triangular.T_trunc F₀ F₁ F₂ ε = triangularHilbertTruncation F₀ F₁ F₂ ε := by
  change ∫ q in {q : (ℝ × ℝ) × ℝ | ε < |q.1.1 + q.1.2 + q.2|},
    F₀ q.1 * F₁ (q.1.2, q.2) * F₂ (q.2, q.1.1) / ((q.1.1 + q.1.2 + q.2 : ℝ) : ℂ) = _
  rw [← integral_indicator (measurableSet_lt measurable_const (by fun_prop))]
  unfold triangularHilbertTruncation
  congr 1
end Auto
