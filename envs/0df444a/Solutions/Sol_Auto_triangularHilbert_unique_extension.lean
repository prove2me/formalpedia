-- Prove2me | solution 1 for Auto.triangularHilbert_unique_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:03:58.826138+00:00
-- url     : https://prove2.me/submissions/f5bd8b5b-dc12-4ee9-a96b-df88e7b75ece

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangularBoundConstant_nonneg
public import Theorems.Thm_Auto_triangularHilbert_bound
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
public import Theorems.Thm_Auto_triangular_trilinear_dense_extension
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
theorem _root_.solution :
    ∃ T : TriangularL3 →L[ℂ] TriangularL3 →L[ℂ] TriangularL3 →L[ℂ] ℂ,
      (∀ F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ,
        T (F₀.toLp 3) (F₁.toLp 3) (F₂.toLp 3) = triangularHilbert F₀ F₁ F₂) ∧
      (∀ f₀ f₁ f₂, ‖T f₀ f₁ f₂‖ ≤ triangularBoundConstant * ‖f₀‖ * ‖f₁‖ * ‖f₂‖) ∧
      ∀ S : TriangularL3 →L[ℂ] TriangularL3 →L[ℂ] TriangularL3 →L[ℂ] ℂ,
        (∀ F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ,
          S (F₀.toLp 3) (F₁.toLp 3) (F₂.toLp 3) = triangularHilbert F₀ F₁ F₂) → S = T := by
  let e := (SchwartzMap.toLpCLM ℂ ℂ (3 : ℝ≥0∞) (volume : Measure (ℝ × ℝ))).toLinearMap
  have hd : DenseRange e := SchwartzMap.denseRange_toLpCLM (F := ℂ) (by norm_num)
  apply triangular_trilinear_dense_extension e hd triangularHilbertLinear
    triangularBoundConstant_nonneg
  intro F₀ F₁ F₂
  simpa only [triangularHilbertLinear_apply, e, ContinuousLinearMap.coe_coe,
    SchwartzMap.toLpCLM_apply, SchwartzMap.toLp, Lp.norm_toLp] using
    triangularHilbert_bound F₀ F₁ F₂
end Auto
