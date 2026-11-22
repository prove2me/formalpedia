-- Prove2me | solution 1 for Auto.triangularHilbert_principal_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:49:47.534335+00:00
-- url     : https://prove2.me/submissions/bf39dbb1-3963-4bef-b971-89334c87308a

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangularTruncation_tendsto
public import Theorems.Thm_Auto_triangularHilbertTruncation_eq

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
theorem _root_.solution (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) :
    Tendsto (triangularHilbertTruncation F₀ F₁ F₂) (𝓝[>] (0 : ℝ)) (𝓝 (triangularHilbert F₀ F₁
      F₂)) := by
  exact ((triangularTruncation_tendsto F₀ (triangularPullback₁ F₁)
    (triangularPullback₂ F₂)).neg).congr (fun ε => (triangularHilbertTruncation_eq F₀ F₁ F₂ ε).symm)
end Auto
