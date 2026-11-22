-- Prove2me | solution 1 for Auto.tendsto_T_trunc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:54:24.677018+00:00
-- url     : https://prove2.me/submissions/cb729a67-da95-46fe-9191-8de52a8e3792

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangularHilbert_principal_value
public import Theorems.Thm_Auto_T_trunc_eq
public import Theorems.Thm_Auto_T_eq

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
    Tendsto (Triangular.T_trunc F₀ F₁ F₂) (𝓝[>] 0) (𝓝 (Triangular.T F₀ F₁ F₂)) := by
  rw [T_eq]
  exact (triangularHilbert_principal_value F₀ F₁ F₂).congr fun ε => (T_trunc_eq F₀ F₁ F₂ ε).symm
end Auto
