-- Prove2me | solution 1 for Auto.triangular_ht_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:03:57.884337+00:00
-- url     : https://prove2.me/submissions/40a3d427-2285-4b8e-a3a2-0fce3cf59627

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangularBoundConstant_nonneg
public import Theorems.Thm_Auto_triangularHilbert_bound
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
theorem _root_.solution :
    ∃ C : ℝ, ∀ F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ,
      ‖Triangular.T F₀ F₁ F₂‖ₑ ≤
        ENNReal.ofReal C * eLpNorm F₀ 3 * eLpNorm F₁ 3 * eLpNorm F₂ 3 := by
  refine ⟨triangularBoundConstant, fun F₀ F₁ F₂ => ?_⟩
  have h := triangularHilbert_bound F₀ F₁ F₂
  rw [T_eq, ← ofReal_norm, ← ENNReal.ofReal_toReal ((F₀.memLp 3 volume).eLpNorm_ne_top),
    ← ENNReal.ofReal_toReal ((F₁.memLp 3 volume).eLpNorm_ne_top),
    ← ENNReal.ofReal_toReal ((F₂.memLp 3 volume).eLpNorm_ne_top),
    ← ENNReal.ofReal_mul triangularBoundConstant_nonneg,
    ← ENNReal.ofReal_mul (by have := triangularBoundConstant_nonneg; positivity),
    ← ENNReal.ofReal_mul (by have := triangularBoundConstant_nonneg; positivity)]
  exact ENNReal.ofReal_le_ofReal h
end Auto
