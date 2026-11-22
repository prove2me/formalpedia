-- Prove2me | solution 1 for Auto.triangularHilbert_main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:03:58.325804+00:00
-- url     : https://prove2.me/submissions/1b82fb9d-d5de-4b57-b0cc-2154fab0fe4d

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangularHilbert_principal_value
public import Theorems.Thm_Auto_triangularBoundConstant_nonneg
public import Theorems.Thm_Auto_triangularHilbert_bound

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
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ, ∃ L : ℂ,
      Tendsto (fun ε : ℝ => ∫ xyz : (ℝ × ℝ) × ℝ,
        let ((x, y), z) := xyz
        if ε < |x + y + z| then
          F₀ (x, y) * F₁ (y, z) * F₂ (z, x) / ↑(x + y + z) else 0)
        (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      ‖L‖ ≤ C * (eLpNorm F₀ 3).toReal * (eLpNorm F₁ 3).toReal * (eLpNorm F₂ 3).toReal :=
  ⟨triangularBoundConstant, triangularBoundConstant_nonneg, fun F₀ F₁ F₂ =>
    ⟨triangularHilbert F₀ F₁ F₂, triangularHilbert_principal_value F₀ F₁ F₂,
      triangularHilbert_bound F₀ F₁ F₂⟩⟩
end Auto
