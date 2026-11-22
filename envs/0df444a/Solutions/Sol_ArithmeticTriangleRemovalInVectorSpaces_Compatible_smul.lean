-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.Compatible.smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:29.157802+00:00
-- url     : https://prove2.me/submissions/e0e3c5c1-3643-4785-86a3-e19d797e7c6f

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_marginal_smul

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {J J' : ℕ × ℕ × ℕ → ℝ} {g : ℕ × ℕ × ℕ → ℕ} {π₁ π₂ π₃ π₁' π₂' π₃' : ℕ → ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace Compatible
theorem _root_.solution (h : Compatible N π₁ π₂ π₃) {r : ℝ} (hr : 0 ≤ r) :
    Compatible N (r • π₁) (r • π₂) (r • π₃) := by
  obtain ⟨J, hJ, rfl, rfl, rfl⟩ := h
  exact ⟨r • J, fun x ↦ mul_nonneg hr (hJ x), marginal_smul r, marginal_smul r, marginal_smul r⟩
end Compatible
end ArithmeticTriangleRemovalInVectorSpaces
