-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:35.332934+00:00
-- url     : https://prove2.me/submissions/2b67597f-b594-4197-8f04-48b1ba49d999

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_sumTriples
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples



set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N k : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace IsDecreasingOn
theorem _root_.solution (h : IsDecreasingOn N π) {r : ℝ} (hr : 0 ≤ r) :
    IsDecreasingOn N (r • π) := by
  obtain ⟨hπ₀, hπ, hπN⟩ := h
  exact ⟨fun k ↦ mul_nonneg hr (hπ₀ k), fun _ _ hab ↦ mul_le_mul_of_nonneg_left (hπ hab) hr,
    by simp [hπN]⟩
end IsDecreasingOn
end ArithmeticTriangleRemovalInVectorSpaces
