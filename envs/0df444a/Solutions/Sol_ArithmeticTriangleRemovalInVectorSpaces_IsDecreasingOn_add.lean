-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:20.078859+00:00
-- url     : https://prove2.me/submissions/8901b83f-48ac-4fe9-a9e5-5f46345e557a

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_Compatible_add
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
theorem _root_.solution (h : IsDecreasingOn N π) (h' : IsDecreasingOn N π') :
    IsDecreasingOn N (π + π') := by
  obtain ⟨hπ₀, hπ, hπN⟩ := h
  obtain ⟨hπ₀', hπ', hπN'⟩ := h'
  exact ⟨fun k ↦ add_nonneg (hπ₀ k) (hπ₀' k), hπ.add hπ', by simp [hπN, hπN']⟩
end IsDecreasingOn
end ArithmeticTriangleRemovalInVectorSpaces
