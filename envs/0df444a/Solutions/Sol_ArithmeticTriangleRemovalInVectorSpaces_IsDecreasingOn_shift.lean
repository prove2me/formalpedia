-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:14.644807+00:00
-- url     : https://prove2.me/submissions/63dce0b1-8d85-45a2-82d3-f0159d4c2c97

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace IsDecreasingOn
theorem _root_.solution (h : IsDecreasingOn (N + 1) π) :
    IsDecreasingOn N fun k ↦ π (k + 1) := by
  obtain ⟨hπ₀, hπ, hπN⟩ := h
  exact ⟨fun k ↦ hπ₀ _, fun _ _ hab ↦ hπ (by grind), hπN⟩
end IsDecreasingOn
end ArithmeticTriangleRemovalInVectorSpaces
