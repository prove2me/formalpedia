-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:50.80748+00:00
-- url     : https://prove2.me/submissions/c35666bc-44a0-45fc-8b89-5489a2bf7c0e

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
theorem _root_.solution (h : IsDecreasingOn N π) {k : ℕ} (hk : N < k) : π k = 0 := by
  obtain ⟨hπ₀, hπ, hπN⟩ := h
  exact le_antisymm (hπN ▸ hπ hk) (hπ₀ k)
end IsDecreasingOn
end ArithmeticTriangleRemovalInVectorSpaces
