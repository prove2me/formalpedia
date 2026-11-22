-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.weight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:30.570153+00:00
-- url     : https://prove2.me/submissions/8edab287-2380-43f0-8238-34e872afa376

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N k : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace IsDecreasingOn
theorem _root_.solution (h : IsDecreasingOn N π) (k : ℕ) :
    0 ≤ (k + 1 : ℝ) * (π k - π (k + 1)) := by
  obtain ⟨-, hπ, -⟩ := h
  exact mul_nonneg (by positivity) (sub_nonneg.2 (hπ (Nat.le_succ k)))
end IsDecreasingOn
end ArithmeticTriangleRemovalInVectorSpaces
