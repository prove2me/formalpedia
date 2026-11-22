-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.weight_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:31.255635+00:00
-- url     : https://prove2.me/submissions/a5a27045-a071-46a0-ab0a-93ccbe956934

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_eq_zero_of_lt


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N k : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace IsDecreasingOn
theorem _root_.solution (h : IsDecreasingOn N π) {k : ℕ} (hk : N < k) :
    (k + 1 : ℝ) * (π k - π (k + 1)) = 0 := by
  rw [h.eq_zero_of_lt hk, h.eq_zero_of_lt (by grind), sub_zero, mul_zero]
end IsDecreasingOn
end ArithmeticTriangleRemovalInVectorSpaces
