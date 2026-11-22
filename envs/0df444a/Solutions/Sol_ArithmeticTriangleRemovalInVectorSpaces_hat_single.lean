-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.hat_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:25.373983+00:00
-- url     : https://prove2.me/submissions/7fbe1ff2-63a4-4a6d-b933-a51b52fe1403

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
theorem _root_.solution (hk : k ≤ N) : hat N (Pi.single k 1) = unif k := by
  ext j
  rw [hat, sum_eq_single_of_mem k (mem_range.2 (by grind)) fun b _ hb ↦ by simp [hb]]
  simp
end ArithmeticTriangleRemovalInVectorSpaces
