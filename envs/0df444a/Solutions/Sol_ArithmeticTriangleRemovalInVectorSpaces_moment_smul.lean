-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.moment_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:09.517837+00:00
-- url     : https://prove2.me/submissions/548c70f5-d090-4a8c-bd58-005bea2b848d

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_sumTriples
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples



set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution (r : ℝ) : moment N (r • π) = r * moment N π := by
  simp only [moment, Pi.smul_apply, smul_eq_mul, mul_sum]
  congr with k
  ring
end ArithmeticTriangleRemovalInVectorSpaces
