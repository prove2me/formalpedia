-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.hat_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:24.719721+00:00
-- url     : https://prove2.me/submissions/d73862e8-1df6-4bb9-b77f-c469c70ea479

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
theorem _root_.solution (r : ℝ) (w : ℕ → ℝ) : hat N (r • w) = r • hat N w := by
  ext j
  simp [hat, mul_sum, mul_assoc]
end ArithmeticTriangleRemovalInVectorSpaces
