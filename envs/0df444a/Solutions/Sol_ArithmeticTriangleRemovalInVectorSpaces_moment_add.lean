-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.moment_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:07.374279+00:00
-- url     : https://prove2.me/submissions/f868fa91-cf0d-400c-8ab7-65148dc693cb

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
theorem _root_.solution : moment N (π + π') = moment N π + moment N π' := by
  simp [moment, mul_add, sum_add_distrib]
end ArithmeticTriangleRemovalInVectorSpaces
