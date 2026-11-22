-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.mass_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:00.637336+00:00
-- url     : https://prove2.me/submissions/13001b6f-2b78-42f3-bade-4b13e395419e

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
theorem _root_.solution : mass N (π - π') = mass N π - mass N π' := by
  simp [mass, sum_sub_distrib]
end ArithmeticTriangleRemovalInVectorSpaces
