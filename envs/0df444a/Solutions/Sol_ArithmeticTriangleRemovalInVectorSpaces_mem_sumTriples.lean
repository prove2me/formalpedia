-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:14.62069+00:00
-- url     : https://prove2.me/submissions/7505ac5d-7ab1-47db-b6b9-424b295dfdc7

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {N a b c : ℕ} : (a, b, c) ∈ sumTriples N ↔ a + b + c = N := by
  simp only [sumTriples, mem_filter, mem_product, mem_range]
  grind
end ArithmeticTriangleRemovalInVectorSpaces
