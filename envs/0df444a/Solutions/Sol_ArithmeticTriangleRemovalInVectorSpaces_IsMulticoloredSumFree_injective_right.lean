-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.injective_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:07.274886+00:00
-- url     : https://prove2.me/submissions/a83caa66-8bc0-4137-bcff-8091ae989e27

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Abel
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Product

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {ι G W : Type*} [AddCommGroup G] [AddCommGroup W] {x y z : ι → G}
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace IsMulticoloredSumFree
theorem _root_.solution (h : IsMulticoloredSumFree x y z) : Injective z := by
  intro i j hij
  obtain ⟨-, rfl⟩ := (h i i j).1 (hij ▸ (h i i i).2 ⟨rfl, rfl⟩)
  rfl
end IsMulticoloredSumFree
end ArithmeticTriangleRemovalInVectorSpaces
