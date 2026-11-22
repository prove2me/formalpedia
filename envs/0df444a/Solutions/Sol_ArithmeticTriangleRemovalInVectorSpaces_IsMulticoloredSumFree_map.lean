-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:16.092279+00:00
-- url     : https://prove2.me/submissions/c92a0129-fd79-40ae-9d6c-acddbcb8b473

module
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic

set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces
variable {ι G H : Type*} [AddCommGroup G] [AddCommGroup H]
open ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree
variable {x y z : ι → G}
namespace ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree
theorem _root_.solution (h : IsMulticoloredSumFree x y z) (e : G →+ H) (he : Function.Injective e) :
    IsMulticoloredSumFree (e ∘ x) (e ∘ y) (e ∘ z) := by
  intro i j k
  rw [← h, Function.comp_apply, Function.comp_apply, Function.comp_apply, ← map_add, ← map_add,
    ← e.map_zero, he.eq_iff]
end ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree
