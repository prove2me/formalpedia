-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:40.5948+00:00
-- url     : https://prove2.me/submissions/c6e98eab-d22b-499e-b1be-523f2ed18f82

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
theorem _root_.solution (h : IsMulticoloredSumFree x y z) (κ : Type*) :
    IsMulticoloredSumFree (fun (I : κ → ι) t ↦ x (I t)) (fun I t ↦ y (I t)) fun I t ↦ z (I t) := by
  intro I J K
  simp only [funext_iff, Pi.add_apply, Pi.zero_apply, h _ _ _]
  grind
end ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree
