-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:23.1058+00:00
-- url     : https://prove2.me/submissions/798667fa-f1c5-4370-a71e-ab24dedd1aee

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
theorem _root_.solution {κ : Type*} (h : IsMulticoloredSumFree x y z) {f : κ → ι} (hf : Function.Injective f) :
    IsMulticoloredSumFree (x ∘ f) (y ∘ f) (z ∘ f) := by
  intro i j k
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, h, hf.eq_iff, hf.eq_iff]
end ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree
