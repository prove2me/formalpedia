-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.card_triangles_piFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:39.245918+00:00
-- url     : https://prove2.me/submissions/41b1e6e6-747c-451e-908c-816a6205dd21

module
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_triangles
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_triangles

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
variable {X Y Z X' Y' Z' : Finset G} {x y z : G}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution (X Y Z : Finset G) (k : ℕ) :
    #(triangles (Fintype.piFinset fun _ : Fin k ↦ X) (Fintype.piFinset fun _ ↦ Y)
      (Fintype.piFinset fun _ ↦ Z)) = #(triangles X Y Z) ^ k := by
  rw [← Fintype.card_piFinset_const]
  symm
  apply card_equiv ((Equiv.arrowProdEquivProdArrow _ _ _).trans
    ((Equiv.refl _).prodCongr (Equiv.arrowProdEquivProdArrow _ _ _)))
  simp [triangles, funext_iff, forall_and]
end ArithmeticTriangleRemovalInVectorSpaces
