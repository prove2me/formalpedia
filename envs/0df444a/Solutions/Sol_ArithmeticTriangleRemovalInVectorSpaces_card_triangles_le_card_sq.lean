-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.card_triangles_le_card_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:33.347851+00:00
-- url     : https://prove2.me/submissions/cece7a30-2d24-429a-9ea7-13347c778957

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
theorem _root_.solution [Fintype G] (X Y Z : Finset G) :
    #(triangles X Y Z) ≤ Fintype.card G ^ 2 := by
  rw [sq, ← Fintype.card_prod, ← card_univ]
  refine card_le_card_of_injOn (fun (x, y, _) ↦ (x, y)) (fun _ _ ↦ mem_univ _) ?_
  rintro ⟨x, y, z⟩ ht ⟨x', y', z'⟩ ht' h
  simp only [mem_coe, mem_triangles, Prod.mk.injEq] at ht ht' h ⊢
  grind
end ArithmeticTriangleRemovalInVectorSpaces
