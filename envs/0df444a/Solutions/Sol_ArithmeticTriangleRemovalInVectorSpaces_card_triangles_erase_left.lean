-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.card_triangles_erase_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:34.076565+00:00
-- url     : https://prove2.me/submissions/0d5704eb-64ae-4c88-9fe9-0a80f72649df

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
theorem _root_.solution (X Y Z : Finset G) (v : G) :
    #(triangles (X.erase v) Y Z) + #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) =
      #(triangles X Y Z) := by
  rw [add_comm, ← card_filter_add_card_filter_not (s := triangles X Y Z) fun (x, _, _) ↦ x = v]
  congr 2
  ext ⟨x, y, z⟩
  simp only [triangles, mem_filter, mem_product, mem_erase]
  grind
end ArithmeticTriangleRemovalInVectorSpaces
