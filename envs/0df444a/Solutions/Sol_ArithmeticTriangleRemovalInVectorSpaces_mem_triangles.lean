-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.mem_triangles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:09:00.08991+00:00
-- url     : https://prove2.me/submissions/bb7f9c2e-6cab-40bb-b13b-c81c993bf6bc

module
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
variable {X Y Z X' Y' Z' : Finset G} {x y z : G}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution : (x, y, z) ∈ triangles X Y Z ↔ x ∈ X ∧ y ∈ Y ∧ z ∈ Z ∧ x + y + z = 0 := by
  simp [triangles, and_assoc]
end ArithmeticTriangleRemovalInVectorSpaces
