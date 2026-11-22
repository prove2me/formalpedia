-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.triangles_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:55.4009+00:00
-- url     : https://prove2.me/submissions/092a6d8f-c716-49cf-be17-6314b616639f

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
theorem _root_.solution (hX : X' ⊆ X) (hY : Y' ⊆ Y) (hZ : Z' ⊆ Z) :
    triangles X' Y' Z' ⊆ triangles X Y Z :=
  filter_subset_filter _ (product_subset_product hX (product_subset_product hY hZ))
end ArithmeticTriangleRemovalInVectorSpaces
