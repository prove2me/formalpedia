-- Prove2me | Definitions.Def_NonCutPoints_Solution
-- name    : NonCutPoints_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:30:46.385994+00:00
-- url     : https://prove2.me/theorems/f949f06b-0a30-44c6-8be2-a151e667485c
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/non-cut-points-lean; see pinned Apache-2.0 LICENSE and source headers)'s pinned Non-Cut Points of Hausdorff Continua development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/non-cut-points-lean/blob/b1d0ed0338d098a4c84622828390cc84027df8dc/Solution.lean

module
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Order.Zorn
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set
universe u
namespace NonCutPoints
variable {X : Type u} [tX : TopologicalSpace X]
def IsNonCutPoint (C : Set X) (x : X) : Prop :=
  x ∈ C ∧ IsConnected (C \ {x})
structure Cutting (x : X) where
  left : Set X
  right : Set X
  left_open : IsOpen left
  right_open : IsOpen right
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  disjoint : Disjoint left right
  cover : left ∪ right = {x}ᶜ
def Cutting.swap {x : X} (d : Cutting x) : Cutting x where
  left := d.right
  right := d.left
  left_open := d.right_open
  right_open := d.left_open
  left_nonempty := d.right_nonempty
  right_nonempty := d.left_nonempty
  disjoint := d.disjoint.symm
  cover := (union_comm _ _).trans d.cover
end NonCutPoints


