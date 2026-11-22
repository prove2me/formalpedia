-- Prove2me | Definitions.Def_LeanPool_PebblingLean_GraphIso
-- name    : LeanPool_PebblingLean_GraphIso
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:49:41.834722+00:00
-- url     : https://prove2.me/theorems/d8c86526-9aff-4f7f-bdc5-1a1172f25c3d
-- title:
--   Graph Iso
-- statement:
--   Definitions and structural lemmas for Graph Iso, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/GraphIso.lean

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Tactic.Bound.Init
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
universe u v
structure GraphIso {V : Type u} {W : Type v} (G : Graph V) (H : Graph W) where
  /-- The underlying equivalence between the vertex types. -/
  toEquiv : V ≃ W
  /-- The equivalence preserves and reflects adjacency. -/
  adj_iff : ∀ {x y : V}, G.Adj x y ↔ H.Adj (toEquiv x) (toEquiv y)
namespace GraphIso
variable {V : Type u} {W : Type v} {G : Graph V} {H : Graph W}
def mapDistribution (iso : GraphIso G H) (D : Pebbling V) : Pebbling W :=
  fun w => D (iso.toEquiv.symm w)
@[simp]
theorem mapDistribution_apply (iso : GraphIso G H) (D : Pebbling V) (v : V) :
    iso.mapDistribution D (iso.toEquiv v) = D v := by
  simp [mapDistribution]
def symm (iso : GraphIso G H) : GraphIso H G where
  toEquiv := iso.toEquiv.symm
  adj_iff := by
    intro x y
    simpa using
      (iso.adj_iff (x := iso.toEquiv.symm x) (y := iso.toEquiv.symm y)).symm
end GraphIso
end PebblingLean


