-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
-- name    : LeanPool_OrderClosures_BanLat_Disjoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:12:50.426836+00:00
-- url     : https://prove2.me/theorems/536bf8c0-1809-43ff-b287-24c579f5f5ec
-- title:
--   Disjoint
-- statement:
--   Definitions and structural lemmas for Disjoint, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped Topology
open Filter Finset
section LatticeOrdered
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
def IsVLDisjoint (x y : X) : Prop := |x| ⊓ |y| = 0
end LatticeOrdered
section VectorLattice
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
def IsDisjointSet (Λ : Set X) : Prop :=
  0 ∉ Λ ∧ ∀ ⦃a⦄, a ∈ Λ → ∀ ⦃b⦄, b ∈ Λ → a ≠ b → IsVLDisjoint a b
def IsMaximalDisjoint (Λ : Set X) : Prop :=
  Maximal IsDisjointSet Λ
end VectorLattice


