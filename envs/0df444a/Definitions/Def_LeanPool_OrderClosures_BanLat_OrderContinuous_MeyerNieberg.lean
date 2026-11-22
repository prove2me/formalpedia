-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
-- name    : LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:13:58.766155+00:00
-- url     : https://prove2.me/theorems/ff3a8e7f-ed34-4842-add8-05d770196dc5
-- title:
--   Meyer Nieberg
-- statement:
--   Definitions and structural lemmas for Meyer Nieberg, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/MeyerNieberg.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
@[expose] public section
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
section Disjointification
variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E]
def IsKDisjointSeq (k : ℕ) (u : ℕ → E) : Prop :=
  ∀ s : Finset ℕ, s.card = k → ∀ hs : s.Nonempty,
    s.inf' hs (fun n => |u n|) = 0
end Disjointification
section NormCriterion
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [NormedVectorLattice E]
end NormCriterion
namespace BanachLattice
variable [BanachLattice X]
end BanachLattice


