-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_Pi
-- name    : LeanPool_OrderClosures_BanLat_Pi
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:12:47.565734+00:00
-- url     : https://prove2.me/theorems/59fbb6e3-e000-4bb7-b03d-05424ecf10dc
-- title:
--   Pi
-- statement:
--   Definitions and structural lemmas for Pi, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Pi.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Pi
variable {ι : Type*} {X : ι → Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Lattice (X i)] [∀ i, IsOrderedAddMonoid (X i)]
  [∀ i, VectorLattice (X i)]
instance instVectorLattice : VectorLattice (∀ i, X i) := ⟨⟩
end Pi


