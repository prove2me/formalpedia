-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
-- name    : LeanPool_OrderClosures_BanLat_OrderUnit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:13:17.182392+00:00
-- url     : https://prove2.me/theorems/a69f6c3b-5500-4b0e-b676-6a9d89c2f0a4
-- title:
--   Order Unit
-- statement:
--   Definitions and structural lemmas for Order Unit, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderUnit.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
@[expose] public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
def WeakOrderUnit (e : X) : Prop :=
  0 ≤ e ∧ ∀ x : X, IsVLDisjoint x e → x = 0
def StrongOrderUnit (e : X) : Prop :=
  0 ≤ e ∧ ∀ x : X, ∃ c : ℝ, 0 ≤ c ∧ |x| ≤ c • e


