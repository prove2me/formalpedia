-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
-- name    : LeanPool_OrderClosures_BanLat_Convergences_Order
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:10:35.83781+00:00
-- url     : https://prove2.me/theorems/87e1fe9a-1084-49a7-9ee6-9d63246457f4
-- title:
--   Order
-- statement:
--   Definitions and structural lemmas for Order, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
def OrderConvergesTo {ι : Type v} [Preorder ι] (u : ι → X) (x : X) : Prop :=
  ∃ (κ : Type u) (_ : Preorder κ) (_ : IsDirected κ (· ≤ ·)) (_ : Nonempty κ),
    ∃ r : κ → X,
      Antitone r ∧
        (∀ k, 0 ≤ r k) ∧
        IsGLB (Set.range r) 0 ∧
        ∀ k, ∀ᶠ i in Filter.atTop, |u i - x| ≤ r k
namespace OrderConvergesTo
end OrderConvergesTo


