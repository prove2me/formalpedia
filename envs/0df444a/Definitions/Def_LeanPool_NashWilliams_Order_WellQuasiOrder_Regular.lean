-- Prove2me | Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
-- name    : LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:41:23.573206+00:00
-- url     : https://prove2.me/theorems/7f0b2672-1034-4e9f-8079-d9c337206892
-- title:
--   Regular
-- statement:
--   Definitions and structural lemmas for Regular, from Yann Pequignot; LeanPool contributors's pinned Nash-Williams fronts and better-quasi-orders development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Regular.lean

module
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Order.WellFoundedSet
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set Preorder
noncomputable section
namespace Preorder
def IsRegularSeq {Q : Type*} (r : Q → Q → Prop) (f : ℕ → Q) : Prop :=
  ∀ i : ℕ, {j : ℕ | r (f i) (f j)}.Infinite
end Preorder
instance List.SublistForall₂.instIsPreorder {Q : Type*} (r : Q → Q → Prop) [IsPreorder Q r] :
    IsPreorder (List Q) (List.SublistForall₂ r) where
  refl := (List.SublistForall₂.is_refl (Rₐ := r)).refl
  trans := (List.SublistForall₂.is_trans (Rₐ := r)).trans
end


