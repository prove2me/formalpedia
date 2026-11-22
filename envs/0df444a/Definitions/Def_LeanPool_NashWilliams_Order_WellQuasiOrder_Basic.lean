-- Prove2me | Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Basic
-- name    : LeanPool_NashWilliams_Order_WellQuasiOrder_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:41:59.257354+00:00
-- url     : https://prove2.me/theorems/bb0c5996-c574-4fb8-9b4e-8b757c371d9c
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Yann Pequignot; LeanPool contributors's pinned Nash-Williams fronts and better-quasi-orders development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Basic.lean

module
public import Mathlib.Order.WellQuasiOrder
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set
noncomputable section
namespace Sequences
variable {α : Type*}
def IsBad (r : α → α → Prop) (f : ℕ → α) : Prop :=
  ∀ m n : ℕ, m < n → ¬ r (f m) (f n)
def IsPerfect (r : α → α → Prop) (f : ℕ → α) : Prop :=
  ∀ m n : ℕ, m < n → r (f m) (f n)
end Sequences
open Sequences
variable {α : Type*} {r : α → α → Prop}
end


