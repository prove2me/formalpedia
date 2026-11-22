-- Prove2me | Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
-- name    : LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:41:43.521579+00:00
-- url     : https://prove2.me/theorems/1beee4ad-b331-4803-a981-986148bda553
-- title:
--   Infinite
-- statement:
--   Definitions and structural lemmas for Infinite, from Yann Pequignot; LeanPool contributors's pinned Nash-Williams fronts and better-quasi-orders development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Ramsey/Infinite.lean

module
public import Mathlib.Data.Finset.Card
public import Definitions.Def_LeanPool_NashWilliams_Data_Fintype_Pigeonhole
public import Definitions.Def_LeanPool_NashWilliams_Data_Nat_Nth
public import Mathlib.Order.Lattice.Nat
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set
noncomputable section
variable {κ : Type*}
structure RamseyState (c : Finset ℕ → κ) (r : ℕ) where
  vert : ℕ
  col : κ
  succ : Set ℕ
  hInf : succ.Infinite
  hgt : ∀ x ∈ succ, vert < x
  hprop : ∀ t : Finset ℕ, ↑t ⊆ succ → t.card = r → c (insert vert t) = col
end


