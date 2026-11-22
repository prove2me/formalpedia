-- Prove2me | Definitions.Def_LeanPool_LatinQuarter_Cyclic
-- name    : LeanPool_LatinQuarter_Cyclic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:20:24.300847+00:00
-- url     : https://prove2.me/theorems/0f227508-a1c4-4709-98de-84f82e8a9ece
-- title:
--   Cyclic
-- statement:
--   Definitions and structural lemmas for Cyclic, from Richard Bean; LeanPool contributors's pinned Critical sets in Latin squares development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Cyclic.lean

module
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LatinQuarter_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LatinQuarter
def cyclic (n : ℕ) : Square n := fun r c => r + c
def cornerSet (n : ℕ) : Finset (Cell n) :=
  Finset.univ.filter (fun p => p.1.val + p.2.val < n / 2 ∨
    n + n / 2 ≤ p.1.val + p.2.val)
def fillingOrder {n : ℕ} (r c : Fin n) : ℕ := r.val * n + (n - 1 - c.val)
end LatinQuarter


