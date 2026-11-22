-- Prove2me | Definitions.Def_LeanPool_Egrs75_LeafInduction
-- name    : LeanPool_Egrs75_LeafInduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:26:23.303954+00:00
-- url     : https://prove2.me/theorems/a1b7b379-2fd1-4b0d-8edf-6002e5b24b80
-- title:
--   Leaf Induction
-- statement:
--   Definitions and structural lemmas for Leaf Induction, from Egor Lyfar; LeanPool contributors's pinned The EGRS two-prime theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/LeafInduction.lean

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Data.Finset.Attr
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Egrs75.LeafInduction
open Nat
open Egrs75
def badDigitsQ (q n : ℕ) : List ℕ :=
  (Nat.digits q n).filter (fun d => decide ((q - 1) / 2 < d))
def badCountQ (q n : ℕ) : ℕ := (badDigitsQ q n).length
end Egrs75.LeafInduction


