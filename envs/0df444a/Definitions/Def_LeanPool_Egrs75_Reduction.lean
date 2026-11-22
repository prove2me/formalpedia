-- Prove2me | Definitions.Def_LeanPool_Egrs75_Reduction
-- name    : LeanPool_Egrs75_Reduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:26:19.893238+00:00
-- url     : https://prove2.me/theorems/1263df0f-3307-4fc7-8b74-431e35b651d6
-- title:
--   Reduction
-- statement:
--   Definitions and structural lemmas for Reduction, from Egor Lyfar; LeanPool contributors's pinned The EGRS two-prime theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/Reduction.lean

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Attr
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Egrs75
open Nat
def EgrsCrux (p q : ℕ) : Prop := {n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite
end Egrs75


