-- Prove2me | Definitions.Def_LeanPool_Egrs75_Defs
-- name    : LeanPool_Egrs75_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:25:56.51218+00:00
-- url     : https://prove2.me/theorems/747563f8-b208-473c-8f74-f3421193f8dd
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Egor Lyfar; LeanPool contributors's pinned The EGRS two-prime theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/Defs.lean

module
public import Definitions.Def_LeanPool_Egrs75_CentralBinomialDigits
public import Mathlib.Data.Finset.Attr
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Egrs75
open Nat
def LowDigits (p n : ℕ) : Prop := ∀ d ∈ Nat.digits p n, d ≤ (p - 1) / 2
end Egrs75


