-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_XOR
-- name    : LeanPool_CircuitComplexity_XOR
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:52.354093+00:00
-- url     : https://prove2.me/theorems/f8da6e22-79e2-45dc-8c41-dc21ab7dfced
-- title:
--   XOR
-- statement:
--   Definitions and structural lemmas for XOR, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/XOR.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
namespace Schnorr
def xorBool : (N : Nat) → BitString N → Bool
  | 0, _ => false
  | _ + 1, x => (x 0).xor (xorBool _ (x ∘ Fin.succ))
end Schnorr
end CircuitComplexity


