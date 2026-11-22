-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_AC0
-- name    : LeanPool_CircuitComplexity_AC0
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:10:54.929165+00:00
-- url     : https://prove2.me/theorems/dc748321-2380-4a81-9bb0-be048e93f538
-- title:
--   AC0
-- statement:
--   Definitions and structural lemmas for AC0, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/AC0.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_AC0_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
def parityFamily : BoolFunFamily := fun N => Schnorr.xorBool N
end CircuitComplexity


