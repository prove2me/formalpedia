-- Prove2me | Definitions.Def_GridHam_Forbidden
-- name    : GridHam_Forbidden
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:23:44.895805+00:00
-- url     : https://prove2.me/theorems/8675ecc0-08c4-45ba-9bb2-0668a74eb4e2
-- title:
--   Forbidden
-- statement:
--   Definitions and structural lemmas for Forbidden, from zzyzek and contributors's pinned Hamiltonian paths in rectangular grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean

module
public import Definitions.Def_GridHam_Coloring
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GridHam
def unitStepB (a b : ℕ) : Bool := decide (a + 1 = b ∨ b + 1 = a)
def unitStepChain : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => unitStepB a b && unitStepChain (b :: rest)
end GridHam


