-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_AC0_Defs
-- name    : LeanPool_CircuitComplexity_AC0_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:10:27.589901+00:00
-- url     : https://prove2.me/theorems/fa917637-5f74-43be-912c-e594056baaae
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/AC0/Defs.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
def InAC0 (f : BoolFunFamily) : Prop :=
  ∃ (d c : Nat), ∀ (N : Nat) [NeZero N],
    ∃ (G : Nat) (circuit : Circuit Basis.unboundedAON N 1 G),
      circuit.depth ≤ d ∧ circuit.size ≤ N ^ c ∧
      (fun x => (circuit.eval x) 0) = f N
end CircuitComplexity


