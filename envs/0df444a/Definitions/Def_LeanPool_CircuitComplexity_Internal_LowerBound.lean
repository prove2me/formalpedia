-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_Internal_LowerBound
-- name    : LeanPool_CircuitComplexity_Internal_LowerBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:09:19.294703+00:00
-- url     : https://prove2.me/theorems/4b876d11-edbc-4e07-ba10-ab6f62d693f5
-- title:
--   Lower Bound
-- statement:
--   Definitions and structural lemmas for Lower Bound, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_EssentialInput
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Sum
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
namespace Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]
def coveredInputs (g : Gate B (N + G)) : Finset (Fin N) :=
  Finset.univ.filter fun i : Fin N =>
    ∃ k : Fin g.fanIn, (g.inputs k).val = i.val
def gateAt (c : Circuit B N M G) : Fin G ⊕ Fin M → Gate B (N + G)
  | .inl g => c.gates g
  | .inr j => c.outputs j
end Circuit
end CircuitComplexity


