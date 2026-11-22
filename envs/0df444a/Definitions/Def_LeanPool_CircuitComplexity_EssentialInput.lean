-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_EssentialInput
-- name    : LeanPool_CircuitComplexity_EssentialInput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:56.98232+00:00
-- url     : https://prove2.me/theorems/8bf67d77-30ac-413d-b53e-00ee7c3c56a1
-- title:
--   Essential Input
-- statement:
--   Definitions and structural lemmas for Essential Input, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/EssentialInput.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Mathlib.Data.Fintype.Pi
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
def IsEssentialInput {N M : Nat} (f : BitString N → BitString M) (i : Fin N) : Prop :=
  ∃ x : BitString N, f x ≠ f (Function.update x i (!x i))
instance {N M : Nat} {f : BitString N → BitString M} {i : Fin N} :
    Decidable (IsEssentialInput f i) :=
  inferInstanceAs (Decidable (∃ x, f x ≠ f (Function.update x i (!x i))))
def EssentialInputs {N M : Nat} (f : BitString N → BitString M) : Finset (Fin N) :=
  Finset.univ.filter (IsEssentialInput f)
end CircuitComplexity


