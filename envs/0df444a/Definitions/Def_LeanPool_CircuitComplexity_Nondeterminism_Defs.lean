-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
-- name    : LeanPool_CircuitComplexity_Nondeterminism_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:55.897593+00:00
-- url     : https://prove2.me/theorems/2bd5b5df-3e33-4f00-8ae2-e5d302e27c7a
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism/Defs.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Mathlib.Data.Fintype.Pi
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
variable {k m : Nat}
def existQuantify (f : BitString (k + m) → Bool) : BitString m → Bool :=
  fun y => decide (∃ x : BitString k, f (Fin.append x y) = true)
def forallQuantify (f : BitString (k + m) → Bool) : BitString m → Bool :=
  fun y => decide (∀ x : BitString k, f (Fin.append x y) = true)
def restrictFirst (f : BitString ((k + 1) + m) → Bool) (b : Bool) :
    BitString (k + m) → Bool :=
  fun z => f (fun i => if h : i.val = 0 then b else z ⟨i.val - 1, by omega⟩)
end CircuitComplexity


