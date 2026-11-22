-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_Internal_Valiant
-- name    : LeanPool_CircuitComplexity_Internal_Valiant
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:55.59823+00:00
-- url     : https://prove2.me/theorems/77c93d9d-8489-4a52-9d0e-33cb1d0a5cc7
-- title:
--   Valiant
-- statement:
--   Definitions and structural lemmas for Valiant, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Valiant.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_Digraph_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Digraph
noncomputable def canonicalLabel {V : Type*} [Fintype V]
    (G : Digraph V) (v : V) : Nat :=
  have _hV : Fintype V := ‹_›
  sSup { n | ∃ p : Fin (n + 1) → V, G.IsSimplePath p ∧ p (Fin.last n) = v } + 1
end Digraph
namespace CircuitComplexity.Valiant
open Digraph
variable {V : Type*} [Fintype V]
def IsLegalLabeling (G : Digraph V) (ℓ : V → ℕ) : Prop :=
  ∀ u v, G.Adj u v → ℓ u < ℓ v
section LegalLabelHelpers
variable {V : Type*}
end LegalLabelHelpers
def firstDifferBit (k a b : ℕ) : ℕ :=
  if a = b then 0 else k - Nat.log2 (a ^^^ b)
variable [DecidableEq V]
noncomputable def levelEdges
    (G : Digraph V) [DecidableRel G.Adj] (k i : ℕ) : Finset (V × V) :=
  G.edgeFinset.filter (fun e =>
    firstDifferBit k (G.canonicalLabel e.1 - 1) (G.canonicalLabel e.2 - 1) = i)
def maskOutI (k : ℕ) (I : Finset ℕ) (x : ℕ) : ℕ :=
  ∑ i ∈ (Finset.Ioc 0 k) \ I,
    (if x.testBit (k - i) then 2 ^ (k - i) else 0)
end CircuitComplexity.Valiant


