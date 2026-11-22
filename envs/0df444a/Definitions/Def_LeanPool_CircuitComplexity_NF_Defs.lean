-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
-- name    : LeanPool_CircuitComplexity_NF_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:56.345274+00:00
-- url     : https://prove2.me/theorems/2dc3a2ea-d7f9-4a8a-8bed-a976b494cda6
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/NF/Defs.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
structure Literal (N : Nat) where
  /-- The index of the variable this literal refers to. -/
  var : Fin N
  /-- `true` = positive literal (xᵢ); `false` = negative literal (¬xᵢ). -/
  polarity : Bool
  deriving DecidableEq
def Literal.eval (l : Literal N) (x : BitString N) : Bool :=
  if l.polarity then x l.var else !x l.var
def Literal.neg (l : Literal N) : Literal N :=
  { l with polarity := !l.polarity }
structure CNF (N : Nat) where
  /-- The clauses of the formula. Each clause is a list of literals. -/
  clauses : List (List (Literal N))
namespace CNF
def eval (φ : CNF N) (x : BitString N) : Bool :=
  φ.clauses.all fun clause => clause.any fun l => l.eval x
def complexity (φ : CNF N) : Nat := φ.clauses.length
end CNF
structure DNF (N : Nat) where
  /-- The terms of the formula. Each term is a list of literals. -/
  terms : List (List (Literal N))
namespace DNF
def eval (φ : DNF N) (x : BitString N) : Bool :=
  φ.terms.any fun term => term.all fun l => l.eval x
def complexity (φ : DNF N) : Nat := φ.terms.length
end DNF
def CNF.neg (φ : CNF N) : DNF N :=
  ⟨φ.clauses.map (fun clause => clause.map Literal.neg)⟩
def DNF.neg (φ : DNF N) : CNF N :=
  ⟨φ.terms.map (fun term => term.map Literal.neg)⟩
end CircuitComplexity


