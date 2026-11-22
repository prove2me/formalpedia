-- Prove2me | Definitions.Def_LeanPool_PureNock_Trace
-- name    : LeanPool_PureNock_Trace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:59:44.7864+00:00
-- url     : https://prove2.me/theorems/df716b1b-e7e3-4ab5-ab1e-da7c4d0a2985
-- title:
--   Trace
-- statement:
--   Definitions and structural lemmas for Trace, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nock
namespace Verb
def Step (a b : Verb) : Prop := next a = some b
def Consistent : List Verb → Prop
  | []              => True
  | [_]             => True
  | a :: b :: rest  => Step a b ∧ Consistent (b :: rest)
def Complete (T : List Verb) : Prop := ∃ v, T.getLast? = some v ∧ next v = none
def TraceOf (F : Verb) (T : List Verb) : Prop := T.head? = some F ∧ Consistent T
def Continuation (F c : Verb) : Prop := ∃ T, TraceOf F T ∧ c ∈ T
def Valid (F : Verb) : Prop :=
  ∃ T v, TraceOf F T ∧ T.getLast? = some v ∧ next v = none ∧ isTerminal v = true
def Invalid (F : Verb) : Prop :=
  ∃ T v, TraceOf F T ∧ T.getLast? = some v ∧ next v = none ∧ isTerminal v = false
def Finite (F : Verb) : Prop := ∃ T, TraceOf F T ∧ Complete T
def FiniteTransition (F : Verb) : Prop :=
  ∃ (F0 : Verb) (T : List Verb), TraceOf F0 T ∧ Complete T ∧ F ∈ T
def ConsistentR (R : Verb → Verb → Prop) : List Verb → Prop
  | []             => True
  | [_]            => True
  | a :: b :: rest => R a b ∧ ConsistentR R (b :: rest)
def TraceOfR (R : Verb → Verb → Prop) (F : Verb) (T : List Verb) : Prop :=
  T.head? = some F ∧ ConsistentR R T
def size (F : Verb) : Nat := F.leaves
def FiniteΛ (Λ : Nat) (F : Verb) : Prop := Finite F ∧ size F ≤ Λ
def FiniteTransitionΛ (Λ : Nat) (F : Verb) : Prop := FiniteTransition F ∧ size F ≤ Λ
def IsNockProgram (Λ : Nat) (F : Verb) : Prop :=
  (∃ subject formula, F = .node .star subject formula
      ∧ isTerminal subject = true ∧ isTerminal formula = true)
    ∧ size F ≤ Λ
def NockValidProgramΛ (Λ : Nat) (F : Verb) : Prop := IsNockProgram Λ F ∧ Valid F
def SubLang (P Q : Verb → Prop) : Prop := ∀ ⦃F⦄, P F → Q F
def SSubLang (P Q : Verb → Prop) : Prop := SubLang P Q ∧ ∃ F, Q F ∧ ¬ P F
def StepROM (a b : Verb) : Prop := nextROM a = some b
def CompleteROM (T : List Verb) : Prop := ∃ v, T.getLast? = some v ∧ nextROM v = none
def TraceOfROM (F : Verb) (T : List Verb) : Prop := T.head? = some F ∧ ConsistentR StepROM T
def FiniteROM (F : Verb) : Prop := ∃ T, TraceOfROM F T ∧ CompleteROM T
def FiniteROMΛ (Λ : Nat) (F : Verb) : Prop := FiniteROM F ∧ size F ≤ Λ
def ValidROM (F : Verb) : Prop :=
  ∃ T v, TraceOfROM F T ∧ T.getLast? = some v ∧ nextROM v = none ∧ isTerminal v = true
end Verb
end Nock


