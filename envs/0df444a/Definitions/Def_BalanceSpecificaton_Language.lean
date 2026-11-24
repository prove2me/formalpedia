-- Prove2me | Definitions.Def_BalanceSpecificaton_Language
-- name    : BalanceSpecificaton_Language
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:29:55.132682+00:00
-- url     : https://prove2.me/theorems/0cefa91c-0560-4d4c-8ec6-82261185f6ca
-- title:
--   Language
-- statement:
--   Definitions and structural lemmas for Language, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Language.lean

module
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BalanceSpecification
abbrev Word (A : Type*) := List A
abbrev Configuration (A : Type*) := ℤ → A
abbrev ShiftSpace (A : Type*) [TopologicalSpace A] :=
  SymbolicDynamics.FullShift.Subshift A ℤ
def block {A : Type*} (x : Configuration A) (k : ℤ) (n : ℕ) : Word A :=
  List.ofFn fun i : Fin n => x (k + (i : ℕ))
def language {A : Type*} [TopologicalSpace A] (X : ShiftSpace A) : Set (Word A) :=
  {w | ∃ x ∈ X.carrier, ∃ k : ℤ, block x k w.length = w}
def IsFactorial {A : Type*} (L : Set (Word A)) : Prop :=
  ∀ ⦃u v⦄, u <:+: v → v ∈ L → u ∈ L
def words {A : Type*} [TopologicalSpace A] (X : ShiftSpace A) (n : ℕ) : Set (Word A) :=
  {w | w ∈ language X ∧ w.length = n}
def Irreducible {A : Type*} [TopologicalSpace A] (X : ShiftSpace A) : Prop :=
  ∀ u ∈ language X, ∀ v ∈ language X,
    ∃ w ∈ language X, u ++ w ++ v ∈ language X
def IsSynchronizing {A : Type*} (L : Set (Word A)) (w : Word A) : Prop :=
  w ∈ L ∧ ∀ u v, u ++ w ∈ L → w ++ v ∈ L → u ++ w ++ v ∈ L
def Synchronized {A : Type*} [TopologicalSpace A] (X : ShiftSpace A) : Prop :=
  Irreducible X ∧ ∃ w, IsSynchronizing (language X) w
def HasSpecification {A : Type*} [TopologicalSpace A] (X : ShiftSpace A) : Prop :=
  ∃ N : ℕ, ∀ u ∈ language X, ∀ v ∈ language X,
    ∃ w ∈ language X, w.length = N ∧ u ++ w ++ v ∈ language X
def HasVariableSpecification {A : Type*} [TopologicalSpace A] (X : ShiftSpace A) : Prop :=
  ∃ N : ℕ, ∀ u ∈ language X, ∀ v ∈ language X,
    ∃ w ∈ language X, w.length ≤ N ∧ u ++ w ++ v ∈ language X
end BalanceSpecification


