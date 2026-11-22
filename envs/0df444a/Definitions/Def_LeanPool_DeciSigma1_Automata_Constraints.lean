-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
-- name    : LeanPool_DeciSigma1_Automata_Constraints
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:19:12.016455+00:00
-- url     : https://prove2.me/theorems/b5272c7d-a910-42e3-92dc-c9614dfeacc5
-- title:
--   Constraints
-- statement:
--   Definitions and structural lemmas for Constraints, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1
open DeciSigma1.Constraints
namespace Automata
section Guarded
variable {α S T : Type}
def guardedPair (good : S → T → Prop) [∀ s t, Decidable (good s t)] (s : S) (t : T) :
    Option (S × T) :=
  if good s t then some (s, t) else none
def guardedStep (f : S → α → S) (g : T → α → T) (good : S → T → Prop)
    [∀ s t, Decidable (good s t)] : Option (S × T) → α → Option (S × T)
  | none, _ => none
  | some (s, t), a => guardedPair good (f s a) (g t a)
variable (f : S → α → S) (g : T → α → T) (good : S → T → Prop) [∀ s t, Decidable (good s t)]
end Guarded
abbrev Config (n : ℕ) (V : Type*) := V × List (Fin n)
inductive Move {n : ℕ} {V : Type*} (Γ : List (LitT n V)) : Config n V → Config n V → Prop
  | copy {u v w} : LitT.le u v ∈ Γ → Move Γ (u, w) (v, w)
  | push {a u w} (i : Fin n) : LitT.fLe a u ∈ Γ → Move Γ (a i, w) (u, i :: w)
  | pop {u a w} (i : Fin n) : LitT.leF u a ∈ Γ → Move Γ (u, i :: w) (a i, w)
abbrev Moves {n : ℕ} {V : Type*} (Γ : List (LitT n V)) : Config n V → Config n V → Prop :=
  Relation.ReflTransGen (Move Γ)
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
def up (Γ : List (LitT n V)) (x : V) :
    Finset V := Finset.univ.filter fun y => (x, y) ∈ derivedPairs Γ
def down (Γ : List (LitT n V)) (y : V) :
    Finset V := Finset.univ.filter fun x => (x, y) ∈ derivedPairs Γ
def upperStep (Γ : List (LitT n V)) (P : Finset V) (c : Fin n) : Finset V :=
  Finset.univ.filter fun b => ∃ r ∈ P, ∃ p ∈ upperLits Γ, p.1 = r ∧ (p.2 c, b) ∈ derivedPairs Γ
def lowerStep (Γ : List (LitT n V)) (Q : Finset V) (c : Fin n) : Finset V :=
  Finset.univ.filter fun a => ∃ r ∈ Q, ∃ p ∈ lowerLits Γ, p.2 = r ∧ (a, p.1 c) ∈ derivedPairs Γ
def upper (Γ : List (LitT n V)) (x : V) : Semiautomaton (Fin n) (Finset V) :=
  ⟨up Γ x, upperStep Γ⟩
def lower (Γ : List (LitT n V)) (y : V) : Semiautomaton (Fin n) (Finset V) :=
  ⟨down Γ y, lowerStep Γ⟩
def upperRun (Γ : List (LitT n V)) (x : V) (w : List (Fin n)) : Finset V := (upper Γ x).run w
def lowerRun (Γ : List (LitT n V)) (y : V) (w : List (Fin n)) : Finset V := (lower Γ y).run w
def Normal (Γ : List (LitT n V)) (x : V) (u : List (Fin n)) (y : V) (t : List (Fin n)) : Prop :=
  ∃ β γ σ v, u = β ++ σ ∧ t = γ ++ σ ∧ v ∈ upperRun Γ x β ∧ v ∈ lowerRun Γ y γ
end Automata
end DeciSigma1
namespace DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
end DeciSigma1.Constraints


