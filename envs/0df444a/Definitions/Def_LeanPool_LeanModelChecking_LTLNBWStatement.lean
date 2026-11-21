-- Prove2me | Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
-- name    : LeanPool_LeanModelChecking_LTLNBWStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:43:16.176334+00:00
-- url     : https://prove2.me/theorems/c2ce4f7c-310e-4689-8619-b2a78a80a371
-- title:
--   LTLNBWStatement
-- statement:
--   Definitions and structural lemmas for LTLNBWStatement, from György Kurucz; maintained by LeanPool contributors's pinned Formalizations of theorems related to model checking development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/LTLNBWStatement.lean

module
public import Mathlib.Data.Finite.Defs
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.Finiteness.Attr
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanModelChecking
inductive LTL (AP : Type) where
| atom (p : AP)
| not (φ : LTL AP)
| or (φ₁ φ₂ : LTL AP)
| next (φ : LTL AP)
| until (φ₁ φ₂ : LTL AP)
abbrev Letter (AP : Type) := Set AP
def LTL.language {AP} (f : LTL AP) (w : ℕ → Letter AP) : Prop :=
  match f with
  | .atom p => p ∈ w 0
  | .not φ => ¬language φ w
  | .or φ₁ φ₂ => language φ₁ w ∨ language φ₂ w
  | .next φ => language φ (fun j => w (j + 1))
  | .until φ₁ φ₂ =>
    ∃ i, language φ₂ (fun j => w (j + i)) ∧
    ∀ k < i, language φ₁ (fun j => w (j + k))
structure NBW (S : Type) where
  /-- The type of states. -/
  Q : Type
  /-- The set of starting states. -/
  q₀ : Set Q
  /-- The transition relation. -/
  δ : Q → S → Q → Prop
  /-- The set of accepting states. A run is accepting
  if it visits states in `F` infinitely often. -/
  F : Set Q
def NBW.run {S} (A : NBW S) (p : ℕ → A.Q) (w : ℕ → S) :=
  p 0 ∈ A.q₀ ∧ ∀ i, A.δ (p i) (w i) (p (i + 1))
def NBW.language {S} (A : NBW S) (w : ℕ → S) :=
  ∃ p, A.run p w ∧ ∀ i, ∃ j ≥ i, p j ∈ A.F
def forAnyLTLFormulaExistsAnEquivalentNBWStatement :=
  ∀ {AP} (φ : LTL AP), ∃ (A : NBW (Letter AP)), Finite A.Q ∧ φ.language = A.language
end LeanModelChecking


