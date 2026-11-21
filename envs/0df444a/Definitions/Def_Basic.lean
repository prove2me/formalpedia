-- Prove2me | Definitions.Def_Basic
-- name    : Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T15:05:39.34195+00:00
-- url     : https://prove2.me/theorems/3b7e08b7-510f-4546-9c3c-49ca0cef62d4
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from gjenca and contributors's pinned N-free posets and orthomodularity development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean

import Mathlib
set_option autoImplicit true
class Orthoset (α : Type*) where
  /-- The orthogonality relation -/
  perp : α → α → Prop
  perp_symm : Symmetric perp
  perp_irrefl : ∀ a : α, ¬ perp a a
notation:50 a " ⊥ " b => Orthoset.perp a b
def Incomparable {P : Type*} [PartialOrder P] (a b : P) : Prop := ¬ a ≤ b ∧ ¬ b ≤ a
@[reducible] instance instOrthosetOfPartialOrder {P : Type*} [PartialOrder P] : Orthoset P where
  perp := Incomparable
  perp_symm := fun _ _ h => ⟨h.2, h.1⟩
  perp_irrefl := fun _ h => h.1 le_rfl
variable {O : Type*} [Orthoset O]
def orthComp (X : Set O) : Set O := {y | ∀ x ∈ X, x ⊥ y}
def IsOrthoclosed (X : Set O) : Prop := orthComp (orthComp X) = X
def IsOrthoBase (B X : Set O) : Prop :=
  B ⊆ X ∧
  (∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → b₁ ⊥ b₂) ∧
  (∀ x ∈ X, (∀ b ∈ B, x ⊥ b) → x ∈ B)
def IsDaceySubset (X : Set O) : Prop :=
  ∀ B : Set O, IsOrthoBase B X → orthComp (orthComp B) = X
def IsDacey (O : Type*) [Orthoset O] : Prop :=
  ∀ X : Set O, IsOrthoclosed X → IsDaceySubset X
variable {P : Type*} [PartialOrder P]
def incompSet (x : P) : Set P := {z | x ⊥ z}
def IsN (a b c d : P) : Prop :=
  a < c ∧ b ⋖ c ∧ b < d ∧ (a ⊥ b) ∧ (a ⊥ d) ∧ (c ⊥ d)
def IsNFree (P : Type*) [PartialOrder P] : Prop :=
  ¬ ∃ a b c d : P, IsN a b c d
def IsVeryWeakN (a b c d : P) : Prop :=
  a < c ∧ b < c ∧ b < d ∧ (a ⊥ b) ∧ (c ⊥ d)
def IsWeakN (a b c d : P) : Prop :=
  a < c ∧ b ⋖ c ∧ b < d ∧ (a ⊥ b) ∧ (c ⊥ d)
def IsCompatible (P : Type*) [PartialOrder P] : Prop :=
  ∀ x y : P, ¬ (x ⊥ y) →
    ∃ z : P, incompSet x ∪ incompSet y ⊆ incompSet z
def IsX (a b c d m : P) : Prop :=
  a < m ∧ m < c ∧ b < m ∧ m < d ∧ (a ⊥ b) ∧ (c ⊥ d)
def IsCoveringX (a b c d m : P) : Prop :=
  a < m ∧ m ⋖ c ∧ b < m ∧ m < d ∧ (a ⊥ b) ∧ (c ⊥ d)


