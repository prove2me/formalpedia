-- Prove2me | Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
-- name    : LeanPool_NashWilliams_Combinatorics_Front_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:41:23.704023+00:00
-- url     : https://prove2.me/theorems/544c7ceb-523c-422f-829a-a4b7b8ab08d9
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Yann Pequignot; LeanPool contributors's pinned Nash-Williams fronts and better-quasi-orders development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Defs.lean

module
public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.Widget.Calc
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set List
noncomputable section
namespace List
end List
namespace Front
def IsInit (s : List ℕ) (N : ℕ → ℕ) : Prop :=
  s = (List.range s.length).map N
structure IsFront (F : Set (List ℕ)) (M : ℕ → ℕ) : Prop where
  /-- `M` is the increasing enumeration of an infinite subset of `ℕ`; in particular `range M`
  is infinite. Without this a degenerate `M` (e.g. constant) would vacuously admit "fronts". -/
  mono : StrictMono M
  /-- Every element of `F` is the strictly increasing enumeration of a finite set. -/
  sorted : ∀ s ∈ F, s.Pairwise (· < ·)
  /-- Every element of `F` is a subset of `M`. -/
  subM : ∀ s ∈ F, ∀ x ∈ s, x ∈ Set.range M
  /-- Base: `F = {∅}` or the elements of `F` cover `M`. -/
  base : F = {[]} ∨ (⋃ s ∈ F, {x | x ∈ s}) = Set.range M
  /-- Incomparability: `F` is an antichain for the prefix order. -/
  incomp : ∀ s ∈ F, ∀ t ∈ F, s <+: t → s = t
  /-- Density: every subsequence `M ∘ g` of `M` has an initial segment in `F`. -/
  dense : ∀ g : ℕ → ℕ, StrictMono g → ∃ t ∈ F, IsInit t (M ∘ g)
def powK (M : ℕ → ℕ) (k : ℕ) : Set (List ℕ) :=
  {s | s.length = k ∧ s.Pairwise (· < ·) ∧ ∀ x ∈ s, x ∈ Set.range M}
def schreier (M : ℕ → ℕ) : Set (List ℕ) :=
  {s | (∃ a, s.head? = some a ∧ s.length = a + 1) ∧
    s.Pairwise (· < ·) ∧ ∀ x ∈ s, x ∈ Set.range M}
end Front


