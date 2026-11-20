-- Prove2me | Definitions.Def_ForbiddenMatrix_PermutationPatterns
-- name    : ForbiddenMatrix_PermutationPatterns
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:09:56.602176+00:00
-- url     : https://prove2.me/theorems/01f6ae4b-2501-451a-8eee-ba1163fe3659
-- title:
--   Permutation Patterns
-- statement:
--   Definitions and structural lemmas for Permutation Patterns, from Yaël Dillies and the Forbidden Matrix contributors's pinned Forbidden-matrix containment development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean

module
public import Definitions.Def_ForbiddenMatrix_SmallPatterns
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Nat.Choose.Basic
public import Definitions.Def_ForbiddenMatrix_Mathlib_Data_ZMod_Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Qify
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Set OrderDual Equiv
variable {k n q : ℕ}
def PermPattern (σ : Equiv.Perm (Fin n)) (i j : Fin n) : Prop := σ i = j
def rectPtsetq (n q i j : ℕ) := rectPtset n (q * i) (q * (i+1)) (q * j) (q * (j+1))
open scoped Classical in
noncomputable def rectPtsetqMatrix (M : Fin n → Fin n → Prop) (q i j : ℕ) : Finset (Fin n × Fin n) :=
  {(a, b) | M a b ∧ (a, b) ∈ rectPtsetq n q i j}
def blkMatrix (M : Fin n → Fin n → Prop) (q : ℕ) : Fin (n / q) → Fin (n / q) → Prop :=
  fun i j ↦ ∃ p : Fin n × Fin n, M p.1 p.2 ∧ p ∈ rectPtsetq n q i j
open scoped Classical in
noncomputable def blk_den (M : Fin n → Fin n → Prop) (i j : Fin (n / q)) : ℕ := #(rectPtsetqMatrix M q i j)


