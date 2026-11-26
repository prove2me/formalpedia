-- Prove2me | Definitions.Def_Four
-- name    : Four
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T23:09:15.783727+00:00
-- url     : https://prove2.me/theorems/03af6e6d-4d17-4b77-80ad-7fe02e66585f
-- title:
--   Four
-- statement:
--   Definitions and structural lemmas for Four, from Jason Davies (jasondavies/permutation-supersequence-length; see pinned Apache-2.0 LICENSE and README.md)'s pinned Shortest word containing every permutation of ten symbols as a subsequence development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Four.lean

import Definitions.Def_Frequency
set_option autoImplicit true
namespace Supersequence
open List
variable {α : Type} [DecidableEq α]
def LengthBound (k L : Nat) := ∀ w : List (Fin k), Universal w → L ≤ w.length
def mass (w A : List α) := (A.map w.count).sum
def rest (A S : List α) := A.filter (fun a => !S.contains a)
def Compatible (A p q : List α) : Prop :=
  ∀ S : List α, S ⊆ A → Covers (· ∈ S) p ∨ Covers (· ∈ rest A S) q
def onesIn (p A : List α) := A.filter (fun a => p.count a == 1)
end Supersequence


