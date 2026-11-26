-- Prove2me | Definitions.Def_Frequency
-- name    : Frequency
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:57:32.362888+00:00
-- url     : https://prove2.me/theorems/d23cbc27-ddf8-4737-afe5-4e0b251bd6b3
-- title:
--   Frequency
-- statement:
--   Definitions and structural lemmas for Frequency, from Jason Davies (jasondavies/permutation-supersequence-length; see pinned Apache-2.0 LICENSE and README.md)'s pinned Shortest word containing every permutation of ten symbols as a subsequence development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jasondavies/permutation-supersequence-length/blob/cd48854bb301c66360ca31c4b7509b736111f8e9/Frequency.lean

import Std
set_option autoImplicit true
namespace Supersequence
open List
variable {α : Type}
def Covers (A : α → Prop) (w : List α) : Prop :=
  ∀ q : List α, q.Nodup → (∀ a ∈ q, A a) → q.Sublist w
variable [DecidableEq α]
def project (x : α) (w : List α) := w.filter (· != x)
def LowerOnOthers (x : α) (F : Nat) : Prop :=
  ∀ v : List α, x ∉ v → Covers (· ≠ x) v → F ≤ v.length
def runs (x : α) (gs : List (List α)) := gs.flatMap (· ++ [x])
def Universal {n : Nat} (w : List (Fin n)) : Prop :=
  ∀ p : List (Fin n), p.Perm (finRange n) → p.Sublist w
def skip (x : Fin 10) (a : Fin 9) : Fin 10 :=
  if a.val < x.val then ⟨a.val,by omega⟩ else ⟨a.val+1,by omega⟩
def close (x a : Fin 10) : Fin 9 :=
  ⟨(if a.val < x.val then a.val else a.val - 1) % 9, Nat.mod_lt _ (by decide)⟩
end Supersequence


