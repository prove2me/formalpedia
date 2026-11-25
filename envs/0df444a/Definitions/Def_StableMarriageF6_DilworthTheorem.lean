-- Prove2me | Definitions.Def_StableMarriageF6_DilworthTheorem
-- name    : StableMarriageF6_DilworthTheorem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:30:15.804862+00:00
-- url     : https://prove2.me/theorems/67e59e82-7acb-43c6-a50c-8d095c5bbc4d
-- title:
--   Dilworth Theorem
-- statement:
--   Definitions and structural lemmas for Dilworth Theorem, from insammael (insammael/stable-marriage-f6; see pinned Apache-2.0 LICENSE and lean/third_party provenance)'s pinned Small rotation blocks and antichain bound for width-3 CI2 posets (Stable Marriage F6) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/lean/StableMarriageF6/DilworthTheorem.lean

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Antichain
import Mathlib.Tactic
set_option autoImplicit true
namespace DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
def IsChain (s : Set α) : Prop :=
  ∀ x y, x ∈ s → y ∈ s → x ≤ y ∨ y ≤ x
def IsAntichain (s : Set α) : Prop :=
  ∀ x y, x ∈ s → y ∈ s → x ≠ y → ¬(x ≤ y) ∧ ¬(y ≤ x)
def IsChainCover (S : Finset α) {k : ℕ} (C : Fin k → Finset α) : Prop :=
  (∀ i, IsChain (C i : Set α)) ∧
  (Finset.biUnion Finset.univ C = S) ∧
  (∀ i j, i ≠ j → Disjoint (C i) (C j))
def IsAntichainCover (S : Finset α) {k : ℕ} (A : Fin k → Finset α) : Prop :=
  (∀ i, IsAntichain (A i : Set α)) ∧
  (Finset.biUnion Finset.univ A = S) ∧
  (∀ i j, i ≠ j → Disjoint (A i) (A j))
noncomputable def lowerCone (S A : Finset α) : Finset α :=
  S.filter (fun x => ∃ a ∈ A, x ≤ a)
noncomputable def upperCone (S A : Finset α) : Finset α :=
  S.filter (fun x => ∃ a ∈ A, a ≤ x)
noncomputable def chainsEndingAt (S : Finset α) (x : α) : Finset (Finset α) :=
  S.powerset.filter (fun C => x ∈ C ∧ (∀ y ∈ C, y ≤ x) ∧ IsChain (C : Set α))
noncomputable def posetHeight (S : Finset α) (x : α) : ℕ :=
  (chainsEndingAt S x).sup Finset.card
end DilworthTheorem


