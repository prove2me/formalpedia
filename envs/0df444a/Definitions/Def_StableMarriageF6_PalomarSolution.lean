-- Prove2me | Definitions.Def_StableMarriageF6_PalomarSolution
-- name    : StableMarriageF6_PalomarSolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:31:50.211658+00:00
-- url     : https://prove2.me/theorems/1ed0cc95-44e7-5d1d-a378-f8de0e77c49f
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from insammael (insammael/stable-marriage-f6; see pinned Apache-2.0 LICENSE and lean/third_party provenance)'s pinned Small rotation blocks and antichain bound for width-3 CI2 posets (Stable Marriage F6) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/palomar/Solution.lean

import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
namespace StableMarriageF6Public
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [PartialOrder V]
def incomparability (x z : V) : Prop := ¬ x ≤ z ∧ ¬ z ≤ x
def antichain (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≤ y → x = y
def chain (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≤ y ∨ y ≤ x
def widthLE (k : ℕ) : Prop :=
  ∀ s : Finset V, antichain s → s.card ≤ k
def inc (x : V) : Finset V := by
  classical
  exact univ.filter (incomparability x)
def ci2 : Prop :=
  ∀ x y : V, x < y → chain (inc x ∩ inc y) ∧ (inc x ∩ inc y).card ≤ 2
def antichains : Finset (Finset V) := by
  classical
  exact univ.filter (antichain (V := V))
def totalNumberOfAntichains : ℕ := (antichains (V := V)).card
end StableMarriageF6Public


