-- Prove2me | Definitions.Def_StableMarriageF6_F6ConvexWindow
-- name    : StableMarriageF6_F6ConvexWindow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:30:21.922831+00:00
-- url     : https://prove2.me/theorems/0d9d98c8-36e3-4efe-a113-ba490bd0b0ce
-- title:
--   F6 Convex Window
-- statement:
--   Definitions and structural lemmas for F6 Convex Window, from insammael (insammael/stable-marriage-f6; see pinned Apache-2.0 LICENSE and lean/third_party provenance)'s pinned Small rotation blocks and antichain bound for width-3 CI2 posets (Stable Marriage F6) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/lean/StableMarriageF6/F6ConvexWindow.lean

import Mathlib
set_option autoImplicit true
noncomputable section
namespace F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
def IncRel (x z : V) : Prop := ¬ x ≤ z ∧ ¬ z ≤ x
def Antichain (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≤ y → x = y
def Chain (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≤ y ∨ y ≤ x
def WidthLE (k : ℕ) : Prop := ∀ s : Finset V, Antichain s → s.card ≤ k
def Inc (x : V) : Finset V := by classical exact univ.filter (IncRel x)
def CI2 : Prop := ∀ x y : V, x < y →
  Chain (Inc x ∩ Inc y) ∧ (Inc x ∩ Inc y).card ≤ 2
def antichains : Finset (Finset V) := by classical exact univ.filter Antichain
def Ak (k : ℕ) : ℕ := by classical exact ((antichains (V := V)).filter (fun s => s.card = k)).card
def totalAntichains : ℕ := (antichains (V := V)).card
def ideal (s : Finset V) : Finset V := by
  classical
  exact univ.filter (fun x => ∃ y ∈ s, x ≤ y)
def Below (T : Finset V) (x : V) : Prop := 2 ≤ (T.filter (fun t => x < t)).card
def Above (T : Finset V) (x : V) : Prop := 2 ≤ (T.filter (fun t => t < x)).card
structure ChainDecomposition (k : ℕ) where
  color : V → Fin k
  chain_fiber : ∀ i, Chain (univ.filter (fun x => color x = i))
namespace ChainDecomposition
variable {k : ℕ} (d : ChainDecomposition (V := V) k)
def part (i : Fin k) : Finset V := univ.filter (fun x => d.color x = i)
end ChainDecomposition
end F6ConvexWindow


