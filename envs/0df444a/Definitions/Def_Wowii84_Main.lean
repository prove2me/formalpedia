-- Prove2me | Definitions.Def_Wowii84_Main
-- name    : Wowii84_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:22:57.613821+00:00
-- url     : https://prove2.me/theorems/c15874e4-2a43-403b-b06c-8cea43eb74a4
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from ProblemHunter/wowii84-lean contributors and Formal Conjectures Authors (see pinned Apache-2.0 LICENSE and source headers)'s pinned Written on the Wall II Conjecture 84 on largest induced trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
set_option autoImplicit false
@[expose] public section
public section
@[expose] section
namespace WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
def cutSide (G : SimpleGraph α) (c : α) (a : ↥({c}ᶜ : Set α)) : Set α :=
  {z | z = c ∨ ∃ hz : z ≠ c, (G.induce ({c}ᶜ : Set α)).Reachable
    a ⟨z, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz⟩}
structure PendantGeodesics (G : SimpleGraph α) (K : Finset α) where
  endPoint : ↥(K : Set α) → α
  path : ∀ c : ↥(K : Set α), G.Walk c (endPoint c)
  geodesic : ∀ c, (path c).length = G.dist c (endPoint c)
  core_inter : ∀ c z, z ∈ (path c).support → z ∈ K → z = (c : α)
  closed : ∀ c z, z ∈ (path c).support → z ≠ (c : α) →
    ∀ w, G.Adj z w → w ∈ (path c).support
  rest : ∀ (c : ↥(K : Set α)) (z : ↥({(c : α)}ᶜ : Set α)),
    (z : α) ∉ (path c).support → ∀ (v : α) (hv : v ∈ K) (hvc : v ≠ (c : α)),
      (G.induce ({(c : α)}ᶜ : Set α)).Reachable z ⟨v, by simpa using hvc⟩
  depth_gap : ∀ c, 0 < (path c).length → ∃ a, (path c).length + 2 ≤ G.dist c a
  cover : ∀ z : α, ∃ c, z ∈ (path c).support
namespace PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)
def DeletionCenters (G : SimpleGraph α) : Prop :=
  ∀ x, (G.induce ({x}ᶜ : Set α)).Connected →
    (∃ y, ¬ ((G.induce ({x}ᶜ : Set α)).induce
      ({y}ᶜ : Set ↥({x}ᶜ : Set α))).Connected) →
    ∃ c : α, c ≠ x ∧ G.eccent c = G.radius ∧ G.dist c x = G.radius.toNat ∧
      ∀ z : α, z ≠ x → G.dist c z ≤ G.radius.toNat - 1
end PendantGeodesics
end WrittenOnTheWallII.GraphConjecture84


