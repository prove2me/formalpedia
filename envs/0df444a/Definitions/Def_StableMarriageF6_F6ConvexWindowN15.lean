-- Prove2me | Definitions.Def_StableMarriageF6_F6ConvexWindowN15
-- name    : StableMarriageF6_F6ConvexWindowN15
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:31:24.52986+00:00
-- url     : https://prove2.me/theorems/4e5a77b1-95ab-5b73-b536-1dd1951321df
-- title:
--   F6 Convex Window N15
-- statement:
--   Definitions and structural lemmas for F6 Convex Window N15, from insammael (insammael/stable-marriage-f6; see pinned Apache-2.0 LICENSE and lean/third_party provenance)'s pinned Small rotation blocks and antichain bound for width-3 CI2 posets (Stable Marriage F6) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/lean/StableMarriageF6/F6ConvexWindowN15.lean

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
set_option autoImplicit true
noncomputable section
namespace F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
def IsTriple (T : Finset V) : Prop := Antichain T ∧ T.card = 3
def tripleFamily : Finset (Finset V) :=
  (antichains (V := V)).filter (fun T => T.card = 3)
def tripleUnion (F : Finset (Finset V)) : Finset V := F.biUnion id
def inducedPairs (U : Finset V) : Finset (Finset V) :=
  (U.powersetCard 2).filter Antichain
def pairCount (U : Finset V) : ℕ := (inducedPairs U).card
def crossPairs (U W : Finset V) : Finset (Finset V) :=
  U.biUnion (fun x => (W.filter (IncRel x)).image (fun y => {x, y}))
def crossCount (U W : Finset V) : ℕ := ∑ x ∈ U, (W.filter (IncRel x)).card
def lastTriple (F : Finset (Finset V)) (hn : F.Nonempty) : Finset V :=
  Classical.choose (exists_max_image F (fun T => (ideal T).card) hn)
theorem lastTriple_mem (F : Finset (Finset V)) (hn : F.Nonempty) : lastTriple F hn ∈ F :=
  (Classical.choose_spec (exists_max_image F (fun T => (ideal T).card) hn)).1
def triplesDescending (F : Finset (Finset V)) : List (Finset V) :=
  if hn : F.Nonempty then
    lastTriple F hn :: triplesDescending (F.erase (lastTriple F hn))
  else []
termination_by F.card
decreasing_by exact card_lt_card (erase_ssubset (lastTriple_mem F hn))
def emptyTransitions (F : Finset (Finset V)) : ℕ :=
  if hn : F.Nonempty then
    emptyTransitions (F.erase (lastTriple F hn)) +
      if (F.erase (lastTriple F hn)).Nonempty ∧
        Disjoint (tripleUnion (F.erase (lastTriple F hn))) (lastTriple F hn) then 1 else 0
  else 0
termination_by F.card
decreasing_by exact card_lt_card (erase_ssubset (lastTriple_mem F hn))
end F6ConvexWindow


