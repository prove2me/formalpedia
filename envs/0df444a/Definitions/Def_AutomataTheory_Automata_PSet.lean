-- Prove2me | Definitions.Def_AutomataTheory_Automata_PSet
-- name    : AutomataTheory_Automata_PSet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:13:18.460038+00:00
-- url     : https://prove2.me/theorems/9d3b61cd-f232-48c0-ae28-aae42c3b7dff
-- title:
--   PSet
-- statement:
--   Definitions and structural lemmas for PSet, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/PSet.lean

import Definitions.Def_AutomataTheory_Automata_Det
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
namespace Automata
section AutomataPSet
variable {A : Type}
def NA.PSet (M : NA A) : DA A where
  State := Set M.State
  init := M.init
  next := fun ps a ↦ ⋃ s ∈ ps, M.next s a
attribute [local instance_reducible] NA.PSet
variable {M : NA A}
instance : Membership M.State M.PSet.State := by exact { mem := fun s ↦ s }
end AutomataPSet
attribute [local instance_reducible] NA.PSet
section AcceptedLangPSet
variable {A : Type} (M : NA A) (acc : Set M.State)
def NA.PSet_Acc : Set (Set M.State) := { sset | ∃ s ∈ sset, s ∈ acc }
end AcceptedLangPSet


