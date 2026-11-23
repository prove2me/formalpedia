-- Prove2me | Definitions.Def_AutomataTheory_Automata_Loop
-- name    : AutomataTheory_Automata_Loop
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:12:30.058188+00:00
-- url     : https://prove2.me/theorems/327fdb99-581b-4b7c-9ccb-d0640be1c1f0
-- title:
--   Loop
-- statement:
--   Definitions and structural lemmas for Loop, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Loop.lean

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set Sum Filter Stream'
open Classical
open scoped Computability
attribute [local instance_reducible] Stream'
namespace Automata
section AutomataLoop
variable {A : Type}
def NA.Loop (M : NA A) (acc : Set M.State) : NA A where
  State := Unit ⊕ M.State
  init := {inl ()}
  next := fun s a ↦ match (s) with
    | inl () => inr '' { s' | ∃ s0 ∈ M.init, s' ∈ M.next s0 a } ∪
                if ∃ s0 ∈ M.init, ∃ s' ∈ acc, s' ∈ M.next s0 a then {inl ()} else ∅
    | inr s  => inr '' (M.next s a) ∪
                if ∃ s' ∈ acc, s' ∈ M.next s a then {inl ()} else ∅
attribute [local instance_reducible] NA.Loop
variable {M : NA A} {acc : Set M.State}
end AutomataLoop
attribute [local instance_reducible] NA.Loop
section AcceptedLangLoop
variable {A : Type} {M : NA A} {acc : Set M.State}
end AcceptedLangLoop


