-- Prove2me | Definitions.Def_AutomataTheory_Automata_Concat
-- name    : AutomataTheory_Automata_Concat
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:12:27.270065+00:00
-- url     : https://prove2.me/theorems/9ae241d2-053a-4424-ae2e-aec4bad9d3d4
-- title:
--   Concat
-- statement:
--   Definitions and structural lemmas for Concat, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Concat.lean

import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
set_option autoImplicit true
open Function Set Filter Sum Stream'
open Classical
namespace Automata
section AutomataConcat
variable {A : Type}
def NA.Concat (M0 : NA A) (acc0 : Set M0.State) (M1 : NA A) : NA A where
  State := M0.State ⊕ M1.State
  init := inl '' M0.init
  next := fun s a ↦ match (s) with
    | inl s0 => inl '' (M0.next s0 a) ∪
                inr '' { s1' | (s0 ∈ acc0 ∧ ∃ s1 ∈ M1.init, s1' ∈ M1.next s1 a) }
    | inr s1 => inr '' (M1.next s1 a)
attribute [local instance_reducible] NA.Concat
variable {M0 M1 : NA A} {acc0 : Set M0.State}
end AutomataConcat
section AcceptedLangConcat
variable {A : Type} {M0 M1 : NA A} {acc0 : Set M0.State} {acc1 : Set M1.State}
end AcceptedLangConcat


