-- Prove2me | Definitions.Def_AutomataTheory_Sequences_Temporal
-- name    : AutomataTheory_Sequences_Temporal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:11:06.653793+00:00
-- url     : https://prove2.me/theorems/80d5e4e3-ea18-45ec-83b3-37a546a8b4e3
-- title:
--   Temporal
-- statement:
--   Definitions and structural lemmas for Temporal, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Temporal.lean

import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Filter Stream'
section Temporal
def Step {X : Type*} (xs : Stream' X) (p q : Set X) : Prop :=
  ∀ k, xs k ∈ p → xs (k + 1) ∈ q
def LeadsTo {X : Type*} (xs : Stream' X) (p q : Set X) : Prop :=
  ∀ k, xs k ∈ p → ∃ k' ≥ k, xs k' ∈ q
variable {X : Type*} {xs : Stream' X}
end Temporal


