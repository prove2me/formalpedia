-- Prove2me | Definitions.Def_AutomataTheory_Sequences_InfOcc
-- name    : AutomataTheory_Sequences_InfOcc
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:11:10.213864+00:00
-- url     : https://prove2.me/theorems/a21479f0-966c-4a36-9608-e05905b286e3
-- title:
--   Inf Occ
-- statement:
--   Definitions and structural lemmas for Inf Occ, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean

import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
section InfOcc
def InfOcc {X : Type*} (xs : Stream' X) : Set X :=
  { x | ∃ᶠ k in atTop, xs k = x }
instance {X : Type*} [Finite X] : Finite (Option X) :=
  have := Fintype.ofFinite X
  Finite.of_fintype _
end InfOcc


