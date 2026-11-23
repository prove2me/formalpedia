-- Prove2me | Definitions.Def_AutomataTheory_Automata_Sum
-- name    : AutomataTheory_Automata_Sum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:11:26.270133+00:00
-- url     : https://prove2.me/theorems/baca41d2-00b6-4c99-bbab-bb3ec6e01d7d
-- title:
--   Sum
-- statement:
--   Definitions and structural lemmas for Sum, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Sum.lean

import Definitions.Def_AutomataTheory_Automata_Basic
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
namespace Automata
section AutomataSum
variable {I A : Type}
def NA.Sum (M : I → NA A) : NA A where
  State := Σ i : I, (M i).State
  init := ⋃ i : I, Sigma.mk i '' (M i).init
  next := fun ⟨i, s⟩ a ↦ Sigma.mk i '' (M i).next s a
attribute [local instance_reducible] NA.Sum
variable {M : I → NA A}
end AutomataSum
attribute [local instance_reducible] NA.Sum
section AcceptedLangUnion
variable {I A : Type} (M : I → NA A) (acc : (i : I) → Set ((M i).State))
def NA.Sum_Acc : Set (NA.Sum M).State := ⋃ i : I, Sigma.mk i '' acc i
end  AcceptedLangUnion


