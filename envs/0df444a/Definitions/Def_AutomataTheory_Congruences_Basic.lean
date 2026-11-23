-- Prove2me | Definitions.Def_AutomataTheory_Congruences_Basic
-- name    : AutomataTheory_Congruences_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:12:47.817798+00:00
-- url     : https://prove2.me/theorems/0c3cea0b-cdf1-4730-b639-7d20ee5ceac5
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/Basic.lean

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
set_option autoImplicit true
open Function Set Stream'
section Congruences
open Classical
class Congruence (A : Type) extends eq : Setoid (List A) where
  right_congr : ∀ u v, eq u v → ∀ w, eq (u ++ w) (v ++ w)
variable {A : Type}
def Congruence.QuotType (c : Congruence A) := Quotient c.eq
def Congruence.EqvCls (c : Congruence A) (s : c.QuotType) : Set (List A) :=
  (Quotient.mk c.eq) ⁻¹' {s}
def Congruence.ConcatOmegaLang (c : Congruence A) (s t : c.QuotType) : Set (Stream' A) :=
  (c.EqvCls s) * (c.EqvCls t)^ω
def Congruence.Saturates (c : Congruence A) (L : Set (Stream' A)) :=
  ∀ s t : c.QuotType, (c.ConcatOmegaLang s t ∩ L).Nonempty → c.ConcatOmegaLang s t ⊆ L
def Congruence.Ample (c : Congruence A) :=
  ∀ as, ∃ s t : c.QuotType, as ∈ c.ConcatOmegaLang s t
variable {c : Congruence A}
end Congruences


