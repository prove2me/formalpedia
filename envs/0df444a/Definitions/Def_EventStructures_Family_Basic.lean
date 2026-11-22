-- Prove2me | Definitions.Def_EventStructures_Family_Basic
-- name    : EventStructures_Family_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:35:46.399895+00:00
-- url     : https://prove2.me/theorems/1ac7fa1e-1faf-4db1-a173-7b102bfb909c
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Basic.lean

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Basic
set_option autoImplicit true
structure ConfFamily (Label : Type*) where
  Event : Type*
  Config : Set Event → Prop
  label : Event → Label
  empty_mem : Config ∅
  /-- A finite gap between configurations closes one event at a time. -/
  secured : ∀ {x y : Set Event}, Config x → Config y → y ⊆ x → (x \ y).Finite → x ≠ y →
    ∃ e ∈ x \ y, Config (x \ {e})
namespace ConfFamily
variable {L : Type*} (F : ConfFamily L)
def Conf : Type _ := {X : Set F.Event // F.Config X}
def FinConf : Type _ := {X : Finset F.Event // F.Config (X : Set F.Event)}
def empty : Conf F := ⟨∅, F.empty_mem⟩
def enables (c : Set F.Event) (e : F.Event) : Prop := F.Config c ∧ F.Config (c ∪ {e})
variable {F}
variable (F)
def Indep (c : Set F.Event) (e₁ e₂ : F.Event) : Prop :=
  e₁ ≠ e₂ ∧ F.enables c e₁ ∧ F.enables c e₂ ∧ F.Config (c ∪ {e₁} ∪ {e₂})
variable {F}
variable (F)
def compat (e₁ e₂ : F.Event) : Prop := ∃ c, F.Config c ∧ e₁ ∈ c ∧ e₂ ∈ c
end ConfFamily


