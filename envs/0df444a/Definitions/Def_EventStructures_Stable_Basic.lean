-- Prove2me | Definitions.Def_EventStructures_Stable_Basic
-- name    : EventStructures_Stable_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:38:06.782449+00:00
-- url     : https://prove2.me/theorems/dfb668c1-c2ed-4128-b115-bf0ee31d4ed9
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Basic.lean

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_General_Stable
import Mathlib.Data.Set.Lattice
set_option autoImplicit true
open ConfFamily
variable {L : Type*}
def Stable (F : ConfFamily L) : Prop :=
  ∀ {S : Set (Set F.Event)} {z : Set F.Event}, S.Nonempty → (∀ x ∈ S, F.Config x) →
    F.Config z → (∀ x ∈ S, x ⊆ z) → F.Config (⋂₀ S)
def Coherent (F : ConfFamily L) : Prop :=
  ∀ {S : Set (Set F.Event)} {z : Set F.Event}, (∀ x ∈ S, F.Config x) →
    F.Config z → (∀ x ∈ S, x ⊆ z) → F.Config (⋃₀ S)
namespace Stable
variable {F : ConfFamily L}
def hist (F : ConfFamily L) (c : Set F.Event) (x : F.Event) : Set F.Event :=
  ⋂₀ {m | F.Config m ∧ m ⊆ c ∧ x ∈ m}
variable {c : Set F.Event} {x : F.Event}
end Stable


