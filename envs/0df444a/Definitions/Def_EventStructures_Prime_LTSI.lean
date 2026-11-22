-- Prove2me | Definitions.Def_EventStructures_Prime_LTSI
-- name    : EventStructures_Prime_LTSI
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:39:52.989533+00:00
-- url     : https://prove2.me/theorems/6cbe19e5-74d3-4b5b-b421-d72c17d5aecd
-- title:
--   LTSI
-- statement:
--   Definitions and structural lemmas for LTSI, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/LTSI.lean

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Stable_LTSI
import Definitions.Def_EventStructures_Family_LTSI
set_option autoImplicit true
variable {L : Type*}
namespace PES
variable (es : PES L)
open Configuration
local infix:50 " ⊢ " => enables es
local infixl:50 " ⋈ " => es.concurrent
def emptyConfig : Conf es :=
  ⟨∅, fun h _ _ => (Set.notMem_empty _ h).elim,
      fun h _ => (Set.notMem_empty _ h).elim⟩
def esStep (c₁ : Conf es) (a : L) (c₂ : Conf es) : Prop :=
  ∃ e, (c₁.1 ⊢ e) ∧ e ∉ c₁.1 ∧ es.label e = a ∧ c₂.1 = c₁.1 ∪ {e}
def esIndep (c : Conf es) (a : L) (c₁ : Conf es) (b : L) (c₂ : Conf es) : Prop :=
  ∃ e₁ e₂, (c.1 ⊢ e₁) ∧ (c.1 ⊢ e₂) ∧ e₁ ∉ c.1 ∧ e₂ ∉ c.1 ∧
    es.label e₁ = a ∧ es.label e₂ = b ∧
    c₁.1 = c.1 ∪ {e₁} ∧ c₂.1 = c.1 ∪ {e₂} ∧ e₁ ⋈ e₂
def toLTSI : LTSI L where
  State := Conf es
  init := emptyConfig es
  step := esStep es
  indep := esIndep es
def esRStep : Conf es → DirLabel L → Conf es → Prop :=
  ConfFamily.esRStep es.toFamily
def esRIndep : Conf es → DirLabel L → Conf es → DirLabel L → Conf es → Prop :=
  ConfFamily.esRIndep es.toFamily
def toRLTSI : RLTSI L :=
  ConfFamily.toRLTSI es.toFamily
end PES


