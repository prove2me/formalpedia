-- Prove2me | Definitions.Def_EventStructures_Family_LTSI
-- name    : EventStructures_Family_LTSI
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:36:25.855881+00:00
-- url     : https://prove2.me/theorems/de17e646-0400-4040-9799-b5192bf45480
-- title:
--   LTSI
-- statement:
--   Definitions and structural lemmas for LTSI, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/LTSI.lean

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_LTS_Basic
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
namespace ConfFamily
def esStep (c₁ : Conf F) (a : L) (c₂ : Conf F) : Prop :=
  ∃ e, F.enables c₁.val e ∧ e ∉ c₁.val ∧ F.label e = a ∧ c₂.val = c₁.val ∪ {e}
def esIndep (c : Conf F) (a : L) (c₁ : Conf F) (b : L) (c₂ : Conf F) : Prop :=
  ∃ e₁ e₂, F.Indep c.val e₁ e₂ ∧ e₁ ∉ c.val ∧ e₂ ∉ c.val ∧
    F.label e₁ = a ∧ F.label e₂ = b ∧
    c₁.val = c.val ∪ {e₁} ∧ c₂.val = c.val ∪ {e₂}
def toLTSI : LTSI L where
  State := Conf F
  init := ConfFamily.empty F
  step := esStep F
  indep := esIndep F
end ConfFamily


