-- Prove2me | Definitions.Def_EventStructures_Stable_LTSI
-- name    : EventStructures_Stable_LTSI
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:38:47.242795+00:00
-- url     : https://prove2.me/theorems/0bf96cd8-1ae8-4aa9-bf3d-5fa05ffb0fde
-- title:
--   LTSI
-- statement:
--   Definitions and structural lemmas for LTSI, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/LTSI.lean

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_LTSI
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
namespace ConfFamily
def esRStep : Conf F → DirLabel L → Conf F → Prop
  | c₁, DirLabel.fwd a, c₂ => esStep F c₁ a c₂
  | c₁, DirLabel.bwd a, c₂ => esStep F c₂ a c₁
def esRIndep : Conf F → DirLabel L → Conf F → DirLabel L → Conf F → Prop
  | c, DirLabel.fwd a, c₁, DirLabel.fwd b, c₂ => esIndep F c a c₁ b c₂
  | _, DirLabel.fwd _, _, DirLabel.bwd _, _ => False
  | _, DirLabel.bwd _, _, DirLabel.fwd _, _ => False
  | c, DirLabel.bwd a, c₁, DirLabel.bwd b, c₂ =>
      ∃ e₁ e₂, e₁ ≠ e₂ ∧ e₁ ∈ c.val ∧ e₂ ∈ c.val ∧
        F.label e₁ = a ∧ F.label e₂ = b ∧
        F.Config (c.val \ {e₁}) ∧ F.Config (c.val \ {e₂}) ∧
        c₁.val = c.val \ {e₁} ∧ c₂.val = c.val \ {e₂}
def toRLTSI : RLTSI L where
  State := Conf F
  init := ConfFamily.empty F
  step := esRStep F
  indep := esRIndep F
  step_rev := Iff.rfl
variable {F}
end ConfFamily


