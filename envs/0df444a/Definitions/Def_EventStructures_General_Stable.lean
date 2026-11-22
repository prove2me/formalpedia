-- Prove2me | Definitions.Def_EventStructures_General_Stable
-- name    : EventStructures_General_Stable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:37:15.496578+00:00
-- url     : https://prove2.me/theorems/ffaca08f-cc5e-4786-b631-e73bb2b18ea7
-- title:
--   Stable
-- statement:
--   Definitions and structural lemmas for Stable, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Stable.lean

import Definitions.Def_EventStructures_General_Basic
set_option autoImplicit true
structure SES (Label : Type*) extends GES Label where
  enable_inter : ∀ {X Y Z : Finset toGES.Event} {e}, enable X e → enable Y e →
    toGES.Consistent (↑X ∪ ↑Y ∪ {e}) → (↑Z : Set toGES.Event) = ↑X ∩ ↑Y → enable Z e
namespace SES
variable {L : Type*} (S : SES L)
local infix:50 " ⊢ " => S.enable
@[reducible] def toFamily : ConfFamily L := S.toGES.toFamily
variable {S}
end SES


