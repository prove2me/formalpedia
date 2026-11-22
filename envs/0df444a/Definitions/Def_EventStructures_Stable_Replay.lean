-- Prove2me | Definitions.Def_EventStructures_Stable_Replay
-- name    : EventStructures_Stable_Replay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:54:07.986792+00:00
-- url     : https://prove2.me/theorems/08a8475e-8eaa-44f5-9dee-648fa8c55957
-- title:
--   Replay
-- statement:
--   Definitions and structural lemmas for Replay, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Replay.lean

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Replay
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
namespace Stable
def replaySet (F : ConfFamily L) (c l : Set F.Event) : Set F.Event :=
  ⋃ x ∈ l, hist F c x
variable {c l : Set F.Event} (hc : F.Config c) (hlc : l ⊆ c)
end Stable


