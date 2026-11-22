-- Prove2me | Definitions.Def_EventStructures_Prime_Replay
-- name    : EventStructures_Prime_Replay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:54:33.370833+00:00
-- url     : https://prove2.me/theorems/a6a4a43e-e09c-453d-88a2-df63b11ba90f
-- title:
--   Replay
-- statement:
--   Definitions and structural lemmas for Replay, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Replay.lean

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Prime_Log
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
open Log
local infixl:50 " ⊨ " => PES.compatibleWithLog es
namespace Replay
def downset (e : es.Event) : Set es.Event :=
  {x | x ≤ e}
local infixl:50 " ## " => es.minimalConflict
local infixl:50 " # " => es.conflict
def minReplaySet (l : Set es.Event) : Set es.Event :=
  ⋃ e ∈ l, downset es e
def maxReplaySet (l : Set es.Event) : Set es.Event :=
  minReplaySet es l ∪ {e : es.Event | ∀ e₁ e₂ : es.Event, e₁ ## e₂ ∧ e₁ ≤ e → e₁ ∈ l}
end Replay


