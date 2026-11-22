-- Prove2me | Definitions.Def_EventStructures_Family_Reachability
-- name    : EventStructures_Family_Reachability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:52:19.87909+00:00
-- url     : https://prove2.me/theorems/e10be32c-7386-4a03-8b1c-058253e06db4
-- title:
--   Reachability
-- statement:
--   Definitions and structural lemmas for Reachability, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Reachability.lean

import Definitions.Def_EventStructures_Family_Path
import Mathlib.Data.Set.Card
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)


