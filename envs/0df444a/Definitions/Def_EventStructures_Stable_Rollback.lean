-- Prove2me | Definitions.Def_EventStructures_Stable_Rollback
-- name    : EventStructures_Stable_Rollback
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:53:41.281563+00:00
-- url     : https://prove2.me/theorems/933b2f5b-4397-45b3-8fc7-840ead7eb284
-- title:
--   Rollback
-- statement:
--   Definitions and structural lemmas for Rollback, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Rollback.lean

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Rollback
set_option autoImplicit true
open ConfFamily Rollback
variable {L : Type*} {F : ConfFamily L}
namespace Stable
lemma rollbackSet_config (hF : Coherent F) (c : Conf F) (e : F.Event) :
    F.Config (rollbackSet F c e) :=
  hF (fun _ hm => hm.1) c.2 (fun _ hm => hm.2.1)
def rollbackConf (hF : Coherent F) (c : Conf F) (e : F.Event) : Conf F :=
  ⟨rollbackSet F c e, rollbackSet_config hF c e⟩
end Stable


