-- Prove2me | Definitions.Def_EventStructures_Family_Rollback
-- name    : EventStructures_Family_Rollback
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:53:00.058388+00:00
-- url     : https://prove2.me/theorems/ab7a7424-a563-4616-8bba-4aa8a2cae12e
-- title:
--   Rollback
-- statement:
--   Definitions and structural lemmas for Rollback, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
namespace Rollback
def isRollback (c : Conf F) (e : F.Event) (m : Conf F) : Prop :=
  m.1 ⊆ c.1 ∧ e ∉ m.1 ∧
  ∀ m' : Conf F, m'.1 ⊆ c.1 → e ∉ m'.1 → m.1 ⊆ m'.1 → m'.1 ⊆ m.1
def Rollbacks (c : Conf F) (e : F.Event) : Set (Conf F) :=
  {m | isRollback F c e m}
def RollbackCandidates (c : Conf F) (e : F.Event) : Set (Conf F) :=
  {m | m.1 ⊆ c.1 ∧ e ∉ m.1}
def rollbackSet (c : Conf F) (e : F.Event) : Set F.Event :=
  ⋃₀ {m | F.Config m ∧ m ⊆ c.val ∧ e ∉ m}
end Rollback


