-- Prove2me | Definitions.Def_EventStructures_Prime_Log
-- name    : EventStructures_Prime_Log
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:53:51.565085+00:00
-- url     : https://prove2.me/theorems/8d99f90b-1e9f-4c5a-8100-66a09aa3c340
-- title:
--   Log
-- statement:
--   Definitions and structural lemmas for Log, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Log
import Theorems.Thm_PES_enables_iff
import Theorems.Thm_PES_toFamily_Config
import Theorems.Thm_PES_toFamily_Event
attribute [local simp] PES.enables_iff
attribute [local simp] PES.toFamily_Config
attribute [local simp] PES.toFamily_Event


set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
local infixl:50 " ## " => es.minimalConflict
@[simp]
def logged (e : es.Event) : Prop := ∃ e', e ## e'
@[simp]
def log (c : Conf es) : Set es.Event :=
  {e ∈ c.1 | ∃ e' ∉ c.1, e ## e'}
namespace Log
end Log
namespace PES
abbrev compatibleWithLog (σ : Computations es.toFamily) (l : Set es.Event) : Prop :=
  Log.compatibleWithLog es.toFamily es.conflict σ l
def compatibleWithConfigLog (c : Conf es) (σ : Computations es.toFamily) : Prop :=
  compatibleWithLog es σ (log es c)
def CompatibleWithConfigLog (c : Conf es) : Type _ :=
  Log.CompatibleComputations es.toFamily es.conflict (log es c)
@[simp] def labelLog (c : Conf es) : Set L := Log.labelLog es.toFamily (log es c)
end PES


