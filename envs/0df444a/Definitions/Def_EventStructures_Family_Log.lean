-- Prove2me | Definitions.Def_EventStructures_Family_Log
-- name    : EventStructures_Family_Log
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:53:13.934076+00:00
-- url     : https://prove2.me/theorems/348cd5fa-7fb0-47ec-a7ff-10df03df2af8
-- title:
--   Log
-- statement:
--   Definitions and structural lemmas for Log, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Log.lean

import Definitions.Def_EventStructures_Family_Computation
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
namespace Log
@[simp]
def compatibleWithLog (σ : Computations F) (l : Set F.Event) : Prop :=
  (∀ e ∈ l, e ∈ σ.1.1) ∧
  (∀ e ∈ σ.1.1, ∀ e' ∈ l, ¬ R e e') ∧
  (∀ e ∈ σ.1.1, ∀ e' : F.Event, R e e' → e ∈ l)
local infixl:50 " ⊨ " => compatibleWithLog F R
def CompatibleComputations (l : Set F.Event) : Type _ :=
  {σ : Computations F // σ ⊨ l}
def CompatibleComputations.val {l : Set F.Event} (σ : CompatibleComputations F R l) :
    Computations F := σ.1
@[simp] def labelLog (l : Set F.Event) : Set L := F.label '' l
end Log


