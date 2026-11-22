-- Prove2me | Definitions.Def_EventStructures_Family_Replay
-- name    : EventStructures_Family_Replay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:53:46.7118+00:00
-- url     : https://prove2.me/theorems/18685a4e-76f1-486e-831d-90342342b94c
-- title:
--   Replay
-- statement:
--   Definitions and structural lemmas for Replay, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Replay.lean

import Definitions.Def_EventStructures_Family_Log
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
namespace Replay
local infixl:50 " ⊨ " => Log.compatibleWithLog F R
def conf (σ : Computations F) : Conf F := σ.1
@[simp]
def isMinReplay (l : Set F.Event) (σ : Computations F) : Prop :=
  σ ⊨ l ∧ ∀ σ' : Computations F, σ' ⊨ l → (conf F σ).1 ⊆ (conf F σ').1
@[simp]
def isMaxReplay (l : Set F.Event) (σ : Computations F) : Prop :=
  σ ⊨ l ∧ ∀ σ' : Computations F, σ' ⊨ l → (conf F σ').1 ⊆ (conf F σ).1
def LabelEquivComputation (σ₁ σ₂ : Computations F) : Prop :=
  F.label '' (conf F σ₁).1 = F.label '' (conf F σ₂).1
@[simp]
def isMinLabelReplay (l : Set F.Event) (σ : Computations F) : Prop :=
  σ ⊨ l ∧ ∀ σ' : Computations F, σ' ⊨ l →
    F.label '' (conf F σ).1 ⊆ F.label '' (conf F σ').1
end Replay


