-- Prove2me | Definitions.Def_EventStructures_Prime_Rollback
-- name    : EventStructures_Prime_Rollback
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:53:34.28473+00:00
-- url     : https://prove2.me/theorems/8269a821-e69b-4a66-bbed-c169de399024
-- title:
--   Rollback
-- statement:
--   Definitions and structural lemmas for Rollback, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Rollback
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
set_option autoImplicit true
variable {L : Type*} (es : PES L)
namespace Rollback
open Configuration ConfFamily
local infix:50 " ⊢ " => enables es
lemma rollback_future_isConf {c : Conf es} {e : es.Event} :
    isConf es (c.1 \ es.future e) := by
  constructor
  · intro e₁ e₂ h₁ h₂
    rcases h₁ with ⟨h₁c, _⟩
    rcases h₂ with ⟨h₂c, _⟩
    exact c.2.1 h₁c h₂c
  · intro x y hx hy
    rcases hx with ⟨hxc, hxf⟩
    refine ⟨c.2.2 hxc hy, ?_⟩
    intro hyf
    have hle : e ≤ x := le_trans hyf hy
    exact hxf hle
def rollbackFuture (c : Conf es) (e : es.Event) : Conf es :=
  ⟨c.1 \ es.future e, rollback_future_isConf (es := es) (c := c)⟩
end Rollback


