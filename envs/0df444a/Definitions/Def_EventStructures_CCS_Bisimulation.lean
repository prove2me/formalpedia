-- Prove2me | Definitions.Def_EventStructures_CCS_Bisimulation
-- name    : EventStructures_CCS_Bisimulation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:53:49.323287+00:00
-- url     : https://prove2.me/theorems/c18debd7-730a-49f2-aa69-fae5142231be
-- title:
--   Bisimulation
-- statement:
--   Definitions and structural lemmas for Bisimulation, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
set_option autoImplicit true
open CCS ConfFamily
namespace CCS
universe u
variable {Name : Type u}
open scoped Classical in
/-- The process remaining after a configuration has fired. -/
noncomputable def resid : ∀ {Name : Type u}, (P : Process Name) →
    Set (semantics P).Event → Process Name
  | _, .nil, _ => .nil
  | _, .pre α P, c => if none ∈ c then resid P {e | some e ∈ c} else .pre α P
  | _, .sum P Q, c =>
      if ∃ e, Sum.inl e ∈ c then resid P {e | Sum.inl e ∈ c}
      else if ∃ f, Sum.inr f ∈ c then resid Q {f | Sum.inr f ∈ c}
      else .sum P Q
  | _, .par P Q, c => .par (resid P (projL c)) (resid Q (projR c))
  | _, .res P, c => .res (resid P (unres c))
end CCS


