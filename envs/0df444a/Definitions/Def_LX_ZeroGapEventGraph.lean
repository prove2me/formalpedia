-- Prove2me | Definitions.Def_LX_ZeroGapEventGraph
-- name    : LX_ZeroGapEventGraph
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:07:38.866076+00:00
-- url     : https://prove2.me/theorems/847653b5-b5c0-4aad-a623-b17f3170a913
-- title:
--   Reachability and components of endpoint events
-- statement:
--   Given a list of endpoint events on a positive cycle, join positions whenever they are the two endpoints of some listed event, allowing either order. Reachability is the reflexive transitive closure of this symmetric relation. The component of a root is the finite set of positions reachable from it, including the root itself even when no events occur. Repeated events do not change the relation, and an event with equal endpoints is permitted. This interface connects event lists to finite component arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapEventGraph.lean#L10-L74

/-
Adapted from https://github.com/snow-ghost/glushkov-lx-lean at 8cddcd222b591673dc63475d9d45b9ed5c6eb92c.
MIT License

Copyright (c) 2026 S. Uskov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Mathlib
import Definitions.Def_LX_AffineCrossings
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PortRoute
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapExchange
import Definitions.Def_LX_ZeroGapPair

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

/-! Connected components of the event graph contain the cycles of the
original permutation and are invariant under it. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def EventEdge (events : List (Event n)) (i j : Fin n) : Prop :=
  ∃ e ∈ events, (i=e.1 ∧ j=e.2) ∨ (i=e.2 ∧ j=e.1)

abbrev EventReaches (events : List (Event n)) := Relation.ReflTransGen (EventEdge events)

theorem event_edge_symm (events : List (Event n)) {i j : Fin n} (h : EventEdge events i j) :
    EventEdge events j i := by
  obtain ⟨e,he,h⟩ := h
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨e,he,Or.inr ⟨rfl,rfl⟩⟩
  · exact ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩











noncomputable def eventComponent (events : List (Event n)) (root : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (EventReaches events root)

@[simp] theorem mem_eventComponent (events : List (Event n)) (root i : Fin n) :
    i ∈ eventComponent events root ↔ EventReaches events root i := by
  classical
  simp [eventComponent]



end LX.Core.ZeroGap


