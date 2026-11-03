-- Prove2me | Definitions.Def_LX_ZeroGapComponentSize
-- name    : LX_ZeroGapComponentSize
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:11:00.173206+00:00
-- url     : https://prove2.me/theorems/fe3777c9-1316-4c40-8639-16f74d56cbf0
-- title:
--   Simple graph on a rooted event component
-- statement:
--   For a list of events on a positive cycle and a root, form a simple graph whose vertices are positions in the root’s event component. Distinct component vertices are adjacent precisely when a listed event joins them in either order. Equal endpoints do not create graph loops. The root itself is supplied as a distinguished vertex using reflexive reachability. This graph translates the event component into the finite simple graph setting.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapComponentSize.lean#L9-L17

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
import Definitions.Def_LX_ZeroGapEventGraph
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

/-! Every connected component of the event graph uses at least one fewer
exchange events than its number of vertices. -/
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

noncomputable def componentGraph (events : List (Event n)) (root : Fin n) :
    SimpleGraph {i : Fin n // i ∈ eventComponent events root} where
  Adj i j := i ≠ j ∧ EventEdge events i.val j.val
  symm := by constructor; intro i j h; exact ⟨Ne.symm h.1,event_edge_symm events h.2⟩
  loopless := by constructor; intro i h; exact h.1 rfl

noncomputable def rootVertex (events : List (Event n)) (root : Fin n) :
    {i : Fin n // i ∈ eventComponent events root} :=
  ⟨root,(mem_eventComponent events root root).mpr Relation.ReflTransGen.refl⟩









end LX.Core.ZeroGap


