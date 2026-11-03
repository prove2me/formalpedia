-- Prove2me | Definitions.Def_LX_ZeroGapComponentCounting
-- name    : LX_ZeroGapComponentCounting
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:12:26.589487+00:00
-- url     : https://prove2.me/theorems/1c70fac0-9a97-479f-b291-bd74aa6d1686
-- title:
--   Events inside and outside a rooted component
-- statement:
--   For an event list on a positive cycle and a root, filter the list according to whether an event’s first endpoint is reachable from the root. The complementary filter gives outside events. Both preserve order and repeated occurrences. Separately, collect every endpoint appearing anywhere in the list into a finite set, removing repetitions. These constructions distinguish list multiplicity from vertex membership in event counting arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapComponentCounting.lean#L7-L54

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
import Definitions.Def_LX_ZeroGapComponentSize
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

namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

noncomputable def componentEvents (events : List (Event n)) (root : Fin n) : List (Event n) := by
  classical
  exact events.filter (fun e => decide (EventReaches events root e.1))

noncomputable def outsideEvents (events : List (Event n)) (root : Fin n) : List (Event n) := by
  classical
  exact events.filter (fun e => decide (¬EventReaches events root e.1))







def endpoints (events : List (Event n)) : Finset (Fin n) :=
  (events.flatMap (fun e => [e.1,e.2])).toFinset








end LX.Core.ZeroGap


