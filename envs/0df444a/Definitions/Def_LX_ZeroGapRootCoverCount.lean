-- Prove2me | Definitions.Def_LX_ZeroGapRootCoverCount
-- name    : LX_ZeroGapRootCoverCount
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:12:04.577934+00:00
-- url     : https://prove2.me/theorems/bd5b9cb1-5550-4799-9527-4df81cca268f
-- title:
--   Adding an auxiliary root to an event list
-- statement:
--   For events on $n$ positive cyclic positions, lift each endpoint $i$ to $i+1$ in a set of $n+1$ positions, leaving the new position zero unused by the lifted original events. Given a list of roots, append one event from zero to each lifted root. The original event order is preserved, and repeated roots create repeated appended events. This construction encodes a collection of roots using one auxiliary vertex for subsequent component counting.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapRootCoverCount.lean#L9-L12

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

/-! If a list of roots meets every event component, the number of vertices
is at most the number of exchange events plus the number of roots. -/
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

def liftEvent (e : Event n) : Event (n+1) := (e.1.succ,e.2.succ)

def rootedEvents (events : List (Event n)) (roots : List (Fin n)) : List (Event (n+1)) :=
  events.map liftEvent ++ roots.map (fun r => (0,r.succ))








end LX.Core.ZeroGap


