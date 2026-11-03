-- Prove2me | Definitions.Def_LX_ZeroGapEventGeometry
-- name    : LX_ZeroGapEventGeometry
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:06:37.662519+00:00
-- url     : https://prove2.me/theorems/a374bbb4-e187-48a2-a2b1-592072e210f5
-- title:
--   Endpoint events and their cyclic interiors
-- statement:
--   An endpoint event is an ordered pair of positions on a positive cycle. Associate to it the transposition of its endpoints, and rotate an event by adding the same residue to both endpoints. A position is inside an event when its forward distance from the first endpoint is strictly positive and strictly smaller than the distance to the second endpoint. A second event is outside the first when neither of its endpoints is inside. Endpoints themselves are excluded from the interior, and equal endpoints give an empty interior. These definitions describe cyclic event geometry without imposing an event ordering.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapEventGeometry.lean#L12-L20

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

/-! Directed open arcs and the geometric condition satisfied by the ordered
list of zero-gap exchanges. Later endpoints avoid each earlier open arc. -/
namespace LX.Core.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

abbrev Event (n : ℕ) := Fin n × Fin n

def eventSwap (e : Event n) : State n := Equiv.swap e.1 e.2

def rotateEvent (u : Fin n) (e : Event n) : Event n := (e.1+u,e.2+u)

def Inside (e : Event n) (i : Fin n) : Prop := 0 < distance e.1 i ∧ distance e.1 i < distance e.1 e.2

def LaterOutside (e f : Event n) : Prop := ¬Inside e f.1 ∧ ¬Inside e f.2














end LX.Core.ZeroGap


