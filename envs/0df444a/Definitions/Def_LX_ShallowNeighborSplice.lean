-- Prove2me | Definitions.Def_LX_ShallowNeighborSplice
-- name    : LX_ShallowNeighborSplice
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:14:10.699824+00:00
-- url     : https://prove2.me/theorems/b6d0e46a-373b-4f85-abf0-7fa7b0f71cd5
-- title:
--   Adjacency and intervals relative to an ordered carrier
-- statement:
--   For a finite carrier $S$ of positions, two positions are rank adjacent when both belong to $S$, they are distinct, and no carrier position lies strictly between them in the ordinary order. Either orientation is allowed. A subset $T$ is a carrier interval when it is contained in $S$ and contains every carrier position strictly between any two of its members. Positions outside $S$ may occupy gaps. Empty and singleton subsets satisfy the interval condition. These notions express adjacency and convexity in the induced carrier order.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ShallowNeighborSplice.lean#L8-L17

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
import Definitions.Def_LX_ZeroGapComponentCounting
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
variable {n : ℕ}

/-- Adjacency in the ordered carrier, allowing either arrow direction. -/
def RankAdjacent (S : Finset (Fin n)) (x y : Fin n) : Prop :=
  x ∈ S ∧ y ∈ S ∧ x ≠ y ∧
    ∀ z ∈ S, ¬(min x.val y.val < z.val ∧ z.val < max x.val y.val)

/-- An interval relative to an ordered carrier; fixed ambient positions may
lie in its gaps. -/
def CarrierInterval (T S : Finset (Fin n)) : Prop :=
  T ⊆ S ∧ ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ S,
    min x.val y.val < z.val → z.val < max x.val y.val → z ∈ T















end LX.Core.ZeroGap


