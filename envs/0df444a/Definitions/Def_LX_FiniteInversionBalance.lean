-- Prove2me | Definitions.Def_LX_FiniteInversionBalance
-- name    : LX_FiniteInversionBalance
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:21:25.516238+00:00
-- url     : https://prove2.me/theorems/aab9f662-7cb3-4ea0-87f8-9bb0170ef0cb
-- title:
--   Integer indicators for inversions and leftward motion
-- statement:
--   For a permutation $p$ of $n$ positions, define an integer indicator of an inversion at $(i,j)$ to equal one precisely when $i<j$ and $p(j)<p(i)$. Define a second integer indicator at $i$ to equal one precisely when $p(i)<i$. Both are zero otherwise. These comparisons concern the ordinary finite order, so the second indicator records leftward displacement rather than adjacent descents. Integer values permit subtraction and signed summation in inversion balance formulas, including when $n=0$.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FiniteInversionBalance.lean#L8-L46

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
import Definitions.Def_LX_AffineDeletion
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_BufferProgram
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionIndices
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PortRoute
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ZeroGapComponentSize
import Definitions.Def_LX_ZeroGapCycleRoots
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Definitions.Def_LX_ZeroGapEventTravel
import Definitions.Def_LX_ZeroGapExchange
import Definitions.Def_LX_ZeroGapInversionSum
import Definitions.Def_LX_ZeroGapInversionTerms
import Definitions.Def_LX_ZeroGapPair
import Definitions.Def_LX_ZeroGapRootCoverCount
import Definitions.Def_LX_ZeroGapSorting

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteGaps
end LX.Core.FiniteGaps
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Integer indicator of an ordinary inversion. -/
def inversionIndicator (p : State n) (i j : Fin n) : ℤ :=
  if i.val < j.val ∧ (p j).val < (p i).val then 1 else 0







/-- Indicator of a position whose image lies to its left. -/
def descendingIndicator (p : State n) (i : Fin n) : ℤ :=
  if (p i).val < i.val then 1 else 0









end LX.Core.FiniteCuts


