-- Prove2me | Definitions.Def_LX_ExceptionalPriceLower
-- name    : LX_ExceptionalPriceLower
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:31:00.941642+00:00
-- url     : https://prove2.me/theorems/d6940e60-259c-4cc2-a461-526229153c58
-- title:
--   Piecewise depth profiles for exceptional boards
-- statement:
--   For natural numbers $m,k$, define two natural valued profiles. The even profile is $m-2$ at $k=0$, $m-1$ at $1\le k\le2$, $k-3$ at $3\le k\le m+1$, and $k-(m+2)$ otherwise. The odd profile is $m-1,m,0$ at $k=0,1,2$, respectively, followed by the same two remaining formulas. Cases are evaluated in the stated order, and all subtraction is truncated natural subtraction. These functions specify comparison profiles for later depth estimates; no inequality with an actual depth is part of their definition.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ExceptionalPriceLower.lean#L44-L49

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
import Definitions.Def_LX_AffineRankOrder
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_BufferProgram
import Definitions.Def_LX_ClockwiseLiftCount
import Definitions.Def_LX_Connected
import Definitions.Def_LX_DeadlinePrice
import Definitions.Def_LX_DepthCrowding
import Definitions.Def_LX_DepthReturn
import Definitions.Def_LX_DirectedTokenLower
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_ExceptionalPrefixDelay
import Definitions.Def_LX_FiniteCrossPairCount
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FinitePairReduction
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_FirstLapFormula
import Definitions.Def_LX_ForwardCarrier
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyRotationOptimality
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_InversionIndices
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_LiftedScanBridge
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PortRoute
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_StrictBandInversionCapacity
import Definitions.Def_LX_SweepCarrier
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
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
namespace LX.AffineScan
end LX.AffineScan
namespace LX.AnchoredPhases
end LX.AnchoredPhases
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
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace LX.FinitePairReduction
end LX.FinitePairReduction
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.LiftedScan
end LX.LiftedScan
namespace List
end List

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





def evenDepthLower (m k : ℕ) : ℕ :=
  if k=0 then m-2 else if k ≤ 2 then m-1 else if k ≤ m+1 then k-3 else k-(m+2)

def oddDepthLower (m k : ℕ) : ℕ :=
  if k=0 then m-1 else if k=1 then m else if k=2 then 0
  else if k ≤ m+1 then k-3 else k-(m+2)























end LX.AffineScan


