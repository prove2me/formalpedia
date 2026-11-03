-- Prove2me | Definitions.Def_LX_ExceptionalPrefixDelay
-- name    : LX_ExceptionalPrefixDelay
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:29:37.447044+00:00
-- url     : https://prove2.me/theorems/1a5383a8-f7bd-4c34-a2c4-8f1e22186501
-- title:
--   Exceptional even and odd displacement boards
-- statement:
--   For positive $n$ and a natural parameter $m$, two integer displacement functions on the $n$ positions are specified piecewise. At positions $0,1,2$, the even board has values $4-m,1-m,1-m$, while the odd board has values $2-m,-m,0$. For all remaining positions $i$, both formulas give $m+4-2i$ when $i\le m+1$ and $3m+4-2i$ otherwise. Earlier cases take precedence. These formulas are defined without requiring $n=2m$ or $n=2m+1$. They identify boards used in the exceptional antipode analysis; the definitions themselves assert neither uniqueness nor that these boards satisfy lift conditions.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ExceptionalPrefixDelay.lean#L38-L52

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
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_FiniteCrossPairCount
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
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
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace List
end List

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





/-- Exceptional lift in the even antipode family. This definition alone
does not assert that it is the only unpaid bounded lift. -/
def evenException (m : ℕ) (i : Fin n) : ℤ :=
  if i.val=0 then 4-(m : ℤ)
  else if i.val ≤ 2 then 1-(m : ℤ)
  else if i.val ≤ m+1 then (m : ℤ)+4-2*i.val
  else 3*(m : ℤ)+4-2*i.val

/-- Exceptional lift in the odd antipode family. -/
def oddException (m : ℕ) (i : Fin n) : ℤ :=
  if i.val=0 then 2-(m : ℤ)
  else if i.val=1 then -(m : ℤ)
  else if i.val=2 then 0
  else if i.val ≤ m+1 then (m : ℤ)+4-2*i.val
  else 3*(m : ℤ)+4-2*i.val















end LX.AffineScan


