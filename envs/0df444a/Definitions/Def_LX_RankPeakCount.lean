-- Prove2me | Definitions.Def_LX_RankPeakCount
-- name    : LX_RankPeakCount
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:36:11.277848+00:00
-- url     : https://prove2.me/theorems/e0eb8c05-64e6-430f-a837-33b5867332e6
-- title:
--   Cyclic offsets at a selected anchor height
-- statement:
--   For a permutation $p$ on a positive cycle and natural $h$, select positions whose anchored height is $h$ and collect their displacement residues $p(i)-i$ in a finite set. Repeated residues are counted only once. No assumption requires $h$ to be the minimum height, and the set is empty if the selected height is absent. This set records the available cyclic offsets at that rank level.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/RankPeakCount.lean#L105-L106

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
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_AnchorPhasePrice
import Definitions.Def_LX_AnchorReserveRigidity
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_BufferProgram
import Definitions.Def_LX_ClockwiseLiftCount
import Definitions.Def_LX_CompleteMapping
import Definitions.Def_LX_Connected
import Definitions.Def_LX_EvenUnitStructure
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_FiniteCrossPairCount
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteInversionDecomposition
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_FiniteWindowRestriction
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_InversionIndices
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_LinearMatchingGeometry
import Definitions.Def_LX_MinimumEnergyPhases
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_NestedMatchingGeometry
import Definitions.Def_LX_PairCorePorts
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PortRoute
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_StrictBandInversionCapacity
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_TwoWindowCycleDefect
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
namespace LX.Core.FiniteCoordinates
end LX.Core.FiniteCoordinates
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
namespace LX.PairCore
end LX.PairCore
namespace List
end List

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]












def minimumHeightOffsets (p : State n) (h : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter fun i => height p i=h).image (fun i => p i-i)












end LX.AnchoredPhases


