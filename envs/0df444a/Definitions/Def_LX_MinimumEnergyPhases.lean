-- Prove2me | Definitions.Def_LX_MinimumEnergyPhases
-- name    : LX_MinimumEnergyPhases
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:33:16.987058+00:00
-- url     : https://prove2.me/theorems/865c374b-496b-4254-b1bf-e4866f071f5d
-- title:
--   Global minimum energy of an anchored lift
-- statement:
--   For a permutation $p$ on a positive cycle and anchor $a$, require that the energy of its anchored displacement board be no greater than the energy of every balanced lift of $p^{-1}$, at every integer phase. Energy is the sum of squared absolute integer displacements. The comparison quantifies over all integer boards satisfying the lift condition, without a width restriction. This defines global minimum energy for the selected anchor; it does not merely compare anchor heights or only the finite family of anchored candidates.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/MinimumEnergyPhases.lean#L9-L12

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
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_BufferProgram
import Definitions.Def_LX_ClockwiseLiftCount
import Definitions.Def_LX_CompleteMapping
import Definitions.Def_LX_Connected
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_FiniteCrossPairCount
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_InversionIndices
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PortRoute
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_StrictBandInversionCapacity
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
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Global minimum over all balanced integer lifts and all phases. It is
stronger than minimizing the anchor height. -/
def GlobalMinimum (p : State n) (a : Fin n) : Prop :=
  ∀ c d, IsLift p.symm c d → energy (_root_.LX.AnchoredPhases.displacement p a) ≤ energy d















end LX.AnchoredPhases


