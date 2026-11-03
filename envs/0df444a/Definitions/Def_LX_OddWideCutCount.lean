-- Prove2me | Definitions.Def_LX_OddWideCutCount
-- name    : LX_OddWideCutCount
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:38:47.422715+00:00
-- url     : https://prove2.me/theorems/42913a9a-abee-49d1-86a9-e51ac0930758
-- title:
--   Terminal head and aligned anchor conditions
-- statement:
--   For a positive cycle, permutation $p$, and natural height parameter $h$, three predicates specify terminal configurations. The head predecessor condition requires height $h$ at anchor zero and $0<(1-p(0))≤h+3$. The smaller higher aligned condition requires a higher aligned terminal anchor $b$ and another anchor $c$ of height $h+1$ with $0<c-p(c)<b-p(b)$. The relevant terminal head condition allows either height $h$ at zero, or height $h+1$ there with $0<-p(0)≤h+3$. Differences in these inequalities are cyclic residues read as ordinary representatives. These predicates package the separate terminal alternatives without asserting that any alternative occurs.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/OddWideCutCount.lean#L42-L50

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
import Definitions.Def_LX_DeadlinePrice
import Definitions.Def_LX_DepthCrowding
import Definitions.Def_LX_DepthReturn
import Definitions.Def_LX_EvenUnitStructure
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_FiniteChainMerge
import Definitions.Def_LX_FiniteCrossPairCount
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteDropBudget
import Definitions.Def_LX_FiniteEnergyRotation
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteInversionDecomposition
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_FiniteWindowRestriction
import Definitions.Def_LX_FirstLapFormula
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_ForwardCarrier
import Definitions.Def_LX_ForwardPrefixContraction
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_InversionIndices
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_LinearMatchingGeometry
import Definitions.Def_LX_LowOffsetDropBudget
import Definitions.Def_LX_MinimumEnergyPhases
import Definitions.Def_LX_MinimumHeightMultiplicity
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_MinimumOffsetCount
import Definitions.Def_LX_NestedMatchingGeometry
import Definitions.Def_LX_OddPairedHigherPayment
import Definitions.Def_LX_PairCorePorts
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PortRoute
import Definitions.Def_LX_RankPeakCount
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SecondExcess
import Definitions.Def_LX_StrictBandInversionCapacity
import Definitions.Def_LX_SweepCarrier
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
namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.PairCore
end LX.PairCore
namespace List
end List

namespace LX.AnchoredPhases
open Classical
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]





def HeadPredecessorTerminal (p : State n) (h : ℕ) : Prop :=
  height p 0=h ∧ 0 < (1-p 0).val ∧ (1-p 0).val ≤ h+3

def SmallerHigherAlignedTerminal (p : State n) (h : ℕ) : Prop :=
  ∃ b c : Fin n,HigherAlignedTerminal p h b ∧ height p c=h+1 ∧
    0 < (c-p c).val ∧ (c-p c).val < (b-p b).val

def RelevantTerminalHead (p : State n) (h : ℕ) : Prop :=
  height p 0=h ∨ (height p 0=h+1 ∧ 0 < (-p 0).val ∧ (-p 0).val ≤ h+3)













end LX.AnchoredPhases


