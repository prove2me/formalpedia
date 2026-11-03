-- Prove2me | Definitions.Def_LX_AffineRankOrder
-- name    : LX_AffineRankOrder
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:18:52.975889+00:00
-- url     : https://prove2.me/theorems/cf562f1f-baee-4d9f-b0b3-2f5068accf03
-- title:
--   Threshold ranks and their pointwise order
-- statement:
--   For a board on a positive cycle, integer threshold $v$, and cut residue $r$, sum over positions $i$ the nonnegative part of $\lfloor(F(i)-v)/n\rfloor+\mathbf1_{i≤r}$, where $F(i)=i+d(i)$. This integer sum defines the threshold rank. One board is rank below another when this inequality holds at every cut and every integer threshold. A tail quantity omits positions zero and one and sums the nonnegative quotient terms without cut indicators. These finite sums encode periodic rank information; no lift condition is imposed.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AffineRankOrder.lean#L8-L30

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
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_BufferProgram
import Definitions.Def_LX_Connected
import Definitions.Def_LX_DepthReturn
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_ForwardCarrier
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_InversionIndices
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SweepCarrier
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace List
end List

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Counts periodic copies of targets at least v to the left of cut r.
The infinite periodic board is represented by a finite sum of quotients. -/
def thresholdRank (d : Fin n → ℤ) (r : Fin n) (v : ℤ) : ℤ :=
  ∑ i : Fin n,max ((targets d i-v)/(n : ℤ)+(if i ≤ r then 1 else 0)) 0

def RankLE (d e : Fin n → ℤ) : Prop :=
  ∀ r v,thresholdRank d r v ≤ thresholdRank e r v






 def _root_.LX.UploadDefinitions.AffineRankOrder.rankTail (d : Fin n → ℤ) (v : ℤ) : ℤ :=
  ∑ i ∈ (Finset.univ.erase (0 : Fin n)).erase 1,max ((targets d i-v)/(n : ℤ)) 0
































end LX.AffineScan


