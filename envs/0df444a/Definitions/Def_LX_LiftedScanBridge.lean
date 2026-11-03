-- Prove2me | Definitions.Def_LX_LiftedScanBridge
-- name    : LX_LiftedScanBridge
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:14:25.466419+00:00
-- url     : https://prove2.me/theorems/6600250a-c9f2-4804-a8f0-e1530278eb07
-- title:
--   Remaining displacement in a lifted execution
-- statement:
--   For a lifted configuration on a positive cycle, its visible permutation is obtained from its physical token permutation and cursor. Given an integer target function $F$ on token labels, define the remainder at a relative position $i$ to be the target of the token visible there minus its tracked integer position. Thus $R(i)=F(v(i))-P(v(i))$, where $v$ is the visible permutation and $P$ the integer position log. The difference is taken in the integers and retains winding information. No alignment or target compatibility hypothesis is required to form it. This connects literal lifted execution to displacement board updates.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LiftedScanBridge.lean#L8-L14

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
import Definitions.Def_LX_BufferProgram
import Definitions.Def_LX_Connected
import Definitions.Def_LX_EventTrace
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
namespace LX.LiftedScan
end LX.LiftedScan
namespace List
end List

namespace LX.LiftedScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

abbrev visible (s : LX.Core.LiftedModel.Configuration n) : State n :=
  LX.Core.PhysicalModel.visible s.physical

/-- Remaining displacement of the token currently at a relative cursor slot.
Targets and tracked positions are integers, so winding is preserved. -/
def remainder (F : Fin n → ℤ) (s : LX.Core.LiftedModel.Configuration n) (i : Fin n) : ℤ :=
  F (visible s i)-s.position (visible s i)





























end LX.LiftedScan


