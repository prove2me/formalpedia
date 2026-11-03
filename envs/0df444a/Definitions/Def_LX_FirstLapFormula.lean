-- Prove2me | Definitions.Def_LX_FirstLapFormula
-- name    : LX_FirstLapFormula
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:17:15.937192+00:00
-- url     : https://prove2.me/theorems/8f601c75-811b-49fb-9ca2-06c2f18a5807
-- title:
--   Prefix minimum and emitted depth
-- statement:
--   For a natural valued sequence $b$, its prefix minimum at $k$ is the minimum of $b(0),\ldots,b(k)$. For an integer displacement board on a positive cycle, let the periodic target at $j$ be $j+d(j\bmod n)$ and let its depth be the backward depth of that residue. The emitted depth at $j$ is its original depth minus one if an earlier target is strictly larger; otherwise it is the prefix minimum of original depths through $j-1$. Subtraction in these depth indices and values is truncated natural subtraction, so the definition includes $j=0$. This records first lap depth data entirely from the input board.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FirstLapFormula.lean#L8-L59

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

/-- Minimum of the original depths at positions 0 through k. -/
def prefixMinimum (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => b 0
  | k+1 => min (prefixMinimum b k) (b (k+1))







/-- All quantities in this expression belong to the original input lift. -/
def emittedDepth (d : Fin n → ℤ) (j : ℕ) : ℕ :=
  if ∃ i : Fin j, atTarget d j < atTarget d i.val
  then atDepth d j-1 else prefixMinimum (atDepth d) (j-1)








end LX.AffineScan


