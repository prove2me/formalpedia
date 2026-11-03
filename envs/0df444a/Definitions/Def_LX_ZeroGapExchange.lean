-- Prove2me | Definitions.Def_LX_ZeroGapExchange
-- name    : LX_ZeroGapExchange
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:05:47.283847+00:00
-- url     : https://prove2.me/theorems/5c286beb-1385-4a70-b2e6-e8b57108f653
-- title:
--   Exchange of zero and a selected lifted endpoint
-- statement:
--   For positive $n$, displacement board $d$, and position $v$, define a new board whose value at zero is $v+d(v)$, whose value at $v$ is $d(0)-v$, and whose other values are unchanged. Here $v$ is read as an integer representative. The zero case is checked first; if $v=0$, the board is unchanged. This formula exchanges the two integer targets while expressing their displacements in the original coordinates. No zero gap or sign condition is required to define the operation.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapExchange.lean#L10-L11

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
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

/-! Swapping the endpoints of a zero gap gives a balanced shorter lift.
The exact drop in displacement mass is twice the gap length. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def exchange (d : Fin n → ℤ) (v i : Fin n) : ℤ :=
  if i=0 then (v : ℤ)+d v else if i=v then d 0-(v : ℤ) else d i














end LX.Core.ZeroGap


