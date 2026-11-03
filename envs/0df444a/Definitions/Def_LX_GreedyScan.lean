-- Prove2me | Definitions.Def_LX_GreedyScan
-- name    : LX_GreedyScan
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:06:31.661713+00:00
-- url     : https://prove2.me/theorems/3f85605b-8c32-4816-8bac-472055ddbb24
-- title:
--   Greedy scan traces on displacement boards
-- statement:
--   For an integer displacement board on a positive cycle, define finite greedy traces inductively. The zero board stops immediately with the empty word. A nonzero board rotates forward when $d(0)≤d(1)+1$, and exchanges when $d(1)+1<d(0)$, continuing from the updated board in each case. The exchange condition itself rules out the zero board. This relation specifies the exact greedy choices and stopping condition; it does not assert termination for every board.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/GreedyScan.lean#L8-L14

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
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_Connected
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_PhysicalModel
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
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace List
end List

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- The forward scan stops immediately at zero and exchanges exactly at descents. -/
inductive ScanTrace : (Fin n → ℤ) → List Letter → Prop
  | done {d} (hz : ∀ i, d i = 0) : ScanTrace d []
  | left {d w} (hz : ¬ ∀ i, d i = 0) (hle : d 0 ≤ d 1 + 1)
      (tail : ScanTrace (rotate d) w) : ScanTrace d (.l :: w)
  | swap {d w} (hdesc : d 1 + 1 < d 0)
      (tail : ScanTrace (exchange d) w) : ScanTrace d (.x :: w)

















end LX.AffineScan


