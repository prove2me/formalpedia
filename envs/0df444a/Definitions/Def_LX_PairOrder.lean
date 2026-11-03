-- Prove2me | Definitions.Def_LX_PairOrder
-- name    : LX_PairOrder
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:09:21.228832+00:00
-- url     : https://prove2.me/theorems/2f8df933-d51c-44c5-b6d0-4e1dfe95d9ec
-- title:
--   Order and validity of lifted pair keys
-- statement:
--   For a pair key and lifted configuration on a positive cycle, the key is before when the integer position of its first label is strictly less than the position of its second label plus its shift. Independently, a key is valid when its first label is strictly smaller than its second and its integer shift is divisible by $n$. The order predicate is defined even for invalid keys. These notions describe oriented comparisons between periodic token copies.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PairOrder.lean#L10-L14

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
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PairEvents
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
namespace List
end List

/-! Relative order of periodic token copies. A physical X changes the order of
exactly its own lifted pair orbit. This links reduced traces to inversions. -/
namespace LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def PairKey.Before (key : PairKey n) (s : Configuration n) : Prop :=
  s.position key.first < s.position key.second+key.shift

def PairKey.Valid (key : PairKey n) : Prop :=
  key.first < key.second ∧ (n : ℤ) ∣ key.shift













end LX.Core.LiftedModel


