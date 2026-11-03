-- Prove2me | Definitions.Def_LX_LiftedRename
-- name    : LX_LiftedRename
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:04:32.810347+00:00
-- url     : https://prove2.me/theorems/5a801638-05ac-493b-aedb-da71a9232896
-- title:
--   Renaming lifted tokens with integer offsets
-- statement:
--   Given a lifted configuration on a positive cycle, a label permutation $q$, and an integer offset for each new label, rename the physical tokens by multiplying the old token permutation on the left by $q^{-1}$. The new integer position of label $i$ is the old position of $q(i)$ plus its assigned offset. Both cursors remain unchanged. Offsets are arbitrary, with no alignment or divisibility condition in this definition. This construction expresses label changes together with their lifted position adjustments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LiftedRename.lean#L10-L13

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
namespace List
end List

/-! Periodic renaming of lifted tokens commutes with physical execution. The
integer offset is retained, so this symmetry records winding as well as labels. -/
namespace LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def rename (q : State n) (offset : Fin n → ℤ) (s : Configuration n) : Configuration n where
  physical := ⟨q.symm*s.physical.tokens, s.physical.cursor⟩
  position i := s.position (q i)+offset i
  cursor := s.cursor











end LX.Core.LiftedModel


