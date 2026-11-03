-- Prove2me | Definitions.Def_LX_RecenteredLift
-- name    : LX_RecenteredLift
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:06:17.855513+00:00
-- url     : https://prove2.me/theorems/a8b9ecff-5482-4313-8b1f-193a10774ed4
-- title:
--   Local target and displacement coordinates
-- statement:
--   For a positive cycle, permutation $p$, and residues $c,r$, define its local target as $L^{-r}pL^{-(c-r)}$, with exponents read from cyclic representatives. For an integer board $d$, its local displacement at $i$ is $d(L^r(i))$. These coordinate transformations retain the full permutation and integer values and do not impose a lift condition. They supply the recentering convention used before endpoint operations.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/RecenteredLift.lean#L11-L15

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
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace List
end List

/-! Recenter a phase lift at an arbitrary port. The local target is chosen so
that paid entry and exit rotations recover the original visible permutation. -/
namespace LX.Core.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def localTarget (p : State n) (c r : Fin n) : State n :=
  (L n^r.val)⁻¹*p*(L n^(c-r).val)⁻¹

def localDisplacement (d : Fin n → ℤ) (r : Fin n) (i : Fin n) : ℤ :=
  d ((L n^r.val) i)










end LX.Core.RotationWords


