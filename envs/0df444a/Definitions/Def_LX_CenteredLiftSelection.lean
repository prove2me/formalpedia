-- Prove2me | Definitions.Def_LX_CenteredLiftSelection
-- name    : LX_CenteredLiftSelection
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:06:40.304339+00:00
-- url     : https://prove2.me/theorems/b492a728-aaaf-45ec-bb78-be42e05ed1af
-- title:
--   Centered representatives and a single coordinate raise
-- statement:
--   For positive $n$, natural $m$, and integer $z$, define the centered representative as $((z+m)\bmod n)-m$. It lies in the integer interval from $-m$ through $n-m-1$. For an integer function $e$ and position $a$, raising at $a$ adds $n$ to that coordinate and leaves the others unchanged. These operations are defined without balance, parity, or minimality hypotheses and specify representatives and single turn modifications used in lift selection.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/CenteredLiftSelection.lean#L8-L65

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
namespace LX.CenteredLift
end LX.CenteredLift
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

namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def center (m : ℕ) (z : ℤ) : ℤ := (z+m) % (n : ℤ)-m













def raiseAt (e : Fin n → ℤ) (a : Fin n) (i : Fin n) : ℤ := e i+if i=a then n else 0




end LX.CenteredLift


