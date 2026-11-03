-- Prove2me | Definitions.Def_LX_ReverseDual
-- name    : LX_ReverseDual
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:04:11.483524+00:00
-- url     : https://prove2.me/theorems/368d35be-bca2-4cec-9f59-952af0e50805
-- title:
--   Reflection dual of an inverse permutation
-- statement:
--   For a permutation $p$ on a positive cycle, define its reverse dual to be $Jp^{-1}J$, where $J(i)=1-i$ in cyclic coordinates. The inverse is taken before conjugation by the reflection. This construction specifies the permutation transformation used to compare a directed word with its reversed order. The definition alone does not state a distance identity.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ReverseDual.lean#L9-L11

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
import Definitions.Def_LX_Connected
import Definitions.Def_LX_Graph
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection

namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.WordReflection
end LX.Core.WordReflection

namespace LX
open LX.Core.WordReflection
variable {n : ℕ} [NeZero n]

/-- Reflecting an inverse reverses an LX word without adding inverse
letters. This is a symmetry of the directed word metric. -/
def reverseDual (p : State n) : State n := reflection*p⁻¹*reflection

















end LX


