-- Prove2me | Definitions.Def_LX_NestedMatchingGeometry
-- name    : LX_NestedMatchingGeometry
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:06:32.808305+00:00
-- url     : https://prove2.me/theorems/2b03614d-d22a-4421-a6cb-e2e57e22d6f5
-- title:
--   Exclusion of separated forward pairs
-- statement:
--   For a permutation $p$ of $n$ positions, require that for every $a<b<c<d$, the equality $p(a)=b$ implies $p(c)
--   e d$. Thus two forward pairs cannot occupy two separated intervals of the ordinary finite order. No involution hypothesis is included in this predicate. For fewer than four positions the condition is vacuous. Together with other hypotheses it expresses the geometric restriction used in nested matching analysis.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/NestedMatchingGeometry.lean#L7-L9

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LinearMatchingGeometry

namespace LX.Core
end LX.Core
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts

namespace LX.Core.FiniteCuts
variable {n : ℕ}

def NoSeparatedPairs (p : State n) : Prop :=
  ∀ a b c d : Fin n, a.val < b.val → b.val < c.val → c.val < d.val →
    p a=b → p c ≠ d







end LX.Core.FiniteCuts


