-- Prove2me | Definitions.Def_LX_LinearMatchingGeometry
-- name    : LX_LinearMatchingGeometry
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:02:57.217862+00:00
-- url     : https://prove2.me/theorems/303663ce-d930-4380-a0cc-e54d220e9bef
-- title:
--   Exclusion of crossing pairs in finite order
-- statement:
--   For a permutation $p$ of $n$ positions, impose the following condition: whenever $a<b<c<d$ and $p(a)=c$, one has $p(b)
--   e d$. Thus two indicated forward pairs cannot have alternating endpoints in the ordinary finite order. This predicate alone does not assert that $p$ is an involution or that all its cycles are pairs. It is vacuous when fewer than four positions exist. It isolates the noncrossing consequence needed in finite equality classifications.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LinearMatchingGeometry.lean#L7-L10

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

namespace LX.Core
end LX.Core
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts

namespace LX.Core.FiniteCuts
variable {n : ℕ}

/-- The only noncrossing consequence needed for the equality classification. -/
def NoncrossingPairs (p : State n) : Prop :=
  ∀ a b c d : Fin n, a.val < b.val → b.val < c.val → c.val < d.val →
    p a=c → p b ≠ d










end LX.Core.FiniteCuts


