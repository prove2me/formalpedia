-- Prove2me | Definitions.Def_LX_PrunedPartition
-- name    : LX_PrunedPartition
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:03:39.819941+00:00
-- url     : https://prove2.me/theorems/4092559e-fd39-40b7-b987-b47ac01e93d4
-- title:
--   Invariance of the complementary subset
-- statement:
--   Let $p$ be a permutation of $n$ positions and $S$ an invariant finite subset, expressed by $p(i)∈S$ if and only if $i∈S$ for every position $i$. Its complement satisfies the corresponding equivalence $p(i)∈Sᶜ$ if and only if $i∈Sᶜ$. This supporting interface makes complementary invariant parts available to the construction that keeps a permutation on a selected subset and fixes the rest. It includes empty and full subsets and also the empty ambient set.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PrunedPartition.lean#L9-L10

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
import Definitions.Def_LX_PrunedLift

namespace LX.Core
end LX.Core
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift

/-! The retained and removed unions of cycles partition both the permutation
and every integer displacement, with disjoint physical targets. -/
namespace LX.Core.PrunedLift
variable {n : ℕ}

theorem complement_invariant (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (i : Fin n) : p i ∈ Sᶜ ↔ i ∈ Sᶜ := by simp [hS]







end LX.Core.PrunedLift


