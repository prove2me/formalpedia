-- Prove2me | Definitions.Def_LX_PrunedLift
-- name    : LX_PrunedLift
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:02:42.461791+00:00
-- url     : https://prove2.me/theorems/2a376c18-9be0-4db3-b633-8a16ab9a2503
-- title:
--   Keeping a permutation on an invariant subset
-- statement:
--   Let $p$ be a permutation of $n$ positions and $S$ a finite subset such that $p(i)$ belongs to $S$ exactly when $i$ does. Define a permutation agreeing with $p$ on $S$ and fixing every position outside $S$. Its inverse agrees with the inverse of $p$ on $S$ and is also the identity outside. The empty subset yields the identity, and the full subset yields $p$. This construction retains selected invariant parts of a permutation on the original ambient positions.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PrunedLift.lean#L10-L22

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
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift

/-! Restrict a permutation and its lift to an invariant union of cycles.
Balance of the retained lift is stated separately from invariance. -/
namespace LX.Core.PrunedLift
open scoped BigOperators
variable {n : ℕ}

def permutation (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) : State n where
  toFun i := if i ∈ S then p i else i
  invFun i := if i ∈ S then p.symm i else i
  left_inv i := by
    by_cases hi : i ∈ S
    · simp [hi, (hS i).mpr hi]
    · simp [hi]
  right_inv i := by
    by_cases hi : i ∈ S
    · have hm : p.symm i ∈ S := (hS (p.symm i)).mp (by simpa using hi)
      simp [hi, hm]
    · simp [hi]





end LX.Core.PrunedLift


