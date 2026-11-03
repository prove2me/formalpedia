-- Prove2me | Definitions.Def_LX_AffineLift
-- name    : LX_AffineLift
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:00:41.410504+00:00
-- url     : https://prove2.me/theorems/137932cc-a45c-4881-a90a-9766aac67a47
-- title:
--   Balanced affine lifts and subset majorization
-- statement:
--   For a permutation $p$ of $n$ positions, integer phase $c$, and integer displacements $d(i)$, a balanced lift requires total displacement zero and $i+d(i)$ congruent to $p^{-1}(i)+c$ modulo $n$ for every token. Its energy is the natural number $Σ_i |d(i)|²$. A phase shift associated with a subset $S$ adds $|S|$ everywhere and subtracts $n$ at members of $S$. Majorization requires $2Σ_{i∈S}d(i)≤|S|(n-|S|)$ for every subset. These definitions allow $n=0$ and do not impose positivity implicitly. They provide the lift constraints and comparison quantities used throughout the phase analysis.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AffineLift.lean#L13-L89

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

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace List
end List

/-!
A balanced phase lift of an actual permutation, with subset majorization.
We minimize the nonnegative integer sum of squared displacements over all
balanced lifts and phases. Phase shifts yield majorization directly, without
assuming an affine inversion formula or a pre-existing bounded lift.
-/
namespace LX.Core.AffineLift
open scoped BigOperators

/-- `p` maps visible positions to labels, so token `i` ends at `p.symm i`.
The integer phase is the final physical cursor, taken modulo `n`. -/
def IsLift {n : ℕ} (p : State n) (c : ℤ) (d : Fin n → ℤ) : Prop :=
  (∑ i, d i) = 0 ∧ ∀ i : Fin n,
    Int.ModEq (n : ℤ) ((i : ℤ) + d i) ((p.symm i : ℤ) + c)

def energy {n : ℕ} (d : Fin n → ℤ) : ℕ := ∑ i, (d i).natAbs ^ 2







/-- Shift the final cursor by `|s|`, and subtract one turn at selected tokens. -/
def phaseShift {n : ℕ} (d : Fin n → ℤ) (s : Finset (Fin n)) (i : Fin n) : ℤ :=
  d i + s.card - if i ∈ s then (n : ℤ) else 0







/-- Subset form of the Lorenz/majorization condition used in the upper proof. -/
def Majorized {n : ℕ} (d : Fin n → ℤ) : Prop :=
  ∀ s : Finset (Fin n), 2 * ∑ i ∈ s, d i ≤ (s.card : ℤ) * (n - s.card)








end LX.Core.AffineLift


