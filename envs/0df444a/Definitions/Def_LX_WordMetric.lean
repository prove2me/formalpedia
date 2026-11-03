-- Prove2me | Definitions.Def_LX_WordMetric
-- name    : LX_WordMetric
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:03:23.019353+00:00
-- url     : https://prove2.me/theorems/0fd943d3-a46a-4776-9f1c-0f8933f98a56
-- title:
--   Directed words, length, distance, and diameter
-- statement:
--   On a positive cycle, directed words use only forward rotation and exchange. Evaluate them through the three letter model. Translate a backward rotation into $n-1$ forward rotations and extend this replacement to words by concatenation. Define the directed length of a permutation as the infimum of natural word lengths representing it. Define distance from $a$ to $b$ as the length of $a^{-1}b$, and diameter as the maximum length over the finite permutation set. The infimum definition uses the natural infimum convention even before representability is established separately. These definitions retain directed generator costs without identifying them with a symmetric graph metric.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/WordMetric.lean#L10-L85

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

namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords

/-! Directed LX words. No inverse generator is included in the alphabet.
The target bound is a proposition, not an axiom or an assumed estimate. -/
namespace LX

abbrev State := LX.Core.State

inductive Letter where
  | l | x
  deriving DecidableEq, Repr

def Letter.toCore : Letter → LX.Core.Letter
  | .l => .l
  | .x => .x

def eval {n : ℕ} [NeZero n] (w : List Letter) : State n :=
  LX.Core.eval (w.map Letter.toCore)





/-- A correctness bridge only: expanding R this way does not prove a quadratic bound. -/
def expandLetter (n : ℕ) : LX.Core.Letter → List Letter
  | .l => [.l]
  | .r => List.replicate (n - 1) .l
  | .x => [.x]

def expand (n : ℕ) (w : List LX.Core.Letter) : List Letter :=
  w.flatMap (expandLetter n)







/-- Minimum directed length from the identity; reachability is proved separately. -/
noncomputable def length {n : ℕ} [NeZero n] (p : State n) : ℕ :=
  sInf {k : ℕ | ∃ w : List Letter, eval w = p ∧ w.length = k}





/-- Right-multiplication directed distance, without symmetrizing generators. -/
noncomputable def dist {n : ℕ} [NeZero n] (a b : State n) : ℕ := length (a⁻¹ * b)

/-- Maximum directed distance; translation reduces all pairs to the identity. -/
noncomputable def diameter (n : ℕ) [NeZero n] : ℕ :=
  Finset.univ.sup (fun p : State n => length p)









end LX


