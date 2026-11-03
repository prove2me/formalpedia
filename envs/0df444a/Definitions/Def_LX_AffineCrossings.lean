-- Prove2me | Definitions.Def_LX_AffineCrossings
-- name    : LX_AffineCrossings
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:01:43.382375+00:00
-- url     : https://prove2.me/theorems/495d3da7-8014-4b1f-86f3-d8dae5340838
-- title:
--   Signed affine crossing numbers
-- statement:
--   For positive $n$, an integer displacement function $d$, and cyclic positions $i,j$, form the crossing numerator $(j-i)_{n}+d(j)-d(i)$, where the cyclic difference is represented between zero and $n-1$. Its crossing number is the negative of the integer quotient of this numerator by $n$, using floor division. No balance or lift condition is imposed. These signed quantities express pairwise affine crossing data in a fixed orientation.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AffineCrossings.lean#L22-L26

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
import Definitions.Def_LX_AffineLift
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

/-! Signed affine crossing data obtained from an actual balanced phase lift.
The row-sum identity is proved from bijectivity of endpoint residues. -/
namespace LX.Core.AffineLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





def crossingNumerator (d : Fin n → ℤ) (i j : Fin n) : ℤ :=
  ((j - i : Fin n) : ℤ) + d j - d i

def crossing (d : Fin n → ℤ) (i j : Fin n) : ℤ :=
  -(crossingNumerator d i j / (n : ℤ))
























end LX.Core.AffineLift


