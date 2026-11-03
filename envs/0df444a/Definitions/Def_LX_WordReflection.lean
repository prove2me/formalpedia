-- Prove2me | Definitions.Def_LX_WordReflection
-- name    : LX_WordReflection
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:03:24.374615+00:00
-- url     : https://prove2.me/theorems/d3fdf573-d6c9-40ff-9293-07007c868fdd
-- title:
--   Cyclic reflection through the head pair
-- statement:
--   On a positive cycle, define the reflection permutation by $i↦1-i$ in cyclic arithmetic. Applying the same formula twice returns the original position, so it also supplies its inverse. In small dimensions the resulting permutation is interpreted with the same modular convention. This fixes the reflection used to transform directed words and phase data.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/WordReflection.lean#L10-L14

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
import Definitions.Def_LX_SymmetricWordMetric

namespace LX.Core
end LX.Core
namespace LX.Core.WordReflection
end LX.Core.WordReflection

/-! Reflection in the edge between positions zero and one. It exchanges L/R,
fixes X, and agrees with the word symmetry already used by the lower proof. -/
namespace LX.Core.WordReflection
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def reflection : State n where
  toFun i := 1-i
  invFun i := 1-i
  left_inv i := by change (1 : Fin n)-(1-i)=i; ring
  right_inv i := by change (1 : Fin n)-(1-i)=i; ring









end LX.Core.WordReflection


