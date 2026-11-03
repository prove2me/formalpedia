-- Prove2me | Definitions.Def_LX_ZeroGapPair
-- name    : LX_ZeroGapPair
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:02:15.811279+00:00
-- url     : https://prove2.me/theorems/c753add9-1856-4727-abf7-e9ceedd1a799
-- title:
--   Forward cyclic distance between positions
-- statement:
--   For two positions $u,v$ on a positive cycle, define their forward distance as the ordinary representative of the residue $v-u$. It lies between zero and $n-1$ and is zero for equal positions. The quantity is directed and need not equal the distance in the reverse direction. It specifies the interval lengths used for endpoint events and their integer travel weights.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapPair.lean#L9-L9

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

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap

/-! Every nonzero balanced displacement vector has an oppositely signed pair
with no nonzero displacement in the open forward arc between its endpoints. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def distance (u v : Fin n) : ℕ := (v-u).val








end LX.Core.ZeroGap


