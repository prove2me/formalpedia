-- Prove2me | Definitions.Def_LX_ForwardCarrier
-- name    : LX_ForwardCarrier
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:02:17.456741+00:00
-- url     : https://prove2.me/theorems/3b699deb-ff0e-4557-9341-3c035a5f9266
-- title:
--   Ordered comparisons and forward sweep prefixes
-- statement:
--   For an integer sequence indexed by natural numbers, comparison at $k$ replaces its values at $k,k+1$ by their minimum and maximum, respectively, and leaves other entries unchanged. A sweep prefix of length zero is the original sequence. Its successor applies comparison at the next index to the preceding prefix. Thus a length $k$ prefix compares adjacent pairs starting at zero through $k-1$. These operations specify the linear comparison process before a cyclic seam is reached.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ForwardCarrier.lean#L5-L12

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

namespace Int
end Int
namespace LX
end LX
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace List
end List

namespace LX.ForwardCarrier

/-- Physical target values during a forward sweep before the seam is reached. -/
def compareAt (F : ℕ → ℤ) (k j : ℕ) : ℤ :=
  if j = k then min (F k) (F (k+1))
  else if j = k+1 then max (F k) (F (k+1)) else F j

def sweepPrefix (F : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0 => F
  | k+1 => compareAt (sweepPrefix F k) k











end LX.ForwardCarrier


