-- Prove2me | Definitions.Def_LX_TwoColorPairs
-- name    : LX_TwoColorPairs
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:02:34.324424+00:00
-- url     : https://prove2.me/theorems/8a4b37aa-55c8-4980-aec9-6cf5302a1ee4
-- title:
--   Counts of colors and monochromatic pairs
-- statement:
--   For a Boolean coloring of $n$ ordered positions, count each color by the number of positions having that value. Count same color pairs by the number of pairs $i<j$ with equal colors. Each unordered pair of distinct positions contributes once, and diagonal pairs contribute nothing. Both definitions allow the empty domain. These statistics express two color pair counts without selecting a particular arrangement of either color.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/TwoColorPairs.lean#L7-L11

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

namespace LX
end LX

namespace LX
open scoped BigOperators
variable {n : ℕ}

def sameColorPairs (χ : Fin n → Bool) : ℕ :=
  ∑ i : Fin n,∑ j : Fin n,if i < j ∧ χ i=χ j then 1 else 0

def colorCount (χ : Fin n → Bool) (b : Bool) : ℕ :=
  (Finset.univ.filter fun i => χ i=b).card











end LX


