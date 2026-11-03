-- Prove2me | Definitions.Def_LX_ZeroGapInversionTerms
-- name    : LX_ZeroGapInversionTerms
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:02:13.126261+00:00
-- url     : https://prove2.me/theorems/5b413161-2135-44c3-a049-e4fdeecd5418
-- title:
--   Affine inversion summands and endpoint swapping
-- statement:
--   For integer target values on a positive cycle, the inversion term at $(i,j)$ is $|\lfloor(F(j)-F(i))/n\rfloor|$ when $i<j$, and zero otherwise. It is a natural number. Swapping endpoints means precomposing the target function with the transposition of zero and a chosen position $v$. The definitions permit $v=0$, giving the unchanged target function. These are the individual terms and target operation used in endpoint inversion calculations.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapInversionTerms.lean#L9-L12

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
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

/-! The inversion terms reversed by a zero-gap endpoint swap each drop from
one to zero. Other endpoint terms are exchanged in pairs. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def inversionTerm (F : Fin n → ℤ) (i j : Fin n) : ℕ :=
  if i < j then ((F j-F i)/(n : ℤ)).natAbs else 0

def swapEndpoints (F : Fin n → ℤ) (v i : Fin n) : ℤ := F (Equiv.swap 0 v i)











end LX.Core.ZeroGap


