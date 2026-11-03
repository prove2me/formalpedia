-- Prove2me | Definitions.Def_LX_LiftedPair
-- name    : LX_LiftedPair
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:05:34.643142+00:00
-- url     : https://prove2.me/theorems/95f6cdad-18c8-42ad-916c-1e09ac9a2073
-- title:
--   Two token renaming with opposite offsets
-- statement:
--   For positions $a,b$ and integer shift $s$, assign offset $s$ to label $a$, offset $-s$ to label $b$, and zero to all other labels. The test for $a$ comes first, so equal labels receive $s$. Rename a lifted configuration using the transposition of these labels and these offsets. The definition applies to every positive cycle and does not require distinct labels or a shift divisible by the dimension. It packages the pair actions used for affine events.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LiftedPair.lean#L10-L14

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
import Definitions.Def_LX_AffineCrossings
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PhysicalModel

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace List
end List

/-! A lifted pair is a pair of finite labels together with an integer relative
copy offset. Equal pair events implement the same periodic involution. -/
namespace LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def pairOffset (a b : Fin n) (shift : ℤ) (i : Fin n) : ℤ :=
  if i=a then shift else if i=b then -shift else 0

def pairRename (a b : Fin n) (shift : ℤ) : Configuration n → Configuration n :=
  rename (Equiv.swap a b) (pairOffset a b shift)














end LX.Core.LiftedModel


