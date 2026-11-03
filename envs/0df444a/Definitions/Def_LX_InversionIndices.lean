-- Prove2me | Definitions.Def_LX_InversionIndices
-- name    : LX_InversionIndices
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:10:56.845761+00:00
-- url     : https://prove2.me/theorems/97385cea-ab2a-4c0a-86c3-304a97f968a7
-- title:
--   Integer indices selected by a signed quotient
-- statement:
--   For an integer $q$, define a finite set of integers as $[-q,0)$ when $q≥0$, and $[0,-q)$ when $q<0$. Endpoints are integer intervals with the upper endpoint excluded. In particular the set is empty for $q=0$. This convention supplies the periodic indices associated with either sign of an affine crossing quotient.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/InversionIndices.lean#L8-L9

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
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder
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

/-! Finite copy-index intervals for the inversions of one periodic pair. -/
noncomputable section

namespace LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]

def inversionIndices (q : ℤ) : Finset ℤ :=
  if 0 ≤ q then Finset.Ico (-q) 0 else Finset.Ico 0 (-q)















end LX.Core.LiftedModel


