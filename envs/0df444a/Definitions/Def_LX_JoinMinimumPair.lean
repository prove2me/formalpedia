-- Prove2me | Definitions.Def_LX_JoinMinimumPair
-- name    : LX_JoinMinimumPair
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:09:29.418393+00:00
-- url     : https://prove2.me/theorems/c508cdce-65fd-4f18-a58f-5779d044bed2
-- title:
--   Displacement modification joining two minima
-- statement:
--   For positive $n$, an integer displacement function $d$, and positions $u,v$, define a new displacement at $i$ by
--
--   $$d(i)-1+\mathbf1_{i=u}+(n-1)\mathbf1_{i=v}.$$
--
--   The two indicators are added independently, including when $u=v$. The definition does not impose distinctness, minimality, balance, parity, or a relation between these positions and a permutation. It specifies the modification used when joining selected fixed positions and shifting a phase; hypotheses establishing that interpretation belong to later results.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/JoinMinimumPair.lean#L10-L13

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
import Definitions.Def_LX_Connected
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace List
end List

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- The balanced lift obtained by joining two fixed positions of an odd
three-fixed-point source and shifting the final phase back by one. -/
def joinMinima (d : Fin n → ℤ) (u v : Fin n) (i : Fin n) : ℤ :=
  d i-1+(if i=u then 1 else 0)+(if i=v then (n : ℤ)-1 else 0)














end LX.AffineScan


