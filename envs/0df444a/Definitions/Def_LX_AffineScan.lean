-- Prove2me | Definitions.Def_LX_AffineScan
-- name    : LX_AffineScan
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:04:53.862468+00:00
-- url     : https://prove2.me/theorems/afa9fbd1-ec03-46d2-8ef6-5770fc6b5863
-- title:
--   Affine displacement board execution
-- statement:
--   For an integer board $d$ on a positive cycle, its cyclic label at position $i$ is $i+d(i)$ modulo $n$. Forward rotation replaces $d(i)$ by $d(L(i))$. Head exchange replaces it by $d(X(i))$ plus the indicator of $i=0$ minus the indicator of $i=1$. Both indicators are retained even if those positions coincide. Execute directed words by successive application from left to right, with the empty word acting identically. This is the displacement board model of rotation and exchange.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AffineScan.lean#L11-L143

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

/-! Local invariants for the forward scan used to construct LX words.
This module proves progress and energy descent, not the quadratic price. -/
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def labels (d : Fin n → ℤ) (i : Fin n) : Fin n := i + (d i : Fin n)

def rotate (d : Fin n → ℤ) (i : Fin n) : ℤ := d (finRotate n i)

def exchange (d : Fin n → ℤ) (i : Fin n) : ℤ :=
  d (Equiv.swap 0 1 i) + (if i = 0 then 1 else 0) - (if i = 1 then 1 else 0)
























def step : Letter → (Fin n → ℤ) → (Fin n → ℤ)
  | .l => rotate
  | .x => exchange

def run : List Letter → (Fin n → ℤ) → (Fin n → ℤ)
  | [], d => d
  | a :: w, d => run w (step a d)





















end LX.AffineScan


