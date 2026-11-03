-- Prove2me | Definitions.Def_LX_SweepCarrier
-- name    : LX_SweepCarrier
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:09:25.341062+00:00
-- url     : https://prove2.me/theorems/3eb059fb-3429-414c-b252-14160b1c0b03
-- title:
--   Greedy sweep states and their words
-- statement:
--   For a board on a positive cycle, the periodic target at natural index $j$ is $j+d(j\bmod n)$. Compare the head by exchanging exactly when $d(1)+1<d(0)$; then rotate once to obtain a sweep step. Iterating defines the state after any natural number of steps. A step word is exchange followed by rotation in the strict descent case, and rotation alone otherwise. Concatenating those state dependent step words defines the sweep word. This specifies the full execution data without assuming balance or termination.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/SweepCarrier.lean#L9-L26

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
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_Connected
import Definitions.Def_LX_ForwardCarrier
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
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
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace List
end List

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Periodic target values, read in the current cursor coordinates. -/
def atTarget (d : Fin n → ℤ) (j : ℕ) : ℤ := (j : ℤ) + d (j : Fin n)

def compareHead (d : Fin n → ℤ) : Fin n → ℤ :=
  if d 1 + 1 < d 0 then exchange d else d

def sweepStep (d : Fin n → ℤ) : Fin n → ℤ := rotate (compareHead d)

def sweep (d : Fin n → ℤ) : ℕ → (Fin n → ℤ)
  | 0 => d
  | k+1 => sweepStep (sweep d k)

def sweepStepWord (d : Fin n → ℤ) : List Letter :=
  if d 1 + 1 < d 0 then [.x, .l] else [.l]

def sweepWord (d : Fin n → ℤ) : ℕ → List Letter
  | 0 => []
  | k+1 => sweepWord d k ++ sweepStepWord (sweep d k)






























end LX.AffineScan


