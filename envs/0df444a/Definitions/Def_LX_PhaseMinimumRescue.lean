-- Prove2me | Definitions.Def_LX_PhaseMinimumRescue
-- name    : LX_PhaseMinimumRescue
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:04:10.577801+00:00
-- url     : https://prove2.me/theorems/38772e17-3f4f-40f2-a363-ad42189b936a
-- title:
--   Phase shift omitting one selected position
-- statement:
--   For an integer displacement board on a positive cycle and selected position $a$, apply the phase shift to the complement of the singleton containing $a$. Equivalently, add $n-1$ at $a$ and subtract one at every other position. The name refers to its later application when $a$ is a minimum; minimality is not a condition of the definition. The construction is also defined for the one position cycle, where it leaves the board unchanged. It provides a prescribed phase modification for comparing lift energies.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PhaseMinimumRescue.lean#L10-L11

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
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_Connected
import Definitions.Def_LX_Graph
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
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace List
end List

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

def raiseMinimum (d : Fin n → ℤ) (a : Fin n) : Fin n → ℤ :=
  phaseShift d (Finset.univ.erase a)






end LX.AffineScan


