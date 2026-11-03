-- Prove2me | Definitions.Def_LX_FiniteWindowRestriction
-- name    : LX_FiniteWindowRestriction
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:09:57.397113+00:00
-- url     : https://prove2.me/theorems/8e2f879e-3814-4632-b801-f607fa2af44e
-- title:
--   Restricting a permutation to an invariant window
-- statement:
--   Let a window of length $b$ begin at offset $a$ inside $n$ positions, with $a+b\le n$. Suppose a permutation $p$ preserves membership in this window in both directions. Restrict $p$ to its invariant subset and identify the subset with $b$ local positions by $i\mapsto a+i$. The resulting permutation sends local position $i$ to the local coordinate of $p(a+i)$. Empty windows are allowed. This construction transfers finite permutation arguments between a window and the ambient set without changing the local ordering.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FiniteWindowRestriction.lean#L22-L23

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
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_RecenteredLift

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace List
end List

/-! Extract the finite permutation of an invariant physical window. -/
namespace LX.Core.FiniteWindow
variable {n b : ℕ}



def restriction (W : Window n b) (p : State n) (hW : ∀ j, Contains W (p j) ↔ Contains W j) : State b :=
  ((windowEquiv W).trans (p.subtypePerm hW)).trans (windowEquiv W).symm






end LX.Core.FiniteWindow


