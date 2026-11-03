-- Prove2me | Definitions.Def_LX_TwoWindowCycleDefect
-- name    : LX_TwoWindowCycleDefect
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:14:37.123051+00:00
-- url     : https://prove2.me/theorems/0dd49d2f-6892-4cc1-a2ad-91f65eec4d4a
-- title:
--   Cycle defect in finite coordinates
-- statement:
--   For a permutation $p$ of $n$ positions, define its cycle defect as displacement mass minus inversion count minus support size plus the number of nontrivial disjoint cycle factors. The mass is $Σ_i|p(i)-i|$ in ordinary integer coordinates. Every term is converted to the integers before subtraction. Fixed points do not contribute nontrivial cycle factors. The definition allows the empty permutation and does not assert nonnegativity. It packages the finite quantities used in cycle defect comparisons.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/TwoWindowCycleDefect.lean#L8-L11

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
import Definitions.Def_LX_AffineDeletion
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_BufferProgram
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionIndices
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ZeroGapInversionTerms

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
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
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Cycle defect in physical finite coordinates. -/
def cycleDefect (p : State n) : ℤ :=
  (∑ i, |_root_.LX.Core.FiniteCuts.displacement p i|)-(inversionNumber p : ℤ)-
    (p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ)


end LX.Core.FiniteCuts

namespace LX.Core.FiniteWindow
open FiniteCuts
open scoped BigOperators
variable {n : ℕ}


end LX.Core.FiniteWindow


