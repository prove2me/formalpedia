-- Prove2me | Definitions.Def_LX_ZeroGapCycleRoots
-- name    : LX_ZeroGapCycleRoots
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:13:43.376028+00:00
-- url     : https://prove2.me/theorems/a0866bf9-3997-4332-8453-67d6794eebf1
-- title:
--   Root representatives from permutation cycles
-- statement:
--   For a permutation $q$ on a positive cycle, choose the least position in its support when the support is nonempty, and choose zero otherwise. For another permutation $p$, form a root list from all fixed positions of its inverse, followed by one such representative for each nontrivial disjoint cycle factor of the inverse. Finite sets are converted to lists using the formalization’s chosen order. This gives representatives associated with fixed positions and cycle factors for event root cover arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapCycleRoots.lean#L13-L33

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
import Definitions.Def_LX_BufferProgram
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PortRoute
import Definitions.Def_LX_ZeroGapComponentSize
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Definitions.Def_LX_ZeroGapExchange
import Definitions.Def_LX_ZeroGapPair
import Definitions.Def_LX_ZeroGapRootCoverCount

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

/-! Cycle representatives and fixed points give a root cover of the sorting
event graph; all cycles inside the packet can share one root. -/
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

noncomputable def cycleRoot (q : State n) : Fin n := by
  classical
  exact if h : q.support.Nonempty then q.support.min' h else 0





noncomputable def cycleRoots (p : State n) : List (Fin n) := by
  classical
  exact (p⁻¹).supportᶜ.toList ++ (p⁻¹).cycleFactorsFinset.toList.map cycleRoot






end LX.Core.ZeroGap


