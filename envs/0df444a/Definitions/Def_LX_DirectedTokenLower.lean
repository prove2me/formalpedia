-- Prove2me | Definitions.Def_LX_DirectedTokenLower
-- name    : LX_DirectedTokenLower
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:15:02.55519+00:00
-- url     : https://prove2.me/theorems/8ae41e0b-9e52-4f8a-83f5-c5b14c88b1f2
-- title:
--   Token budget predicate for directed executions
-- statement:
--   For a lifted configuration on a positive cycle, require for every label $i$ that $n·(i-1)≤c+(n-1)P(i)$, where $P(i)$ is its tracked integer position and $c$ its integer cursor. In the left hand side, $i-1$ is truncated natural subtraction of the label representative before conversion to the integers; the other arithmetic is integer arithmetic. This predicate is defined for arbitrary configurations and expresses the token budget used in directed lower bound arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/DirectedTokenLower.lean#L10-L13

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
import Definitions.Def_LX_Connected
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionIndices
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric

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
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace List
end List

namespace LX.DirectedTokenLower
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]

/-- A token cannot make repeated net backward progress without paying
forward cursor turns. This invariant allows arbitrary detours and swaps. -/
def TokenBudget (s : Configuration n) : Prop :=
  ∀ i : Fin n,(n : ℤ)*(i.val-1 : ℕ) ≤ s.cursor+((n : ℤ)-1)*s.position i



















end LX.DirectedTokenLower


