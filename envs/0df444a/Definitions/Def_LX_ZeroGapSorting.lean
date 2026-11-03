-- Prove2me | Definitions.Def_LX_ZeroGapSorting
-- name    : LX_ZeroGapSorting
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:16:06.262214+00:00
-- url     : https://prove2.me/theorems/cef65267-a60d-4e30-b490-9ea1047ce911
-- title:
--   Mass and zero gap sorting traces
-- statement:
--   For an integer displacement board on a positive cycle, its mass is the sum of the absolute values of all displacements. A sorting trace records a permutation, a board, and a natural number of endpoint exchanges. A zero board admits a trace with zero exchanges, without requiring the permutation to be the identity. A step selects a recentering position $u$ and a nonzero endpoint $v$, requiring positive displacement at local zero, negative displacement at local $v$, and zero at every strictly intermediate local position. It then exchanges the local endpoints and continues with the recentered target and board. The trace count increases by one. This inductive relation specifies allowable finite sorting histories without asserting their existence for arbitrary inputs.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapSorting.lean#L10-L23

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
import Definitions.Def_LX_ZeroGapExchange
import Definitions.Def_LX_ZeroGapInversionSum
import Definitions.Def_LX_ZeroGapInversionTerms
import Definitions.Def_LX_ZeroGapPair

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

/-! Termination of the zero-gap sorting process and its exact number of
endpoint transpositions. Recentring is part of the mathematical trace. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def mass (d : Fin n → ℤ) : ℕ := ∑ i, (d i).natAbs



inductive SortingTrace : State n → (Fin n → ℤ) → ℕ → Prop
  | done {p d} (hz : ∀ i, d i=0) : SortingTrace p d 0
  | step {p d} (u v : Fin n) (hv : 0 < v.val)
      (hpos : 0 < RotationWords.localDisplacement d u 0)
      (hneg : RotationWords.localDisplacement d u v < 0)
      (hgap : ∀ i : Fin n, 0 < i.val → i.val < v.val → RotationWords.localDisplacement d u i=0)
      {M : ℕ}
      (tail : SortingTrace (Equiv.swap 0 v*RotationWords.localTarget p 0 u)
        (exchange (RotationWords.localDisplacement d u) v) M) : SortingTrace p d (M+1)







end LX.Core.ZeroGap


