-- Prove2me | Definitions.Def_LX_FixedPairJoinPrice
-- name    : LX_FixedPairJoinPrice
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:23:46.644978+00:00
-- url     : https://prove2.me/theorems/156b94e7-a070-454a-9ea4-08187d67499d
-- title:
--   Displacement mass minus inversion count
-- statement:
--   For a permutation $q$ on a positive finite cycle, read positions in their ordinary order and let $d_i=q(i)-i$ be the signed integer displacement. Define its depth deficit as the integer $\sum_i |d_i|-\operatorname{inv}(q)$, where the inversion count uses ordinary finite inversions. The subtraction is in the integers, so nonnegativity is not built into the definition. This quantity separates displacement mass from inversion count in fixed pair joining estimates.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FixedPairJoinPrice.lean#L12-L13

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
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteEnergyRotation
import Definitions.Def_LX_FiniteInversionDecomposition
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
import Definitions.Def_LX_ShallowCutShift
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
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
namespace LX.FiniteJoin
end LX.FiniteJoin
namespace List
end List

namespace LX.FiniteJoin
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

def depthDeficit (q : State n) : ℤ :=
  (∑ i, |_root_.LX.Core.FiniteCuts.displacement q i|)-(inversionNumber q : ℤ)









end LX.FiniteJoin


