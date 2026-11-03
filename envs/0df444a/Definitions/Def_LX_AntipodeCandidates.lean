-- Prove2me | Definitions.Def_LX_AntipodeCandidates
-- name    : LX_AntipodeCandidates
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:15:13.618424+00:00
-- url     : https://prove2.me/theorems/f3828386-e7be-416c-9312-46f4da4714cc
-- title:
--   Explicit even and odd antipode candidates
-- statement:
--   On a positive cycle, the even candidate is the inverse of the product of the reflection $i↦1-i$ with the transposition of residues one and two. It is defined without requiring even dimension. For $n=2m+1$ with $m≥2$, define an odd rank permutation sending $2$ to $m+1$, each $3≤i≤m+1$ to $i-1$, and fixing the remaining positions. The odd candidate is the inverse of reflection times this rank permutation. These are specified candidates; their definitions do not assert extremality in a word metric.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AntipodeCandidates.lean#L11-L43

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
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_BufferProgram
import Definitions.Def_LX_Connected
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_InversionIndices
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_TwoColorPairs
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection
import Definitions.Def_LX_ZeroGapInversionTerms

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Antipode
end LX.Antipode
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
namespace LX.Core.WordReflection
end LX.Core.WordReflection
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Generation-oriented even candidate; its inverse is the sorting
permutation [1,n-1,0,n-2,...,2]. -/
def even : State n := (LX.Core.WordReflection.reflection*Equiv.swap 1 2).symm

def oddRankValue (m k : ℕ) : ℕ :=
  if k=2 then m+1 else if 3 ≤ k ∧ k ≤ m+1 then k-1 else k

def oddRankInverseValue (m k : ℕ) : ℕ :=
  if k=m+1 then 2 else if 2 ≤ k ∧ k ≤ m then k+1 else k

def oddRank (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) : State n where
  toFun i := ⟨oddRankValue m i.val,by
    have := i.isLt
    unfold oddRankValue
    split_ifs <;> omega⟩
  invFun i := ⟨oddRankInverseValue m i.val,by
    have := i.isLt
    unfold oddRankInverseValue
    split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext
    change oddRankInverseValue m (oddRankValue m i.val)=i.val
    unfold oddRankValue oddRankInverseValue
    split_ifs <;> omega
  right_inv i := by
    apply Fin.ext
    change oddRankValue m (oddRankInverseValue m i.val)=i.val
    unfold oddRankValue oddRankInverseValue
    split_ifs <;> omega

/-- Generation-oriented odd candidate. -/
def odd (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) : State n :=
  (LX.Core.WordReflection.reflection*oddRank m hm hn).symm











end LX.Antipode


