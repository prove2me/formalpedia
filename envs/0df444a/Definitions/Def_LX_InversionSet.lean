-- Prove2me | Definitions.Def_LX_InversionSet
-- name    : LX_InversionSet
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:12:17.31627+00:00
-- url     : https://prove2.me/theorems/685bfa55-f94c-46f9-bf72-3b87e028fc55
-- title:
--   Finite affine inversion sets and counts
-- statement:
--   For integer targets $F$ on a positive cycle, examine every pair $i<j$ and set $q=\lfloor(F(j)-F(i))/n\rfloor$. Use indices in $[-q,0)$ if $q≥0$, and $[0,-q)$ otherwise. Each index $k$ produces the pair key $(i,j,nk)$; their finite union is the inversion pair set. The inversion count is the sum of $|q|$ over $i<j$. The embedding retains both labels and the integer period index. No residue compatibility or distinct target assumption is required to define either quantity.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/InversionSet.lean#L11-L29

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
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder
import Definitions.Def_LX_PhysicalModel

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
namespace List
end List

/-! A finite set of all affine inversions, with its explicit double-sum cardinality. -/
noncomputable section

namespace LX.Core.LiftedModel
open scoped BigOperators
variable {n : ℕ} [NeZero n]

def pairIndexEmbedding : (Σ _i : Fin n, Σ _j : Fin n, ℤ) ↪ PairKey n where
  toFun t := ⟨t.1, t.2.1, (n : ℤ)*t.2.2⟩
  inj' := by
    rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
    have hi : i=i' := congrArg PairKey.first h
    have hj : j=j' := congrArg PairKey.second h
    have hk : (n : ℤ)*k=(n : ℤ)*k' := congrArg PairKey.shift h
    have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    have hkk : k=k' := (mul_left_cancel₀ hn hk)
    subst i'; subst j'; subst k'
    rfl

def inversionPairs (F : Fin n → ℤ) : Finset (PairKey n) :=
  ((Finset.univ : Finset (Fin n)).sigma (fun i =>
    (Finset.univ : Finset (Fin n)).sigma (fun j =>
      if i < j then inversionIndices ((F j-F i)/(n : ℤ)) else ∅))).map pairIndexEmbedding

def inversionCount (F : Fin n → ℤ) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then ((F j-F i)/(n : ℤ)).natAbs else 0













end LX.Core.LiftedModel


