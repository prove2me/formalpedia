-- Prove2me | Definitions.Def_LX_FiniteWindow
-- name    : LX_FiniteWindow
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:09:18.703201+00:00
-- url     : https://prove2.me/theorems/7f1a9ae3-d830-42b2-84cd-81a0f047fcc5
-- title:
--   Finite windows and permutation extension
-- statement:
--   A window of length $b$ in $n$ positions consists of a natural offset $a$ and a bound $a+b≤n$. Its local position $i$ embeds at $a+i$, and an ambient position belongs to the window exactly when its representative lies in the half open interval $[a,a+b)$. The embedding is identified with an equivalence onto that subset. A permutation of the $b$ local positions extends to an ambient permutation through this equivalence, fixing the complement. Empty windows are allowed. These constructions fix the coordinate conventions for local finite permutation arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FiniteWindow.lean#L9-L32

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

/-! Extend a finite permutation to a contiguous window of a larger ambient
permutation, fixing every external label. No ambient size is changed. -/
namespace LX.Core.FiniteWindow
variable {n b : ℕ}

structure Window (n b : ℕ) where
  offset : ℕ
  fits : offset+b ≤ n

def embed (W : Window n b) (i : Fin b) : Fin n := ⟨W.offset+i.val, by have := W.fits; omega⟩

def Contains (W : Window n b) (j : Fin n) : Prop :=
  W.offset ≤ j.val ∧ j.val < W.offset+b

instance (W : Window n b) : DecidablePred (Contains W) := fun j => inferInstanceAs (Decidable (W.offset ≤ j.val ∧ j.val < W.offset+b))

def windowEquiv (W : Window n b) : Fin b ≃ {j : Fin n // Contains W j} where
  toFun i := ⟨embed W i, by unfold Contains embed; simp⟩
  invFun j := ⟨j.val.val-W.offset, by have := j.property; unfold Contains at this; omega⟩
  left_inv i := by apply Fin.ext; simp [embed]
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have := j.property
    unfold Contains at this
    dsimp [embed]
    omega

def permutation (W : Window n b) (p : State b) : State n := p.extendDomain (windowEquiv W)



















end LX.Core.FiniteWindow


