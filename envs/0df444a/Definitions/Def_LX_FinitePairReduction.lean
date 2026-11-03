-- Prove2me | Definitions.Def_LX_FinitePairReduction
-- name    : LX_FinitePairReduction
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:04:03.33682+00:00
-- url     : https://prove2.me/theorems/56ebed8b-83b0-42da-b7bb-bdec15e51cc6
-- title:
--   Shortest words and exchange partner traces
-- statement:
--   On a positive cycle, use the directed alphabet consisting of forward rotation and head exchange. A word is shortest from a permutation $p$ when every word with the same endpoint after right multiplication has at least its length. A head pair means that two specified labels occupy positions zero and one in either order. For a specified token, the partner trace records its other head token whenever an exchange occurs, and records nothing for rotations. The current permutation is updated after each letter. The head partner test checks position zero first, so its convention remains defined when small dimensions identify positions zero and one. These predicates and traces express local token participation in shortest directed words.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FinitePairReduction.lean#L8-L21

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
import Definitions.Def_LX_Connected
import Definitions.Def_LX_Graph
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
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.FinitePairReduction
end LX.FinitePairReduction
namespace List
end List

namespace LX.FinitePairReduction
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def ShortestFrom (p : State n) (w : List Letter) : Prop :=
  ∀ v : List Letter,p*eval v=p*eval w → w.length ≤ v.length

def HeadPair (p : State n) (a b : Fin n) : Prop :=
  (p 0=a ∧ p 1=b) ∨ (p 0=b ∧ p 1=a)

def headPartners (i : Fin n) (p : State n) : List (Fin n) :=
  if p 0=i then [p 1] else if p 1=i then [p 0] else []

/-- The actual successive exchange partners of one named token. -/
def partners (i : Fin n) : List Letter → State n → List (Fin n)
  | [], _ => []
  | .l::w, p => partners i w (p*eval [.l])
  | .x::w, p => headPartners i p ++ partners i w (p*eval [.x])

























end LX.FinitePairReduction


