-- Prove2me | Definitions.Def_LX_PairEvents
-- name    : LX_PairEvents
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:06:43.351264+00:00
-- url     : https://prove2.me/theorems/5e0619dc-e03f-44ff-945d-131b9f9590ad
-- title:
--   Normalized keys for lifted pair events
-- statement:
--   A pair key on $n$ positions consists of two labels and an integer shift. Normalize a pair by placing the smaller label first, reversing the shift when the labels are reversed; equality retains the original order and shift. The action of a key is its two token renaming with opposite offsets. For a lifted configuration on a positive cycle, its exchange event key uses the two current head tokens and shift equal to the first token’s integer position plus one minus the second’s position, then normalizes that data. This records the labeled lifted exchange rather than only the physical cursor.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PairEvents.lean#L9-L26

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PhysicalModel

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace List
end List

/-! Canonical keys of lifted pair events. The stored shift is n times the copy
index, avoiding any loss through integer division. Order reversal negates it. -/
namespace LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing

structure PairKey (n : ℕ) where
  first : Fin n
  second : Fin n
  shift : ℤ
  deriving DecidableEq

variable {n : ℕ} [NeZero n]

def normalizePair (a b : Fin n) (shift : ℤ) : PairKey n :=
  if a ≤ b then ⟨a,b,shift⟩ else ⟨b,a,-shift⟩

def PairKey.action (key : PairKey n) : Configuration n → Configuration n :=
  pairRename key.first key.second key.shift

def eventKey (s : Configuration n) : PairKey n :=
  let a := s.physical.tokens s.physical.cursor
  let b := s.physical.tokens (s.physical.cursor+1)
  normalizePair a b (s.position a+1-s.position b)

















end LX.Core.LiftedModel


