-- Prove2me | Definitions.Def_LX_LiftedModel
-- name    : LX_LiftedModel
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:03:26.864212+00:00
-- url     : https://prove2.me/theorems/150e9d6d-ea10-4b45-a8c9-d2cd6002bb9e
-- title:
--   Lifted integer positions and cursor execution
-- statement:
--   A lifted configuration on a positive cycle contains a physical configuration, one integer position for every named token, and an integer cursor. Alignment means their residues agree with the physical cursor and with each token’s physical location. Forward and backward letters change the integer cursor by one and minus one; exchange leaves it fixed and adds one to the first head token’s integer position while subtracting one from the second. Both contributions apply if those tokens coincide. Words execute left to right. Initially positions equal their natural representatives and the cursor is zero. These data retain winding that physical residues alone cannot record.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LiftedModel.lean#L11-L113

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

/-! Literal LX.Core execution with an integer cursor and integer positions of every
named token. The position log records winding, including exchanges at the seam.
Its residues are proved to agree with the finite physical permutation. -/
namespace LX.Core.LiftedModel
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing

structure Configuration (n : ℕ) where
  physical : PhysicalModel.Configuration n
  position : Fin n → ℤ
  cursor : ℤ

variable {n : ℕ} [NeZero n]

def Aligned (s : Configuration n) : Prop :=
  (s.cursor : Fin n) = s.physical.cursor ∧
  ∀ i, (s.position i : Fin n) = s.physical.tokens.symm i

def increment (a : Letter) : ℤ := match a with
  | .l => 1
  | .r => -1
  | .x => 0

def step (a : Letter) (s : Configuration n) : Configuration n where
  physical := PhysicalModel.step a s.physical
  cursor := s.cursor + increment a
  position i := match a with
    | .l | .r => s.position i
    | .x => s.position i + (if i = s.physical.tokens s.physical.cursor then 1 else 0) -
        (if i = s.physical.tokens (s.physical.cursor + 1) then 1 else 0)







def run : List Letter → Configuration n → Configuration n
  | [], s => s
  | a :: w, s => run w (step a s)











def initial : Configuration n := ⟨PhysicalModel.initial, fun i => (i : ℤ), 0⟩











end LX.Core.LiftedModel


