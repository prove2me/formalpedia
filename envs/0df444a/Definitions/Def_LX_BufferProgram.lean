-- Prove2me | Definitions.Def_LX_BufferProgram
-- name    : LX_BufferProgram
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:04:10.997397+00:00
-- url     : https://prove2.me/theorems/5a69fd53-f54b-4be8-a84a-77f6f61a24bf
-- title:
--   Rotation and exchange counts of a word
-- statement:
--   For a word in forward rotation, backward rotation, and exchange, count rotations by the number of letters other than exchange, and count exchanges by the number equal to exchange. Both are natural numbers and both vanish on the empty word. The definitions count literal letters, including repetitions, without simplifying the evaluated permutation. They supply separate cost quantities for execution estimates.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/BufferProgram.lean#L14-L16

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

/-! Counts of rotations and exchanges in literal L/R/X words.
These counts are used by the finite support and service estimates.
Each letter contributes to exactly one of the two counts. -/
namespace LX.Core.BufferProgram
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing

variable {n : ℕ} [NeZero n]

def rotations (w : List Letter) : ℕ := (w.filter (fun a => a ≠ .x)).length

def exchanges (w : List Letter) : ℕ := (w.filter (fun a => a = .x)).length


end LX.Core.BufferProgram


