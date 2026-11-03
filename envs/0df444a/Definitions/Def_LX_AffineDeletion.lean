-- Prove2me | Definitions.Def_LX_AffineDeletion
-- name    : LX_AffineDeletion
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:10:29.355522+00:00
-- url     : https://prove2.me/theorems/cc8b89bb-8e5b-44e6-9be4-86b1f57412e2
-- title:
--   The rotation subsequence of a word
-- statement:
--   For a word in forward rotation, backward rotation, and exchange, retain precisely the letters other than exchange. The resulting subsequence preserves the order and multiplicity of both kinds of rotations, and is empty for a word containing only exchanges. This operation specifies the literal rotation data used when studying deletion of exchange events.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AffineDeletion.lean#L11-L11

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
import Definitions.Def_LX_BufferProgram
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PairEvents
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

/-! Repeated lifted pairs can be eliminated from every finite LX.Core word. The
integer endpoint configuration and the entire L/R subsequence are preserved.
Identifying the remaining number of X with affine inversion length is separate. -/
namespace LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]

def rotationLetters (w : List Letter) : List Letter := w.filter (fun a => a ≠ .x)













end LX.Core.LiftedModel


