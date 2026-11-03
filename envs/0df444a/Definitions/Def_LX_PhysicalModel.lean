-- Prove2me | Definitions.Def_LX_PhysicalModel
-- name    : LX_PhysicalModel
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:02:20.237777+00:00
-- url     : https://prove2.me/theorems/13b3452e-244d-4679-9527-7510c4e410a7
-- title:
--   Physical token configurations and cursor execution
-- statement:
--   On a positive cycle, a physical configuration consists of a permutation assigning token labels to positions and a cursor position. A forward or backward rotation moves only the cursor by one cyclic step. An exchange swaps the tokens at the cursor and its successor. A word executes its letters from left to right; the empty word leaves the configuration unchanged. Initially the token permutation is the identity and the cursor is zero. The visible permutation is the physical token permutation multiplied by the forward rotation raised to the cursor representative. These definitions separate physical token motion from the visible coordinate frame.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PhysicalModel.lean#L11-L61

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
import Definitions.Def_LX_Graph

namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel

/-! Physical positions, a paid cursor, and literal L/R/X words.
Every physical operation is proved to induce the same visible generator.
A realized balanced lift ends at the original target in its exact orientation. -/
namespace LX.Core.PhysicalModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open AffineLift

structure Configuration (n : ℕ) where
  tokens : State n
  cursor : Fin n

variable {n : ℕ} [NeZero n]

def visible (s : Configuration n) : State n := s.tokens * L n ^ s.cursor.val



def step (a : Letter) (s : Configuration n) : Configuration n :=
  match a with
  | .l => ⟨s.tokens, s.cursor + 1⟩
  | .r => ⟨s.tokens, s.cursor - 1⟩
  | .x => ⟨s.tokens * Equiv.swap s.cursor (s.cursor + 1), s.cursor⟩



def run : List Letter → Configuration n → Configuration n
  | [], s => s
  | a :: w, s => run w (step a s)



def initial : Configuration n := ⟨1, 0⟩




end LX.Core.PhysicalModel


