-- Prove2me | Definitions.Def_LX_Small4
-- name    : LX_Small4
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:09:10.411807+00:00
-- url     : https://prove2.me/theorems/49c97725-9d5e-4860-a927-60408c892213
-- title:
--   Explicit directed word table for 4 positions
-- statement:
--   For permutations of 4 positions, this bundle specifies an explicit array of 24 words in forward rotation and head exchange. A permutation code selects its word by the factorial index of that code. The empty word is among the entries. The array is fixed data used for finite verification of directed word bounds; its definition does not itself assert that the entries evaluate to their indexed permutations or that their lengths are minimal. Those properties are expressed in separate results.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/Small4.lean#L9-L35

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
import Definitions.Def_LX_PermutationCode
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric

namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Small4
end LX.Small4

-- Generated witnesses; the Lean kernel checks semantics, coverage and length.
namespace LX.Small4
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def words : Array (List Letter) := #[
  [],
  [.l,.l,.x,.l,.l],
  [.l,.l,.x,.l,.x],
  [.x,.l],
  [.l,.x,.l,.l,.x],
  [.l,.l,.l,.x],
  [.x],
  [.l,.l,.x,.l,.l,.x],
  [.l,.l,.l,.x,.l,.l],
  [.l],
  [.l,.l,.l,.x,.l,.x],
  [.l,.x,.l],
  [.x,.l,.l,.x,.l],
  [.l,.x],
  [.l,.l,.x,.l],
  [.x,.l,.x],
  [.l,.l],
  [.x,.l,.l],
  [.l,.l,.l,.x,.l],
  [.l,.x,.l,.x],
  [.x,.l,.l,.x],
  [.l,.l,.x],
  [.l,.x,.l,.l],
  [.l,.l,.l]]

def table (c : LX.Core.PermCode 4) : List Letter := words[LX.Core.codeIndex c]!







end LX.Small4


