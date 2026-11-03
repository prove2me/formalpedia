-- Prove2me | Definitions.Def_LX_Small5Exact
-- name    : LX_Small5Exact
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:09:25.379783+00:00
-- url     : https://prove2.me/theorems/8b292845-6c44-4303-8dfe-09a36a625a4f
-- title:
--   Potential table and distinguished permutation on five positions
-- statement:
--   For permutations of five positions, specify an array of 120 natural valued potentials indexed by the factorial code of each permutation. The score of a permutation is the corresponding array entry. Also specify the permutation with image list $[1,0,4,2,3]$. These concrete data support the finite analysis of exact directed distances. The potential definition alone does not assert a distance bound, an edge inequality, or maximality of the distinguished permutation.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/Small5Exact.lean#L8-L31

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
namespace LX.Small5
end LX.Small5

namespace LX.Small5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def potentials : Array ℕ := #[
  0,6,6,7,9,11,6,7,7,2,8,9,7,8,6,9,4,9,7,6,9,10,6,5,
  1,7,7,8,10,11,7,8,7,1,7,8,8,7,7,9,3,8,7,7,8,9,7,5,
  7,9,8,2,8,9,6,8,8,3,9,10,9,8,9,8,3,2,9,4,8,9,8,5,
  7,7,6,10,4,9,10,8,10,9,3,4,6,8,5,10,5,10,9,10,4,3,4,5,
  6,6,7,9,6,5,7,6,8,8,8,5,10,9,6,5,4,5,6,5,8,10,5,4]

def score (p : State 5) : ℕ := potentials[LX.Core.codeIndex (LX.Core.encode p)]!





noncomputable def farthest : State 5 :=
  Equiv.ofBijective ![1,0,4,2,3] (by decide +kernel)







end LX.Small5


