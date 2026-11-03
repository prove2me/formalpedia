-- Prove2me | Definitions.Def_LX_SymmetricWordMetric
-- name    : LX_SymmetricWordMetric
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:02:37.454446+00:00
-- url     : https://prove2.me/theorems/ed38467c-4c07-496b-b7b9-0897fb98cfbc
-- title:
--   Inverse letters in the symmetric alphabet
-- statement:
--   On the three letter alphabet, interchange forward rotation with backward rotation and leave exchange fixed. This operation defines the inverse of a single letter and requires no dimension parameter. It supplies the letter convention for reversing symmetric words and expressing inverse evaluations.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/SymmetricWordMetric.lean#L6-L9

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

namespace LX.Core

def Letter.inverse : Letter → Letter
  | .l => .r
  | .r => .l
  | .x => .x










end LX.Core


