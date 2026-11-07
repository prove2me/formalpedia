-- Prove2me | Definitions.Def_MatrixSpencer_encPartialInst
-- name    : MatrixSpencer_encPartialInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:53.473321+00:00
-- url     : https://prove2.me/theorems/f4db7d27-f910-4734-be40-c1e86a21d3e4
-- title:
--   Encoding of a partial-coloring instance
-- statement:
--   The encoding of the matrix instance followed by the coordinates of $x^{(0)}$, in order, in binary.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.7, p.11 (auxiliary encoding)

import Mathlib
import Definitions.Def_MatrixSpencer_PartialInst
import Definitions.Def_MatrixSpencer_encMatInst

namespace MatrixSpencer

/-- **Encoding of a partial-coloring instance.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.7, p.11.

The matrix instance, followed by the entries of `x⁽⁰⁾` in order. -/
def encPartialInst (I : PartialInst) : List OnlineCRS.Combine.Sym :=
  encMatInst I.inst ++ RobustToDynamics.encListRat (List.ofFn I.x0)

end MatrixSpencer


