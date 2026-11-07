-- Prove2me | Definitions.Def_MatrixSpencer_encMatInst
-- name    : MatrixSpencer_encMatInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:02.513425+00:00
-- url     : https://prove2.me/theorems/11c54bb4-4f63-427d-b790-37ff697873ca
-- title:
--   Encoding of a matrix instance
-- statement:
--   The instance is written as $n$ in unary, the separator $3$, $d$ in unary, the separator $3$, and then all $nd^2$ entries in the lexicographic order of (matrix, row, column), each in binary.
--
--   **Formalization Note** The dimensions are unary because the output has $n$ bits: with binary dimensions and $d=0$ it would be longer than any polynomial of the input. For $d\ge1$ the entries force this length anyway.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Theorem 1.3, p.12 (auxiliary encoding)

import Mathlib
import Definitions.Def_MatrixSpencer_MatInst
import Definitions.Def_RobustToDynamics_encListRat
import Definitions.Def_OnlineCRS_Combine_Sym

namespace MatrixSpencer

/-- **Encoding of a matrix instance.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), auxiliary encoding for "randomized polynomial time" (p.12).

`n` and `d` are written in **unary**, each followed by the separator `3`, and then all `n d²` entries,
in the lexicographic order of `(i, a, b)`, each in binary via `RobustToDynamics.encListRat`.

**Formalization Note.** Unary dimensions are what "polynomial" must mean here: the output has `n`
bits, so with binary dimensions and `d = 0` it would be longer than any polynomial of the input.
Whenever `d ≥ 1` the `n d²` entries force the input to be that long anyway. The encoding is proved
injective in `Solutions/verification/MatrixSpencer_sanity.lean`. -/
def encMatInst (I : MatInst) : List OnlineCRS.Combine.Sym :=
  List.replicate I.n 1 ++ [3] ++ List.replicate I.d 1 ++ [3] ++
    RobustToDynamics.encListRat (((List.finRange I.n).product ((List.finRange I.d).product (List.finRange I.d))).map
      fun p => I.A p.1 p.2.1 p.2.2)

end MatrixSpencer


