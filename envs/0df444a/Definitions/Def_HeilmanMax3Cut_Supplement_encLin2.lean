-- Prove2me | Definitions.Def_HeilmanMax3Cut_Supplement_encLin2
-- name    : HeilmanMax3Cut_Supplement_encLin2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:06:35.472202+00:00
-- url     : https://prove2.me/theorems/12d40500-2d3b-4904-a090-57a41f9ce852
-- title:
--   Encoding of a MAX-2-LIN(3) instance
-- statement:
--   The input string of a MAX-2-LIN(3) instance: the number $n$ of variables in unary, then for each equation $x_i-x_j=c$ the indices $i$ and $j$ in unary and $c$ as one of three symbols. The encoding is injective and of length polynomial in $n+m$.
--
--   **Formalization Note** The alphabet is the published `Max3CutHard.LinSym` (unary digit, separator, three constants).
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Theorem 1.5, p.4

import Mathlib
import Definitions.Def_Max3CutHard_LinSym
import Definitions.Def_HeilmanMax3Cut_Supplement_Lin2Inst

namespace HeilmanMax3Cut.Supplement

/-- **Encoding of a MAX-2-LIN(3) instance.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Theorem 1.5, p.4 (the input of the problem): the
number `n` of variables in unary, then for every listed equation `x_i − x_j = c` the indices `i` and
`j` in unary and `c` as one symbol, over the published alphabet `Max3CutHard.LinSym`.

**Formalization Note.** Every number `a` is written `one^a sep`; `c = 0, 1, 2` is written `t0`, `t1`,
`t2`. The encoding is injective (the number of variables is read first, then each equation), so the
gap problem is not trivialised by a lossy encoding, and its length is polynomial in `n + m`. -/
def encLin2 (I : Lin2Inst) : List Max3CutHard.LinSym :=
  (List.replicate I.n Max3CutHard.LinSym.one ++ [Max3CutHard.LinSym.sep]) ++
    I.eqs.flatMap fun e =>
      (List.replicate (e.i : ℕ) Max3CutHard.LinSym.one ++ [Max3CutHard.LinSym.sep]) ++
      (List.replicate (e.j : ℕ) Max3CutHard.LinSym.one ++ [Max3CutHard.LinSym.sep]) ++
      [if e.c = 0 then Max3CutHard.LinSym.t0 else if e.c = 1 then Max3CutHard.LinSym.t1
        else Max3CutHard.LinSym.t2]

end HeilmanMax3Cut.Supplement


