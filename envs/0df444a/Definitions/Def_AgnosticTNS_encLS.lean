-- Prove2me | Definitions.Def_AgnosticTNS_encLS
-- name    : AgnosticTNS_encLS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:20.676199+00:00
-- url     : https://prove2.me/theorems/5c198f25-ff17-4a05-980c-fc03a2f7a754
-- title:
--   Learning sequence as an input string
-- statement:
--   A learning sequence is written as its length $L$ in unary followed, for each step, by the indicator vectors of $S_i$, $I_i$ and $F_i$. "The learning sequence is an input to the algorithm" (Proposition 3.10).
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Proposition 3.10, p.26

import Mathlib
import Definitions.Def_AgnosticTNS_LearningSequence
import Definitions.Def_QAlgorithms_ClassicalStringComputability

namespace AgnosticTNS

/-- **A learning sequence as an input string**, Algorithm 1 input and Proposition 3.10, p.26 ("The
learning sequence is an input to the algorithm") (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): `L` in unary, then for every step `i`
the indicator vectors of `S_i`, `I_i` and `F_i`. -/
def encLS {n : ℕ} (Ls : LearningSequence n) : QAlgorithms.Complexity.Str :=
  QAlgorithms.Complexity.encNat Ls.L ++ ((List.finRange Ls.L).map fun i =>
    (List.finRange n).map (fun v => decide (v ∈ Ls.S i)) ++
    (List.finRange Ls.L).map (fun j => decide (j ∈ Ls.I i)) ++
    (List.finRange n).map (fun v => decide (v ∈ Ls.F i))).flatten

end AgnosticTNS


