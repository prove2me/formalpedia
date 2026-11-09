-- Prove2me | Definitions.Def_AgnosticTNS_encSeqIndex
-- name    : AgnosticTNS_encSeqIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:37:17.214399+00:00
-- url     : https://prove2.me/theorems/7792e1be-4351-4650-b122-474b3925af3b
-- title:
--   Input string of an instance of the sequence learner
-- statement:
--   $n,d,k_\delta$ in unary, the adjacency matrix of $G$, the learning sequence, $\chi$ in binary and $\epsilon,\vartheta$ in binary rational code.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Algorithm 1, p.19; Proposition 3.10, p.26

import Mathlib
import Definitions.Def_AgnosticTNS_SeqIndex
import Definitions.Def_AgnosticTNS_encGraph
import Definitions.Def_AgnosticTNS_encLS
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

namespace AgnosticTNS

/-- **The input string of an instance of the sequence learner**, Algorithm 1, p.19 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): `n`, `d`
and `k_δ` in unary, the adjacency matrix of `G`, the learning sequence, `χ` in binary and `ε, ϑ` in
the published binary rational code. -/
noncomputable def encSeqIndex (i : SeqIndex) : QAlgorithms.Complexity.Str :=
  encNat i.n ++ encGraph i.G ++ encLS i.Ls ++ encNat i.d ++ encBin i.χ ++ encRat i.ε ++ encRat i.ϑ ++
    encNat i.kδ

end AgnosticTNS


