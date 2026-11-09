-- Prove2me | Definitions.Def_AgnosticTNS_encTreeIndexQ
-- name    : AgnosticTNS_encTreeIndexQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:33.739205+00:00
-- url     : https://prove2.me/theorems/e8a22882-8f94-4e55-8f58-198b5270327d
-- title:
--   Input string of an instance of Corollary 5.1
-- statement:
--   $n,d,\chi,k_\delta$ in unary, the adjacency matrix of $T$, and $\epsilon,\vartheta$ in binary rational code.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Corollary 5.1, p.39

import Mathlib
import Definitions.Def_AgnosticTNS_TreeIndexQ
import Definitions.Def_AgnosticTNS_encGraph
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

namespace AgnosticTNS

/-- **The input string of an instance of Corollary 5.1**, p.39 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): `n, d, χ, k_δ` in unary, the
adjacency matrix of `T`, and `ε, ϑ` in the published binary rational code `encRat`. -/
noncomputable def encTreeIndexQ (i : TreeIndexQ) : QAlgorithms.Complexity.Str :=
  encNat i.n ++ encGraph i.T ++ encNat i.d ++ encNat i.χ ++ encRat i.ε ++ encRat i.ϑ ++ encNat i.kδ

end AgnosticTNS


