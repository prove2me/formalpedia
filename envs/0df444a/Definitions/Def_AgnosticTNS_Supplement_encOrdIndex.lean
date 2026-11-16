-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_encOrdIndex
-- name    : AgnosticTNS_Supplement_encOrdIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:40:47.13464+00:00
-- url     : https://prove2.me/theorems/b5ed6358-7cce-41a5-94ab-465b74c99279
-- title:
--   Input string of a Theorem 6.16 instance
-- statement:
--   The binary input of an instance of Theorem 6.16: $n$, $d$, $k_\epsilon$, $k_\delta$ in unary, the adjacency matrix of $G$, the positions $\pi(v)$ in unary, and $\chi$ in binary.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.16, p.59

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_OrdIndex
import Definitions.Def_AgnosticTNS_encGraph
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

namespace AgnosticTNS.Supplement

/-- **The input string of an instance of Theorem 6.16**, p.59 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
`n`, `d`, `k_ε`, `k_δ` in unary, the adjacency matrix of `G`, the positions `π(v)` in unary, and `χ` in
binary. -/
noncomputable def encOrdIndex (i : OrdIndex) : QAlgorithms.Complexity.Str :=
  encNat i.n ++ encGraph i.G ++ ((List.finRange i.n).map fun v => encNat (i.π v)).flatten ++
    encNat i.d ++ encBin i.χ ++ encNat i.kε ++ encNat i.kδ

end AgnosticTNS.Supplement


