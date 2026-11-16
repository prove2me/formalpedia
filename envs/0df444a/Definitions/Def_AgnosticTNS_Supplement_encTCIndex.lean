-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_encTCIndex
-- name    : AgnosticTNS_Supplement_encTCIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:41:30.835727+00:00
-- url     : https://prove2.me/theorems/c6d015f0-6bbb-45ae-b79e-0ba95c7baa4c
-- title:
--   Input string of a Theorem 6.18 instance
-- statement:
--   The binary input of an instance of Theorem 6.18: $n$, $m$, $k$, $d$, $k_\epsilon$, $k_\delta$ in unary, the adjacency matrices of $G$ and $\hat T$, the indicator vector of every bag, and $\chi$ in binary.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.18, p.60

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_TCIndex
import Definitions.Def_AgnosticTNS_encGraph
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

namespace AgnosticTNS.Supplement

/-- **The input string of an instance of Theorem 6.18**, p.60 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
`n`, `m`, `k`, `d`, `k_ε`, `k_δ` in unary, the adjacency matrices of `G` and `T̂`, the indicator vector of
every bag `X̂_t`, and `χ` in binary. -/
noncomputable def encTCIndex (i : TCIndex) : QAlgorithms.Complexity.Str :=
  encNat i.n ++ encGraph i.G ++ encNat i.m ++ encGraph i.That ++
    ((List.finRange i.m).map fun t => (List.finRange i.n).map fun v => decide (v ∈ i.Xhat t)).flatten ++
    encNat i.k ++ encNat i.d ++ encBin i.χ ++ encNat i.kε ++ encNat i.kδ

end AgnosticTNS.Supplement


