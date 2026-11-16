-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_encContrIndex
-- name    : AgnosticTNS_Supplement_encContrIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:29:38.357202+00:00
-- url     : https://prove2.me/theorems/9b27f179-de7c-4254-b0bc-ec95c4dc325b
-- title:
--   Input string of a contraction-sequence instance
-- statement:
--   The binary input of an instance of Theorem 1.2: $n$, $d$, $k_\epsilon$, $k_\delta$ in unary, the adjacency matrix of $G$, the number of merges in unary followed by the indicator vectors of the two merged sets of each step, and $\chi$ in binary. Running times are measured in the length of this string padded with the paper's parameters.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 1.2, p.3

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_ContrIndex
import Definitions.Def_AgnosticTNS_encGraph
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

namespace AgnosticTNS.Supplement

/-- **The input string of an instance of Theorem 1.2**, p.3 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
`n`, `d`, `k_ε`, `k_δ` in unary, the adjacency matrix of `G`, the number of merges in unary followed by
the indicator vectors of the two merged sets of every step, and `χ` in binary. -/
noncomputable def encContrIndex (i : ContrIndex) : QAlgorithms.Complexity.Str :=
  encNat i.n ++ encGraph i.G ++ encNat i.steps.length ++
    (i.steps.map fun s => (List.finRange i.n).map (fun v => decide (v ∈ s.1)) ++
      (List.finRange i.n).map (fun v => decide (v ∈ s.2))).flatten ++
    encNat i.d ++ encBin i.χ ++ encNat i.kε ++ encNat i.kδ

end AgnosticTNS.Supplement


