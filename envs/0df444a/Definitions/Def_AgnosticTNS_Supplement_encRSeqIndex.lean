-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_encRSeqIndex
-- name    : AgnosticTNS_Supplement_encRSeqIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:30:45.804318+00:00
-- url     : https://prove2.me/theorems/3a3a9f46-2f3c-4924-9f84-0e13b04bf48f
-- title:
--   Input string of an Algorithm 2 instance
-- statement:
--   The binary input of an instance of Algorithm 2: $n$, $d$, $k_\epsilon$, $k_\delta$ in unary, the adjacency matrix of $G$, the learning sequence, $\chi$ in binary, and the edge dimensions (a flag, then $w(\{u,v\})$ in binary for every ordered adjacent pair).
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Algorithm 2, p.33

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_RSeqIndex
import Definitions.Def_AgnosticTNS_encGraph
import Definitions.Def_AgnosticTNS_encLS
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

namespace AgnosticTNS.Supplement

/-- **The input string of an instance of Algorithm 2**, p.33 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
`n`, `d`, `k_ε`, `k_δ` in unary, the adjacency matrix of `G`, the learning sequence, `χ` in binary,
and the edge dimensions (a flag, then for every ordered pair `(u, v)` with `u ~ v` the value
`w({u, v})` in binary). -/
noncomputable def encRSeqIndex (i : RSeqIndex) : QAlgorithms.Complexity.Str := by
  classical
  exact encNat i.n ++ encGraph i.G ++ encLS i.Ls ++ encNat i.d ++ encBin i.χ ++
    (match i.w with
      | none => [false]
      | some w => true :: ((List.finRange i.n).map fun u => (List.finRange i.n).map fun v =>
          if h : i.G.Adj u v then encBin (w ⟨s(u, v), h⟩) else []).flatten.flatten) ++
    encNat i.kε ++ encNat i.kδ

end AgnosticTNS.Supplement


