-- Prove2me | Definitions.Def_VDCyclePack_encMInst
-- name    : VDCyclePack_encMInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:31.045203+00:00
-- url     : https://prove2.me/theorems/ecfb2cde-c508-4664-8cff-1a9529306a97
-- title:
--   Binary encoding of an auxiliary multigraph
-- statement:
--   The word of $n$ followed by the length-prefixed list of edges, each edge the words of its two ends in binary.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 6.2, p.18

import Mathlib
import Definitions.Def_VDCyclePack_encWList
import Definitions.Def_VDCyclePack_MInst

namespace VDCyclePack

/-- **Binary encoding of an auxiliary multigraph.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 6.2, p.18: "such cycles can be found in polynomial time".

`encMInst I` is the word of `n` followed by the length-prefixed list of edges, each edge the words of
its two ends.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(symbols `0`, `1` are bits). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length
of the encoding is the usual bit size. Every word is terminated by the symbol `2` and every list is
prefixed by its length, so the encoding is prefix-free and injective (proved in
`Solutions/verification/VDCyclePack_encodings.lean`). -/
def encMInst (I : MInst) : List OnlineCRS.Combine.Sym :=
  encWNat I.n ++ encWList (fun p : Fin I.n × Fin I.n => encWNat p.1.val ++ encWNat p.2.val) I.edges

end VDCyclePack


