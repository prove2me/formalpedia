-- Prove2me | Definitions.Def_VDCyclePack_encGraph
-- name    : VDCyclePack_encGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:11.099235+00:00
-- url     : https://prove2.me/theorems/ac860f68-3b1c-4248-a42e-a1f18e340df3
-- title:
--   Binary encoding of an input graph
-- statement:
--   The word of $n$ followed by the length-prefixed list of edges, each edge the words of its two vertex indices in binary. Its length is the usual bit size of the graph.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Theorem 1.1, p.3

import Mathlib
import Definitions.Def_VDCyclePack_encWList
import Definitions.Def_VDCyclePack_GraphInst

namespace VDCyclePack

/-- **Binary encoding of an input graph.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Theorem 1.1, p.3: "There is a deterministic polynomial-time algorithm that, given a
finite simple undirected graph G, …".

`encGraph I` is the word of `n` followed by the length-prefixed list of edges, each edge the words
of its two vertex indices.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(symbols `0`, `1` are bits). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length
of the encoding is the usual bit size. Every word is terminated by the symbol `2` and every list is
prefixed by its length, so the encoding is prefix-free and injective (proved in
`Solutions/verification/VDCyclePack_encodings.lean`). -/
def encGraph (I : GraphInst) : List OnlineCRS.Combine.Sym :=
  encWNat I.n ++ encWList (fun p : ℕ × ℕ => encWNat p.1 ++ encWNat p.2) I.edges

end VDCyclePack


