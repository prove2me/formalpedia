-- Prove2me | Definitions.Def_VDCyclePack_encCycles
-- name    : VDCyclePack_encCycles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:25.536219+00:00
-- url     : https://prove2.me/theorems/629c150a-24b3-40b7-bd1f-f0ea63fa2d00
-- title:
--   Binary encoding of a list of vertex lists
-- statement:
--   A list of cycles (or paths), each a vertex list, encoded as a length-prefixed list of length-prefixed lists of binary vertex indices. It is the output encoding of the algorithms.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Theorem 1.1, p.3

import Mathlib
import Definitions.Def_VDCyclePack_encWList

namespace VDCyclePack

/-- **Binary encoding of a list of vertex lists (a family of cycles or paths).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Theorem 1.1, p.3: "returns a family P of pairwise vertex-disjoint cycles".

`encCycles cs` is the length-prefixed list of the length-prefixed vertex lists, vertex indices in
binary.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(symbols `0`, `1` are bits). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length
of the encoding is the usual bit size. Every word is terminated by the symbol `2` and every list is
prefixed by its length, so the encoding is prefix-free and injective (proved in
`Solutions/verification/VDCyclePack_encodings.lean`). -/
def encCycles (cs : List (List ℕ)) : List OnlineCRS.Combine.Sym :=
  encWList (encWList encWNat) cs

end VDCyclePack


