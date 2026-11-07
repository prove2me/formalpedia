-- Prove2me | Definitions.Def_VDCyclePack_encMCycles
-- name    : VDCyclePack_encMCycles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:24.419136+00:00
-- url     : https://prove2.me/theorems/8b86b1c3-5e19-4d0d-8c20-70e5b9e8619d
-- title:
--   Binary encoding of a list of multigraph cycles
-- statement:
--   A list of multigraph cycles, each its vertex list and its edge-index list, encoded as a length-prefixed list of pairs of length-prefixed lists of binary indices.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 6.2, p.18

import Mathlib
import Definitions.Def_VDCyclePack_encWList

namespace VDCyclePack

/-- **Binary encoding of a list of multigraph cycles.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 6.2, p.18: "such cycles can be found in polynomial time".

`encMCycles cs` is the length-prefixed list of cycles, each its length-prefixed vertex list followed
by its length-prefixed edge-index list.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(symbols `0`, `1` are bits). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length
of the encoding is the usual bit size. Every word is terminated by the symbol `2` and every list is
prefixed by its length, so the encoding is prefix-free and injective (proved in
`Solutions/verification/VDCyclePack_encodings.lean`). -/
def encMCycles (cs : List (List ℕ × List ℕ)) : List OnlineCRS.Combine.Sym :=
  encWList (fun c : List ℕ × List ℕ => encWList encWNat c.1 ++ encWList encWNat c.2) cs

end VDCyclePack


