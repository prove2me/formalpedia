-- Prove2me | Definitions.Def_VDCyclePack_encWeighted
-- name    : VDCyclePack_encWeighted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:08.608939+00:00
-- url     : https://prove2.me/theorems/c859633c-de49-4716-8da9-6aee9919c64f
-- title:
--   Binary encoding of an explicit weighted list of cycles
-- statement:
--   A list of (cycle, rational weight) entries, encoded as a length-prefixed list whose entries are a length-prefixed vertex list followed by the word of the weight.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 4.1, p.11

import Mathlib
import Definitions.Def_VDCyclePack_encWList
import Definitions.Def_VDCyclePack_encWRat

namespace VDCyclePack

/-- **Binary encoding of an explicit weighted list of cycles.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 4.1, p.11: "given as an explicit list of polynomially many cycles with positive
rational weights".

`encWeighted ws` is the length-prefixed list of entries, each a length-prefixed vertex list
followed by the word of its rational weight.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(symbols `0`, `1` are bits). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length
of the encoding is the usual bit size. Every word is terminated by the symbol `2` and every list is
prefixed by its length, so the encoding is prefix-free and injective (proved in
`Solutions/verification/VDCyclePack_encodings.lean`). -/
def encWeighted (ws : List (List ℕ × ℚ)) : List OnlineCRS.Combine.Sym :=
  encWList (fun e : List ℕ × ℚ => encWList encWNat e.1 ++ encWRat e.2) ws

end VDCyclePack


