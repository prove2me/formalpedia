-- Prove2me | Definitions.Def_VDCyclePack_encWList
-- name    : VDCyclePack_encWList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:01.116833+00:00
-- url     : https://prove2.me/theorems/ff5d2dd5-c0c2-4b67-a5f9-d8a608419efe
-- title:
--   Length-prefixed encoding of a list
-- statement:
--   A list is encoded as the word of its length followed by the words of its entries. Since every entry word is self-delimiting, so is the list word.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 4.1, p.11

import Mathlib
import Definitions.Def_VDCyclePack_encWNat

namespace VDCyclePack

/-- **Length-prefixed encoding of a list.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript): auxiliary encoding for "an explicit list of polynomially many cycles" (Lemma 4.1, p.11).

`encWList e l` is the word of the length of `l` followed by the words `e a` of its entries.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(symbols `0`, `1` are bits). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length
of the encoding is the usual bit size. Every word is terminated by the symbol `2` and every list is
prefixed by its length, so the encoding is prefix-free and injective (proved in
`Solutions/verification/VDCyclePack_encodings.lean`). -/
def encWList {α : Type*} (e : α → List OnlineCRS.Combine.Sym) (l : List α) :
    List OnlineCRS.Combine.Sym :=
  encWNat l.length ++ l.flatMap e

end VDCyclePack


