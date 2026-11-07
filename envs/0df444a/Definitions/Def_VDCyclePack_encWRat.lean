-- Prove2me | Definitions.Def_VDCyclePack_encWRat
-- name    : VDCyclePack_encWRat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:45.092658+00:00
-- url     : https://prove2.me/theorems/5cbd691f-2e97-47a2-a949-9cb33bc317e9
-- title:
--   Self-delimiting word of a rational number
-- statement:
--   The encoding of a rational number (sign, binary reduced numerator, separator, binary denominator) followed by a terminator symbol.
--
--   **Formalization Note** `OnlineCRS.Combine.encRat` followed by the symbol $2$.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 4.1, p.11, and Theorem 4.2, p.12

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encRat

namespace VDCyclePack

/-- **Self-delimiting word of a rational number.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript): auxiliary encoding for "positive rational weights" (Lemma 4.1, p.11; Theorem 4.2, p.12).

`encWRat q` is `OnlineCRS.Combine.encRat q` (sign bit, binary numerator, `2`, binary denominator)
followed by the terminator `2`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(symbols `0`, `1` are bits). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length
of the encoding is the usual bit size. Every word is terminated by the symbol `2` and every list is
prefixed by its length, so the encoding is prefix-free and injective (proved in
`Solutions/verification/VDCyclePack_encodings.lean`). -/
def encWRat (q : ℚ) : List OnlineCRS.Combine.Sym :=
  OnlineCRS.Combine.encRat q ++ [2]

end VDCyclePack


