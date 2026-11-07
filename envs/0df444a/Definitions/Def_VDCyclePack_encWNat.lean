-- Prove2me | Definitions.Def_VDCyclePack_encWNat
-- name    : VDCyclePack_encWNat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:43.487165+00:00
-- url     : https://prove2.me/theorems/01889ba4-d0b9-4801-a61f-d0eab43d6c89
-- title:
--   Self-delimiting binary word of a natural number
-- statement:
--   The binary representation of a natural number followed by a terminator symbol. Numbers are written in binary, so the length of an encoded input is its bit size.
--
--   **Formalization Note** Over the alphabet `OnlineCRS.Combine.Sym` $=\{0,1,2,3\}$ with Mathlib's binary encoding `OnlineCRS.Combine.encNat`; the terminator is the symbol $2$. Every encoding of the mission is proved injective in the (not uploaded) verification file.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Theorem 1.1, p.3 (polynomial time)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat

namespace VDCyclePack

/-- **Self-delimiting binary word of a natural number.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript): auxiliary encoding for "polynomial time" (Theorem 1.1, p.3).

`encWNat k` is the binary encoding of `k` followed by the terminator `2`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(symbols `0`, `1` are bits). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length
of the encoding is the usual bit size. Every word is terminated by the symbol `2` and every list is
prefixed by its length, so the encoding is prefix-free and injective (proved in
`Solutions/verification/VDCyclePack_encodings.lean`). -/
def encWNat (k : ℕ) : List OnlineCRS.Combine.Sym :=
  OnlineCRS.Combine.encNat k ++ [2]

end VDCyclePack


