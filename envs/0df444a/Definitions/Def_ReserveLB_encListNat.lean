-- Prove2me | Definitions.Def_ReserveLB_encListNat
-- name    : ReserveLB_encListNat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:41.534603+00:00
-- url     : https://prove2.me/theorems/b74a3d38-6a9c-4d3e-8b2a-7a58606a7528
-- title:
--   Encoding of a list of machine indices
-- statement:
--   A list of machine indices (the decoder's output, one machine per job) is encoded as its length and entries in binary, joined by the separator.
--
--
--   **Formalization Note** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the four-symbol alphabet `OnlineCRS.Combine.Sym` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are written in binary and every list carries its length, so the encoding is injective and its length is the usual bit size (injectivity is proved in a verification file that is not uploaded).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), proof of Theorem 1.1, p.13

import Mathlib
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_OnlineCRS_Combine_encNat

namespace ReserveLB

/-- **Encoding of a list of machine indices.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), proof of Theorem 1.1, p.13: the decoder's output, one machine per original.

`encListNat l` is the length of `l` and its entries in binary, joined by the separator `3`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1`
bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`,
`encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its
length, and the words contain no `3`, so the encoding is injective (decoded in
`Solutions/verification/ReserveLB_encodings.lean`). -/
def encListNat (l : List ℕ) : List OnlineCRS.Combine.Sym :=
  [3].intercalate (tokList (fun i => [OnlineCRS.Combine.encNat i]) l)

end ReserveLB


