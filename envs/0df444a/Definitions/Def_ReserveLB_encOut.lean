-- Prove2me | Definitions.Def_ReserveLB_encOut
-- name    : ReserveLB_encOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:27.184913+00:00
-- url     : https://prove2.me/theorems/bcea0970-0219-466b-8074-d7cb117741bd
-- title:
--   Encoding of a construction output
-- statement:
--   The construction output (reservation lists and decoder metadata) is encoded as its words joined by the separator.
--
--
--   **Formalization Note** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the four-symbol alphabet `OnlineCRS.Combine.Sym` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are written in binary and every list carries its length, so the encoding is injective and its length is the usual bit size (injectivity is proved in a verification file that is not uploaded).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_ReserveLB_tokOut

namespace ReserveLB

/-- **Encoding of a construction output.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Theorem 1.1, p.2: "The output includes polynomial-size endpoint and regime metadata for
the decoder."

`encOut o` joins the words `tokOut o` by the separator `3`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1`
bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`,
`encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its
length, and the words contain no `3`, so the encoding is injective (decoded in
`Solutions/verification/ReserveLB_encodings.lean`). -/
def encOut (o : List (List ℕ) × List Bool) : List OnlineCRS.Combine.Sym :=
  [3].intercalate (tokOut o)

end ReserveLB


