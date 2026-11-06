-- Prove2me | Definitions.Def_ReserveLB_tokOut
-- name    : ReserveLB_tokOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:28.547484+00:00
-- url     : https://prove2.me/theorems/b83b1e90-5472-4184-9559-23f3325df9a9
-- title:
--   Words of a construction output
-- statement:
--   A construction output is a pair: the reservation lists (entry $j$ lists the machine indices reserved for job $j$) and a bit string of decoder metadata ("polynomial-size endpoint and regime metadata"). Its words are the doubly length-prefixed reservation lists, indices in binary, followed by one word of metadata bits.
--
--
--   **Formalization Note** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the four-symbol alphabet `OnlineCRS.Combine.Sym` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are written in binary and every list carries its length, so the encoding is injective and its length is the usual bit size (injectivity is proved in a verification file that is not uploaded).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Theorem 1.1, p.2 (reservations and decoder metadata)

import Mathlib
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat

namespace ReserveLB

/-- **Words of a construction output.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Theorem 1.1, p.2: the algorithm "reserves at most k distinct original machines per job";
"The output includes polynomial-size endpoint and regime metadata for the decoder."

A construction output is a pair: the reservation lists (entry `j` lists the machine indices of job
`j`) and a bit string of decoder metadata. `tokOut o` is the reservation lists, length-prefixed at
both levels with indices in binary, followed by one word holding the metadata bits.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1`
bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`,
`encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its
length, and the words contain no `3`, so the encoding is injective (decoded in
`Solutions/verification/ReserveLB_encodings.lean`). -/
def tokOut (o : List (List ℕ) × List Bool) : List (List OnlineCRS.Combine.Sym) :=
  tokList (tokList fun i => [OnlineCRS.Combine.encNat i]) o.1 ++
    [o.2.map OnlineCRS.Combine.bit]

end ReserveLB


