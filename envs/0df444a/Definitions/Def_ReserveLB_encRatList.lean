-- Prove2me | Definitions.Def_ReserveLB_encRatList
-- name    : ReserveLB_encRatList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:24.941669+00:00
-- url     : https://prove2.me/theorems/adf9c0b7-1bf3-4693-84a6-598c104d452b
-- title:
--   Encoding of a list of rationals
-- statement:
--   A list of rationals (the speed list, input of Lemma 2.2) is encoded as its length and its entries (numerator and denominator in binary), joined by the separator.
--
--
--   **Formalization Note** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the four-symbol alphabet `OnlineCRS.Combine.Sym` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are written in binary and every list carries its length, so the encoding is injective and its length is the usual bit size (injectivity is proved in a verification file that is not uploaded).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.2, p.3

import Mathlib
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_OnlineCRS_Combine_encRat

namespace ReserveLB

/-- **Encoding of a list of rationals.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.2, p.3: "In polynomial bit time one can construct …" from the speeds.

`encRatList l` is the length of `l` and its entries as rationals, joined by the separator `3`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1`
bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`,
`encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its
length, and the words contain no `3`, so the encoding is injective (decoded in
`Solutions/verification/ReserveLB_encodings.lean`). -/
def encRatList (l : List ℚ) : List OnlineCRS.Combine.Sym :=
  [3].intercalate (tokList (fun q => [OnlineCRS.Combine.encRat q]) l)

end ReserveLB


