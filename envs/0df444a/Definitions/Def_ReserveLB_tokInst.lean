-- Prove2me | Definitions.Def_ReserveLB_tokInst
-- name    : ReserveLB_tokInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:23.792864+00:00
-- url     : https://prove2.me/theorems/82ff777b-ce6f-46fa-8a24-c4cc8fe12297
-- title:
--   Words of a rational instance
-- statement:
--   The words of an instance are: the cap $k$ in binary; the length-prefixed list of speeds (each a rational, numerator and denominator in binary); and the length-prefixed list of laws, each law a length-prefixed list of (value, probability) pairs.
--
--
--   **Formalization Note** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the four-symbol alphabet `OnlineCRS.Combine.Sym` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are written in binary and every list carries its length, so the encoding is injective and its length is the usual bit size (injectivity is proved in a verification file that is not uploaded).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 1, p.2 (the complete input is binary encoded)

import Mathlib
import Definitions.Def_ReserveLB_Inst
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat

namespace ReserveLB

/-- **Words of a rational instance.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 1, p.2: "the complete input is binary encoded".

`tokInst I` is the word list: `k` in binary, then the speed list (length, then each speed as a
rational), then the law list (length, then for each job the length of its law and the
value and probability of each atom).

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1`
bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`,
`encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its
length, and the words contain no `3`, so the encoding is injective (decoded in
`Solutions/verification/ReserveLB_encodings.lean`). -/
def tokInst (I : Inst) : List (List OnlineCRS.Combine.Sym) :=
  OnlineCRS.Combine.encNat I.k ::
    (tokList (fun q => [OnlineCRS.Combine.encRat q]) I.speeds ++
      tokList (tokList fun a : ℚ × ℚ =>
        [OnlineCRS.Combine.encRat a.1, OnlineCRS.Combine.encRat a.2]) I.laws)

end ReserveLB


