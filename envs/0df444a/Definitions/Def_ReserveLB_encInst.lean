-- Prove2me | Definitions.Def_ReserveLB_encInst
-- name    : ReserveLB_encInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:23.829633+00:00
-- url     : https://prove2.me/theorems/07f3a052-e33b-4299-8306-0adab6922d41
-- title:
--   Binary encoding of an instance
-- statement:
--   The **binary encoding** of an instance is its words (the cap, the speed list and the law list, numbers in binary) joined by the separator symbol $3$. Its length is the bit size of the instance, the measure of "polynomial in the full binary input" in Theorem 1.1.
--
--
--   **Formalization Note** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the four-symbol alphabet `OnlineCRS.Combine.Sym` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are written in binary and every list carries its length, so the encoding is injective and its length is the usual bit size (injectivity is proved in a verification file that is not uploaded).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 1, p.2; Theorem 1.1, p.2

import Mathlib
import Definitions.Def_ReserveLB_Inst
import Definitions.Def_ReserveLB_tokInst

namespace ReserveLB

/-- **Binary encoding of a rational instance.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 1, p.2: "the complete input is binary encoded"; Theorem 1.1: "polynomial in the
full binary input".

`encInst I` joins the words `tokInst I` by the separator `3`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1`
bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`,
`encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its
length, and the words contain no `3`, so the encoding is injective (decoded in
`Solutions/verification/ReserveLB_encodings.lean`). -/
def encInst (I : Inst) : List OnlineCRS.Combine.Sym :=
  [3].intercalate (tokInst I)

end ReserveLB


