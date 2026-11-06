-- Prove2me | Definitions.Def_ReserveLB_tokList
-- name    : ReserveLB_tokList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:14.169473+00:00
-- url     : https://prove2.me/theorems/74354932-a6b2-46f6-ba37-78203532e7a9
-- title:
--   Length-prefixed word list
-- statement:
--   An auxiliary encoding: a list $(a_1, \dots, a_r)$ is written as the binary word of its length $r$, followed by the words of $a_1, \dots, a_r$ in order. The words are later joined by a separator symbol.
--
--
--   **Formalization Note** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the four-symbol alphabet `OnlineCRS.Combine.Sym` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are written in binary and every list carries its length, so the encoding is injective and its length is the usual bit size (injectivity is proved in a verification file that is not uploaded).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 1, p.2 (binary input)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat

namespace ReserveLB

/-- **Length-prefixed list of words.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 1, p.2: "the complete input is binary encoded"; Section 6.2, p.13.

`tokList f l` is the word list `encNat |l|`, followed by the words `f a` of each element `a` of `l`
in order. The words are later joined by the separator `3`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1`
bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`,
`encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its
length, and the words contain no `3`, so the encoding is injective (decoded in
`Solutions/verification/ReserveLB_encodings.lean`). -/
def tokList {α : Type*} (f : α → List (List OnlineCRS.Combine.Sym)) (l : List α) :
    List (List OnlineCRS.Combine.Sym) :=
  OnlineCRS.Combine.encNat l.length :: l.flatMap f

end ReserveLB


