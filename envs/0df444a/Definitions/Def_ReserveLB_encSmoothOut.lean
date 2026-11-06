-- Prove2me | Definitions.Def_ReserveLB_encSmoothOut
-- name    : ReserveLB_encSmoothOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:37.968259+00:00
-- url     : https://prove2.me/theorems/a6aab62d-60e3-4c59-abf1-b336892e5463
-- title:
--   Encoding of a smoothing output
-- statement:
--   A smoothing output consists of the class list (speed $S_h$ and count $N_h$ of each class), the forward map $F$ as the list of virtual machines (class, position) of the original machines, and the parent map $G$ as one list per class of the original parents of its virtual machines. It is encoded as the three length-prefixed lists joined by the separator.
--
--
--   **Formalization Note** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the four-symbol alphabet `OnlineCRS.Combine.Sym` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are written in binary and every list carries its length, so the encoding is injective and its length is the usual bit size (injectivity is proved in a verification file that is not uploaded).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.2, p.3

import Mathlib
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat

namespace ReserveLB

/-- **Encoding of a smoothing output.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.2, p.3: virtual classes with speeds `S_h` and counts `N_h`, forward map `F` and
parent map `G`.

A smoothing output is the class list (speed `S_h`, count `N_h`), the forward map as a list of
virtual machines `(class, position)` indexed by original machine, and the parent map as one list
per class of the original parents of its virtual machines. `encSmoothOut` writes the three
length-prefixed lists, joined by the separator `3`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1`
bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`,
`encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its
length, and the words contain no `3`, so the encoding is injective (decoded in
`Solutions/verification/ReserveLB_encodings.lean`). -/
def encSmoothOut (o : List (ℚ × ℕ) × List (ℕ × ℕ) × List (List ℕ)) :
    List OnlineCRS.Combine.Sym :=
  [3].intercalate (tokList (fun a => [OnlineCRS.Combine.encRat a.1, OnlineCRS.Combine.encNat a.2]) o.1 ++
    tokList (fun a => [OnlineCRS.Combine.encNat a.1, OnlineCRS.Combine.encNat a.2]) o.2.1 ++
    tokList (tokList fun i => [OnlineCRS.Combine.encNat i]) o.2.2)

end ReserveLB


