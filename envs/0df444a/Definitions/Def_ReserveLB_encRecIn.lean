-- Prove2me | Definitions.Def_ReserveLB_encRecIn
-- name    : ReserveLB_encRecIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:24.954734+00:00
-- url     : https://prove2.me/theorems/ed09187b-0d5a-418c-ab6a-3d6684483bfa
-- title:
--   Encoding of a recourse input
-- statement:
--   A recourse input consists of the speed list, the size list and the reservation lists; it is encoded as the three length-prefixed lists joined by the separator.
--
--
--   **Formalization Note** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the four-symbol alphabet `OnlineCRS.Combine.Sym` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are written in binary and every list carries its length, so the encoding is injective and its length is the usual bit size (injectivity is proved in a verification file that is not uploaded).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.1, p.3; Section 6.2, p.13

import Mathlib
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat

namespace ReserveLB

/-- **Encoding of a recourse input.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.1, p.3: "polynomial recourse"; Section 6.2, p.13: "For recourse, clear rational
capacities and use exact max flow".

A recourse input is the speed list, the size list and the reservation lists. `encRecIn` writes the
three length-prefixed lists, joined by the separator `3`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1`
bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`,
`encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its
length, and the words contain no `3`, so the encoding is injective (decoded in
`Solutions/verification/ReserveLB_encodings.lean`). -/
def encRecIn (x : List ℚ × List ℚ × List (List ℕ)) : List OnlineCRS.Combine.Sym :=
  [3].intercalate (tokList (fun q => [OnlineCRS.Combine.encRat q]) x.1 ++
    tokList (fun q => [OnlineCRS.Combine.encRat q]) x.2.1 ++
    tokList (tokList fun i => [OnlineCRS.Combine.encNat i]) x.2.2)

end ReserveLB


