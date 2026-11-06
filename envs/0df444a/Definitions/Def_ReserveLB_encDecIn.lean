-- Prove2me | Definitions.Def_ReserveLB_encDecIn
-- name    : ReserveLB_encDecIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:24.89191+00:00
-- url     : https://prove2.me/theorems/a7197a15-b03b-45d1-a051-aa067d9f5db2
-- title:
--   Encoding of the decoder's input
-- statement:
--   After the sizes are revealed, the decoder reads the instance, the construction output and the realized size list (entry $j$ the size of job $j$). Its input is encoded as the words of these three parts joined by the separator.
--
--
--   **Formalization Note** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the four-symbol alphabet `OnlineCRS.Combine.Sym` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are written in binary and every list carries its length, so the encoding is injective and its length is the usual bit size (injectivity is proved in a verification file that is not uploaded).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Theorem 1.1, p.2; proof of Theorem 1.1, p.13

import Mathlib
import Definitions.Def_ReserveLB_Inst
import Definitions.Def_ReserveLB_tokInst
import Definitions.Def_ReserveLB_tokOut
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_OnlineCRS_Combine_encRat

namespace ReserveLB

/-- **Encoding of the decoder's input.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Theorem 1.1, p.2: "Construction and recourse are polynomial in the full binary input";
proof of Theorem 1.1, p.13.

The decoder reads the instance, the construction output and the realized sizes (entry `j` is the
size of job `j`). `encDecIn ((I, o), x)` is the words of `I`, of `o`, and the length-prefixed list
of sizes, joined by the separator `3`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1`
bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`,
`encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its
length, and the words contain no `3`, so the encoding is injective (decoded in
`Solutions/verification/ReserveLB_encodings.lean`). -/
def encDecIn (x : (Inst × (List (List ℕ) × List Bool)) × List ℚ) :
    List OnlineCRS.Combine.Sym :=
  [3].intercalate (tokInst x.1.1 ++ tokOut x.1.2 ++
    tokList (fun q => [OnlineCRS.Combine.encRat q]) x.2)

end ReserveLB


