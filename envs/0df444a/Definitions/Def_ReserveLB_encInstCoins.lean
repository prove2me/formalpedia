-- Prove2me | Definitions.Def_ReserveLB_encInstCoins
-- name    : ReserveLB_encInstCoins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:43.379208+00:00
-- url     : https://prove2.me/theorems/66ff230d-ecab-432e-8299-495fc34f0c14
-- title:
--   Encoding of an instance with construction coins
-- statement:
--   The input of the randomized construction is the instance together with a string of fair coins drawn before the sizes. It is encoded as the words of the instance followed by one word holding the coin bits, joined by the separator.
--
--
--   **Formalization Note** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the four-symbol alphabet `OnlineCRS.Combine.Sym` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are written in binary and every list carries its length, so the encoding is injective and its length is the usual bit size (injectivity is proved in a verification file that is not uploaded).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Theorem 1.1, p.2; Section 6.2, p.13

import Mathlib
import Definitions.Def_ReserveLB_Inst
import Definitions.Def_ReserveLB_tokInst
import Definitions.Def_OnlineCRS_Combine_bit

namespace ReserveLB

/-- **Encoding of an instance together with construction coins.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Theorem 1.1, p.2: "Construction coins are independent of future sizes"; Section 6.2, p.13:
"Pre-size randomness is bounded by O(nk log(m′ + 1) + (n + m′) log(m′ + 1))".

`encInstCoins (I, w)` is the words of `I` followed by one word holding the coin bits `w`, joined by
the separator `3`. The construction is a deterministic function of this input.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1`
bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`,
`encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its
length, and the words contain no `3`, so the encoding is injective (decoded in
`Solutions/verification/ReserveLB_encodings.lean`). -/
def encInstCoins (x : Inst × List Bool) : List OnlineCRS.Combine.Sym :=
  [3].intercalate (tokInst x.1 ++ [x.2.map OnlineCRS.Combine.bit])

end ReserveLB


