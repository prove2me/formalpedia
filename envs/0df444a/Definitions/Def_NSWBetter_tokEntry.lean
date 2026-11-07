-- Prove2me | Definitions.Def_NSWBetter_tokEntry
-- name    : NSWBetter_tokEntry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:33.794568+00:00
-- url     : https://prove2.me/theorems/81637ebc-f776-43a7-a309-ec5067e041ce
-- title:
--   Words of an entry
-- statement:
--   The words of an entry $(i,S,q)$: $i$ in binary, then the length-prefixed list of the goods of $S$, then $q$ as numerator and denominator in binary.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 2.5, p.10

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_NSWBetter_Entry

namespace NSWBetter

/-- **Words of an entry.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 2.5, p.10.

`tokEntry (i, S, q)`: `i` in binary, the length-prefixed list of the goods of `S` in binary, and `q` as a rational.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its length and the words contain no `3`, so the encoding is injective (decoded in `Solutions/verification/NSWBetter_encodings.lean`). -/
def tokEntry (e : Entry) : List (List OnlineCRS.Combine.Sym) :=
  OnlineCRS.Combine.encNat e.1 ::
    (ReserveLB.tokList (fun g => [OnlineCRS.Combine.encNat g]) e.2.1 ++
      [OnlineCRS.Combine.encRat e.2.2])

end NSWBetter


