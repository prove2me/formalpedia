-- Prove2me | Definitions.Def_NSWBetter_encInstEntriesCoins
-- name    : NSWBetter_encInstEntriesCoins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:53:41.731234+00:00
-- url     : https://prove2.me/theorems/f00e199c-91cd-4d17-9aba-4a1eb9a1132c
-- title:
--   Encoding of an instance, a configuration LP solution and coins
-- statement:
--   The input of the randomized algorithm of Theorem 6.1: instance, entry list of the configuration LP solution, and a coin string, in binary.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 6.1, p.36 (randomized algorithm)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_tokInst
import Definitions.Def_NSWBetter_Entry
import Definitions.Def_NSWBetter_tokEntry

namespace NSWBetter

/-- **Input of the randomized algorithm of Theorem 6.1.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 6.1, p.36: "a polynomial time algorithm that outputs a (randomized) fractional allocation z".

`encInstEntriesCoins ((I, l), w)`: the words of `I`, of the entry list `l`, and one word with the coin bits `w`, joined by `3`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its length and the words contain no `3`, so the encoding is injective (decoded in `Solutions/verification/NSWBetter_encodings.lean`). -/
def encInstEntriesCoins (x : (Inst × List Entry) × List Bool) : List OnlineCRS.Combine.Sym :=
  [3].intercalate (tokInst x.1.1 ++ ReserveLB.tokList tokEntry x.1.2 ++
    [x.2.map OnlineCRS.Combine.bit])

end NSWBetter


