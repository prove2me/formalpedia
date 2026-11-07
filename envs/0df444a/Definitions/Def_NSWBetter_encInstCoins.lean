-- Prove2me | Definitions.Def_NSWBetter_encInstCoins
-- name    : NSWBetter_encInstCoins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:43.246206+00:00
-- url     : https://prove2.me/theorems/8b71c73a-8cd7-4cac-854d-56aadd5d356e
-- title:
--   Encoding of an instance together with a coin string
-- statement:
--   The input of a randomized algorithm: the words of the instance $I$ followed by one word containing the coin string $w\in\{0,1\}^*$, joined by the separator $3$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 1.1, p.3 ("randomized")

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_tokInst

namespace NSWBetter

/-- **Encoding of an instance with the random coins.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 1.1, p.3: "efficient randomized … algorithm".

`encInstCoins (I, w)` is the words of `I` followed by one word holding the coin bits `w`, joined by `3`. A randomized algorithm is a deterministic polynomial-time map of this input.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its length and the words contain no `3`, so the encoding is injective (decoded in `Solutions/verification/NSWBetter_encodings.lean`). -/
def encInstCoins (x : Inst × List Bool) : List OnlineCRS.Combine.Sym :=
  [3].intercalate (tokInst x.1 ++ [x.2.map OnlineCRS.Combine.bit])

end NSWBetter


