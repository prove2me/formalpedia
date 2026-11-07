-- Prove2me | Definitions.Def_NSWBetter_encInstFrac
-- name    : NSWBetter_encInstFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:04.718449+00:00
-- url     : https://prove2.me/theorems/a23b6c4f-7539-4b4d-99fa-94bd3c1faee7
-- title:
--   Encoding of an instance with a rational fractional allocation
-- statement:
--   The input of the algorithm of Corollary 4.15: the instance and a fractional allocation given as a list of rationals (row-major), in binary.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Corollary 4.15, p.25 ("Given a fractional allocation x")

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_tokInst

namespace NSWBetter

/-- **Input of the well-behavedness test.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Corollary 4.15, p.25: "Given a fractional allocation x, there is a polynomial time algorithm …".

`encInstFrac (I, xs)`: the words of `I`, then the length-prefixed list `xs` of rationals (the matrix `x` row-major), joined by `3`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its length and the words contain no `3`, so the encoding is injective (decoded in `Solutions/verification/NSWBetter_encodings.lean`). -/
def encInstFrac (x : Inst × List ℚ) : List OnlineCRS.Combine.Sym :=
  [3].intercalate (tokInst x.1 ++ ReserveLB.tokList (fun q => [OnlineCRS.Combine.encRat q]) x.2)

end NSWBetter


