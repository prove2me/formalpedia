-- Prove2me | Definitions.Def_NSWBetter_tokInst
-- name    : NSWBetter_tokInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:23.795436+00:00
-- url     : https://prove2.me/theorems/a2ef661b-b197-4431-a14c-6aed186b9667
-- title:
--   Words of the binary encoding of an instance
-- statement:
--   The words of the binary encoding of an instance: the number of goods $m$ in binary, then the valuation matrix as a length-prefixed list of $n$ rows, each row a length-prefixed list of $m$ rationals (numerator and denominator in binary).
--
--   **Formalization Note** The words use the symbols $0,1,2$ only and are later joined by the separator $3$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 1.1, p.3 ("efficient": polynomial in the input size)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_NSWBetter_Inst

namespace NSWBetter

/-- **Words of a rational instance.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 1.1, p.3: "efficient" algorithm, i.e. polynomial time in the binary input size.

`tokInst I` is the word list: `m` in binary, then the list of the `n` rows (length first), each row the list of its `m` values as rationals (length first).

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its length and the words contain no `3`, so the encoding is injective (decoded in `Solutions/verification/NSWBetter_encodings.lean`). -/
def tokInst (I : Inst) : List (List OnlineCRS.Combine.Sym) :=
  OnlineCRS.Combine.encNat I.m ::
    ReserveLB.tokList (ReserveLB.tokList fun q => [OnlineCRS.Combine.encRat q])
      (List.ofFn fun i => List.ofFn (I.v i))

end NSWBetter


