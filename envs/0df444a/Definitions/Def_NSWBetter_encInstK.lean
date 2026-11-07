-- Prove2me | Definitions.Def_NSWBetter_encInstK
-- name    : NSWBetter_encInstK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:21.733749+00:00
-- url     : https://prove2.me/theorems/0668f1a3-4922-4c75-a38c-adea2f44bd7c
-- title:
--   Encoding of an instance with an accuracy parameter $K$ in unary
-- statement:
--   The input of the solver of Theorem 2.5: the encoding of the instance followed by the accuracy parameter $K=1/\varepsilon$ written in unary, so that polynomial time in the input length means polynomial in the input size and $1/\varepsilon$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 2.5, p.10 ("polynomial in the input size and 1/ε")

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_tokInst

namespace NSWBetter

/-- **Input of the configuration LP solver.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 2.5, p.10: "The running time of the algorithm is polynomial in the input size and 1/ε."

`encInstK (I, K)`: the words of `I`, then `K` in **unary** (`K` ones), joined by `3`. With `ε = 1/K`, a running time polynomial in this length is polynomial in the input size and `1/ε`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its length and the words contain no `3`, so the encoding is injective (decoded in `Solutions/verification/NSWBetter_encodings.lean`). -/
def encInstK (x : Inst × ℕ) : List OnlineCRS.Combine.Sym :=
  [3].intercalate (tokInst x.1 ++ [List.replicate x.2 1])

end NSWBetter


