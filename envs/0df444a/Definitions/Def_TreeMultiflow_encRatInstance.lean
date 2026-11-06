-- Prove2me | Definitions.Def_TreeMultiflow_encRatInstance
-- name    : TreeMultiflow_encRatInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:45.495806+00:00
-- url     : https://prove2.me/theorems/da4c95c6-f2cf-4f73-8f84-baf6c0635d7e
-- title:
--   Binary encoding of a rational instance
-- statement:
--   The encoding of a rational instance is the sequence of words
--   $$
--   n,\ |\text{edges}|,\ (a,b,c)\text{ for each edge},\ (s,t,w,x)\text{ for each request},
--   $$
--   separated by a separator symbol, over the four-letter alphabet $\{0,1,2,3\}$. Natural numbers are written in binary; a rational number is written as its reduced numerator (sign bit and binary absolute value), the symbol $2$, and its denominator in binary.
--
--   Polynomial time in Theorems 1.2 and 2.1 is measured in the length of this encoding, which is the usual bit size of the instance.
--
--   **Formalization Note** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`. The words contain no separator, so the encoding is injective.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Theorem 1.2, p.3 (for rationally encoded inputs … in polynomial time)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_TreeMultiflow_RatInstance

namespace TreeMultiflow

/-- **Binary encoding of a rational instance.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Theorem 1.2,
p.3: "for rationally encoded inputs, such a subset can be found in polynomial time".

`encRatInstance I` is the list of words `n`, `|edges|`, then `a, b, c` for each edge, then
`s, t, w, x` for each request, joined by the separator symbol `3`. Natural numbers are written in
binary (`OnlineCRS.Combine.encNat`), rationals as reduced numerator and denominator
(`OnlineCRS.Combine.encRat`).

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1`
bits, `2` inside a rational, `3` separator). Numbers are binary, so the length of the encoding is
the usual bit size of the instance. The words contain no `3`, so the encoding is injective (it
is decoded in `Solutions/verification/TreeMultiflow_encodings.lean`). -/
def encRatInstance (I : RatInstance) : List OnlineCRS.Combine.Sym :=
  [3].intercalate
    ([OnlineCRS.Combine.encNat I.n, OnlineCRS.Combine.encNat I.edges.length] ++
      I.edges.flatMap (fun t => [OnlineCRS.Combine.encNat t.1, OnlineCRS.Combine.encNat t.2.1,
        OnlineCRS.Combine.encNat t.2.2]) ++
      I.reqs.flatMap (fun r => [OnlineCRS.Combine.encNat r.1, OnlineCRS.Combine.encNat r.2.1,
        OnlineCRS.Combine.encRat r.2.2.1, OnlineCRS.Combine.encRat r.2.2.2]))

end TreeMultiflow


