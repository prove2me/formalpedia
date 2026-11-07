-- Prove2me | Definitions.Def_PsdPermanent_encInstance
-- name    : PsdPermanent_encInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:33.465473+00:00
-- url     : https://prove2.me/theorems/42b64caf-4e3b-44b5-9ba4-46e42ebe4819
-- title:
--   Binary encoding of a rational instance
-- statement:
--   The input of the machine is the list of binary words for $n$, for $\varepsilon$, and for the real and imaginary parts of each entry of $A$ row by row, joined by a separator symbol. Rationals are written as reduced numerator and denominator.
--
--   **Formalization Note** All $n^2$ entries are written, so the length of the encoding bounds $n$, and the denominator of $\varepsilon$ is written, so it bounds $\log(1/\varepsilon)$. The encoding is injective (checked in a sanity file).
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Theorem 9, p.9

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_PsdPermanent_RatInstance

namespace PsdPermanent

/-- **Binary encoding of a rational instance.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Theorem 9, p.9 ("polynomial in the input size, n, and log(1/ε)").

The words `n`, `eps`, then the real and the imaginary part of each entry, row by row, joined by the separator
symbol `3`. Natural numbers are written in binary (`OnlineCRS.Combine.encNat`), rationals as reduced numerator and
denominator (`OnlineCRS.Combine.encRat`).

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime` over `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1` bits, `2` inside a rational, `3`
separator). All `n²` entries are written, so the length is at least `n` and bounds the paper's `n`; the reduced
denominator of `eps` is written, so the length bounds `log(1/ε)`. The words contain no `3`, so the encoding
is injective. -/
def encInstance (I : RatInstance) : List OnlineCRS.Combine.Sym :=
  [3].intercalate
    ([OnlineCRS.Combine.encNat I.n, OnlineCRS.Combine.encRat I.eps] ++
      (List.finRange I.n).flatMap fun i => (List.finRange I.n).flatMap fun j =>
        [OnlineCRS.Combine.encRat (I.re i j), OnlineCRS.Combine.encRat (I.im i j)])

end PsdPermanent


