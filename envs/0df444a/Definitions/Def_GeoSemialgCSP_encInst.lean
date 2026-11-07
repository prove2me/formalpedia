-- Prove2me | Definitions.Def_GeoSemialgCSP_encInst
-- name    : GeoSemialgCSP_encInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:01.258971+00:00
-- url     : https://prove2.me/theorems/b6606696-6b0b-4e5a-8ee5-dc5387515791
-- title:
--   Unary encoding of a CSP instance
-- statement:
--   An instance with $n$ variables and constraint list $C$ is encoded as a word over the two-letter alphabet $\{1,\mathrm{sep}\}$: first $n$ in unary (that many $1$'s followed by a separator), then, for each constraint in order, its $k$ variables in unary.
--
--   The encoding has length polynomial in the size of the instance, which is the size measure of NP-hardness reductions to the CSP.
--
--   **Formalization Note** The alphabet is the published `OptInapprox.MaxCut.MCSym` with its unary encoding `MCSym.unary`.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), proof of Theorem 6.1, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_GeoSemialgCSP_Inst
import Definitions.Def_OptInapprox_MaxCut_UGC

namespace GeoSemialgCSP

/-- **Encoding of an instance.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), proof of Theorem 6.1, printed p.19 (PDF
p.20) ("the reduction has polynomial size").

The instance is written over the two-letter alphabet `{1, sep}` of the published
`OptInapprox.MaxCut.MCSym`: the number of variables `n` in unary, then, for each constraint in
order, its `k` variables in unary.

**Formalization Note.** A fixed unary encoding with no padding: its length is polynomial in the
size of the instance and it carries no other information. -/
def encInst {k : ℕ} (I : Inst k) : List OptInapprox.MaxCut.MCSym :=
  OptInapprox.MaxCut.MCSym.unary I.n ++
    I.cons.flatMap fun c => (List.finRange k).flatMap fun j => OptInapprox.MaxCut.MCSym.unary (c j : ℕ)

end GeoSemialgCSP


