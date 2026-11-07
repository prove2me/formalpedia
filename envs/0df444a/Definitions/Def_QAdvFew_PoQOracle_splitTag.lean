-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_splitTag
-- name    : QAdvFew_PoQOracle_splitTag
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:58.301962+00:00
-- url     : https://prove2.me/theorems/bc6f1404-87c5-4dbe-ac47-00d1990e2d74
-- title:
--   Reading a tag off a query
-- statement:
--   Reads a tag $1^c 0$ off the front of a string $s = 1^c 0 r$ and returns the pair $(c, r)$; the result is undefined when $s = 1^c$ has no terminating $0$.
--
--   Components and levels of an oracle are addressed by such tags. A query to level $t$ therefore has length at least $t+1$, which realizes the paper's convention that "a query to level $t$ takes at least $t$ time".
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.2.2, p. 12 (PDF p. 14); §4.1, p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- Reads a tag `1^c 0` off the front of a string and returns `(c, rest)`; `none` if the string is
`1^c` with no terminating `0` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, §3.2.2, p. 12 (PDF p. 14): "Components and levels may be
queried"; §4.1, p. 21 (PDF p. 23): `A = {A_t}`, `O = (A, B, C)`).

**Formalization Note** The tag is `encNat c = 1^c 0` (`QAlgorithms.Complexity.encNat`), so a query
to level `t` has length at least `t + 1`; this realizes "a query to level `t` takes at least `t`
time" (p. 12). -/
def splitTag : Str → Option (ℕ × Str)
  | [] => none
  | false :: s => some (0, s)
  | true :: s => (splitTag s).map (fun p => (p.1 + 1, p.2))

end QAdvFew.PoQOracle


