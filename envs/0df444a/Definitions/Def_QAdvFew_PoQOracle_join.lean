-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_join
-- name    : QAdvFew_PoQOracle_join
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:00.977195+00:00
-- url     : https://prove2.me/theorems/5ebfe299-35da-403d-8da0-e70ddf2af466
-- title:
--   Join of a sequence of oracles
-- statement:
--   The **join** of oracles $(O_c)_{c\in\mathbb N}$ answers the query $1^c 0 s$ by $O_c(s)$, and answers $0$ on a query without a complete tag.
--
--   The same join is used for the levels of one component, as in $A = \{A_t\}_t$, and for the components of a tuple.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.2.3, p. 12 (PDF p. 14); §4.1, p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Oracle
import Definitions.Def_QAdvFew_PoQOracle_splitTag

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The join of a sequence of oracles (Goldin, Lombardi, Morimae, *Quantum Advantage has Few
Complexity Implications*, arXiv:2611.05303v1, §3.2.3, p. 12 (PDF p. 14): "multiple oracles may be
listed in a superscript"; §4.1, p. 21 (PDF p. 23): `A = {A_t}_{t∈ℕ}`): the query `1^c 0 s` is answered
by `Os c` on `s`; a query without a complete tag is answered `0`.

**Formalization Note** The same join serves for the levels of one component (`A = join (fun t => A_t)`)
and for the components of a tuple of oracles (`join3`). -/
def join (Os : ℕ → Oracle) : Oracle := fun s =>
  match splitTag s with
  | some (c, r) => Os c r
  | none => false

end QAdvFew.PoQOracle


