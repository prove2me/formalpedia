-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_truncLevels
-- name    : QAdvFew_PoQOracle_truncLevels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:29.560858+00:00
-- url     : https://prove2.me/theorems/d1f9c705-557c-40a6-9457-5fdcb750e48f
-- title:
--   A component restricted to its low levels
-- statement:
--   A component restricted to its levels at most $k$: a query $1^m0s$ with $m\le k$ is answered as by the component, and every other query by $0$. This gives the circuit inputs $(A_1,\dots,A_k)$ of Lemma 4.7.
--
--   **Formalization Note** Levels are numbered from $0$; level $0$ carries no member pair and is a harmless extra.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §4.1, p. 21 (PDF p. 23); Lemma 4.7, p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_splitTag
import Definitions.Def_QAdvFew_PoQOracle_Oracle

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- A component restricted to its levels `≤ k` (Goldin, Lombardi, Morimae, *Quantum Advantage has
Few Complexity Implications*, arXiv:2611.05303v1, §4.1, p. 21 (PDF p. 23): "`M` queries only the
oracles `{O_1, …, O_{⌊√t⌋}}`"; Lemma 4.7, p. 24 (PDF p. 26): the inputs `(A_1, …, A_{t^{2d}−1})`):
a query `1^m 0 s` with `m ≤ k` is answered as by `X`, every other query by `0`.

**Formalization Note** Levels are numbered from `0`; level `0` of every component carries no member
pair and is a harmless extra. -/
def truncLevels (k : ℕ) (X : Oracle) : Oracle := fun s =>
  match splitTag s with
  | some (m, _) => if m ≤ k then X s else false
  | none => false

end QAdvFew.PoQOracle


