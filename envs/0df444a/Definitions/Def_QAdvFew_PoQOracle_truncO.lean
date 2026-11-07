-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_truncO
-- name    : QAdvFew_PoQOracle_truncO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:42.083673+00:00
-- url     : https://prove2.me/theorems/0dcad551-89d6-4734-a16e-8f479fa9adfb
-- title:
--   The truncated oracle $\mathcal O_{\le k}$
-- statement:
--   The joined oracle of the levels at most $k$ of a triple $(A,B,C)$, which is the oracle "$(\mathcal O_1,\dots,\mathcal O_k)$" that a machine in $S_t$ queries for $k=\lfloor\sqrt t\rfloor$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §4.1, pp. 21–22 (PDF pp. 23–24)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_truncLevels
import Definitions.Def_QAdvFew_PoQOracle_join3

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The joined oracle `O_{≤k} = (A_{≤k}, B_{≤k}, C_{≤k})` of the levels `≤ k` of a triple (Goldin,
Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §4.1,
pp. 21–22 (PDF pp. 23–24): "queries only the oracles `(O_1, …, O_{⌊√t⌋})`"). -/
def truncO (k : ℕ) (ABC : Oracle × Oracle × Oracle) : Oracle :=
  join3 (truncLevels k ABC.1) (truncLevels k ABC.2.1) (truncLevels k ABC.2.2)

end QAdvFew.PoQOracle


