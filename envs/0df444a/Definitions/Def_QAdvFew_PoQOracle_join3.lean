-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_join3
-- name    : QAdvFew_PoQOracle_join3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:50:05.755147+00:00
-- url     : https://prove2.me/theorems/2463fb01-c298-464d-b9dc-0444a016a5ff
-- title:
--   The triple oracle $O=(A,B,C)$
-- statement:
--   The oracle $O = (A,B,C)$ is the join with $A$ under tag $0$, $B$ under tag $1$ and $C$ under tag $2$; other tags are answered $0$.
--
--   A query $q$ to $A$ alone is the query $0q$ to $O$, so $A$-queries mean the same thing in $\mathsf{IP}^A$ and in $\mathsf{BQP}^O$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §4.1, p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_join

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The triple oracle `O = (A, B, C)` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few
Complexity Implications*, arXiv:2611.05303v1, §4.1, p. 21 (PDF p. 23)): component `A` under tag `0`,
`B` under tag `1`, `C` under tag `2`; other tags are answered `0`.

**Formalization Note** A query `q` to `A` alone (the oracle of `IP^A`, `PSPACE^A`) is the query
`0 q` to `O`; both read the same layout of `A`, so `A`-queries mean the same thing in `IP^A` and in
`BQP^O`. -/
def join3 (A B C : Oracle) : Oracle :=
  join (fun c => if c = 0 then A else if c = 1 then B else if c = 2 then C else fun _ => false)

end QAdvFew.PoQOracle


