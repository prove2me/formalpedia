-- Prove2me | Definitions.Def_PCLAssort_gValue
-- name    : PCLAssort_gValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:20:52.378664+00:00
-- url     : https://prove2.me/theorems/0ccc11de-bc70-4339-a054-8752e0b9e074
-- title:
--   The upper bound $g(z)$, optimal value of LP$(z)$
-- statement:
--   For $z\in\mathbb R$, $g(z)$ is the optimal value of LP$(z)$:
--
--   $$
--   g(z)=\max\sum_{(i,j)\in E}y_{ij}\,w_{ij}(z)
--   $$
--
--   over the feasible set of LP$(z)$. It is an upper bound on $f(z)$ (step 1 of the framework of Theorem 2).
--
--   **Formalization Note** The supremum of the objective over the feasible set. For nonnegative sizes and capacity the feasible set is a nonempty polytope, and the supremum is attained.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §4.1, LP$(z)$, p.792 (PDF p.8)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_pclEdges
import Definitions.Def_PCLAssort_pclWeight
import Definitions.Def_PCLAssort_LP9Objective
import Definitions.Def_PCLAssort_LPzFeasible

namespace PCLAssort

/-- The upper bound `g(z)` = optimal value of LP(z) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §4.1, p.792):
`g(z) = max ∑_{(i,j)∈E} y_ij w_ij(z)` over the feasible set of LP(z).

**Formalization Note.** `sSup` of the objective values over the feasible set. For `0 ≤ c` and
`0 ≤ s` the set is nonempty (`x = y = 0`) and bounded (`0 ≤ y_e ≤ 1`), and the supremum is attained
(a linear function on a polytope), so it is the paper's maximum. -/
noncomputable def gValue {n : ℕ} (I : PCLInstance n) (s : Fin n → ℝ) (c z : ℝ) : ℝ :=
  sSup ((fun p => LP9Objective (pclEdges n) (pclWeight I z) p) '' LPzFeasible n s c)

end PCLAssort


