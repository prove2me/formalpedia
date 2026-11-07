-- Prove2me | Definitions.Def_MeanBudgetXC_topSum
-- name    : MeanBudgetXC_topSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:43.076126+00:00
-- url     : https://prove2.me/theorems/e65f4d32-8b7c-4af7-8131-bbd0f3557c9a
-- title:
--   The star value $T_i(q)$
-- statement:
--   For $r=d-1$, the **star value** $T_i(q)$ is the sum of the $r$ largest pair coordinates incident to the vertex $i$, that is
--   $$T_i(q)=\max\Big\{\sum_{j\in T}q_{ij}: T\subseteq V\setminus\{i\},\ |T|=d-1\Big\}.$$
--   It is the minimum singleton lift of a pair array.
--
--   **Formalization Note** The family of $(d-1)$-subsets of $V\setminus\{i\}$ is nonempty exactly when $1\le d\le N$, and every statement of the mission assumes this. Outside that range the value is the default $0$ and is never used.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 3.2, p.11, and Section 3.4, p.13

import Mathlib
import Definitions.Def_MeanBudgetXC_entry

namespace MeanBudgetXC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **star value** `T_i(q)` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local
Pair Marginals*, STOC 2027 submission, manuscript sha256 882d9c71…9e76, Section 3.2, p.11, and
Section 3.4, p.13): the sum of the `r = d − 1` largest pair coordinates `q_ij` incident to the
vertex `i`, i.e. the maximum of `q(i, T) = ∑_{j ∈ T} q_ij` over the `(d − 1)`-element sets
`T ⊆ V \ {i}`.

**Formalization Note** The family of `(d − 1)`-subsets of `V \ {i}` is nonempty exactly when
`d − 1 ≤ card V − 1`; every statement of the mission assumes `1 ≤ d ≤ card V`. Outside that range
the value is `0` and is never used. -/
def topSum (d : ℕ) (q : Pair V → ℝ) (i : V) : ℝ :=
  if h : ((Finset.univ.erase i).powersetCard (d - 1)).Nonempty then
    ((Finset.univ.erase i).powersetCard (d - 1)).sup' h (fun T => ∑ j ∈ T, entry q i j)
  else 0

end MeanBudgetXC


