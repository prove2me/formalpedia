-- Prove2me | Definitions.Def_MeanBudgetXC_rltPolytope
-- name    : MeanBudgetXC_rltPolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:49.761519+00:00
-- url     : https://prove2.me/theorems/d6c90458-e4e5-432e-a092-e781f43e9640
-- title:
--   The cardinality RLT polytope $R_{N,d}$
-- statement:
--   With $r=d-1$, the **cardinality RLT polytope** is the set of pairs $(x,y)$, with $x$ indexed by vertices and $y$ by unordered pairs, satisfying
--   $$0\le x_i\le1,\qquad \sum_i x_i=d,\qquad 0\le y_{ij}\le x_i,x_j,\qquad y_{ij}\ge x_i+x_j-1,\qquad \sum_{j\ne i}y_{ij}=rx_i\quad(i\in[N]).$$
--   For an integral candidate context, $x_i$ indicates membership and $y_{ij}=x_ix_j$ indicates joint membership.
--
--   **Formalization Note** The conditions on $y$ are imposed for every ordered pair $i\ne j$, which covers both $y_{ij}\le x_i$ and $y_{ij}\le x_j$.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 3.4, p.13

import Mathlib
import Definitions.Def_MeanBudgetXC_entry

namespace MeanBudgetXC

/-- The **cardinality RLT polytope** `R_{N,d}` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget
Transition for Local Pair Marginals*, STOC 2027 submission, manuscript sha256 882d9c71…9e76,
Section 3.4, p.13), with `r = d − 1`:
`R_{N,d} = {(x, y) : 0 ≤ x_i ≤ 1, ∑_i x_i = d, 0 ≤ y_ij ≤ x_i, x_j, y_ij ≥ x_i + x_j − 1,
∑_{j ≠ i} y_ij = r x_i (i ∈ [N])}`.

**Formalization Note** `x` is indexed by vertices and `y` by unordered pairs (`y_ij = y_ji`);
`entry y i j` reads `y_ij` for `i ≠ j` (and is `0` for `i = j`, so the degree sum may run over all
`j`). The McCormick conditions are imposed for every ordered pair `i ≠ j`, which covers both
`y_ij ≤ x_i` and `y_ij ≤ x_j`. -/
def rltPolytope (V : Type*) [Fintype V] [DecidableEq V] (d : ℕ) :
    Set ((V → ℝ) × (Pair V → ℝ)) :=
  {xy | (∀ i, 0 ≤ xy.1 i ∧ xy.1 i ≤ 1) ∧ ∑ i, xy.1 i = d ∧
    (∀ i j, i ≠ j → 0 ≤ entry xy.2 i j ∧ entry xy.2 i j ≤ xy.1 i ∧
      xy.1 i + xy.1 j - 1 ≤ entry xy.2 i j) ∧
    ∀ i, ∑ j, entry xy.2 i j = ((d : ℝ) - 1) * xy.1 i}

end MeanBudgetXC


