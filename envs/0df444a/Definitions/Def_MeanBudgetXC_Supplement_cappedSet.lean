-- Prove2me | Definitions.Def_MeanBudgetXC_Supplement_cappedSet
-- name    : MeanBudgetXC_Supplement_cappedSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:07:28.946746+00:00
-- url     : https://prove2.me/theorems/58cd6922-9d26-4322-9825-ae9b2e96a945
-- title:
--   The capped feasible set $\{q\in A: 0\le q\le u\}$
-- statement:
--   For a set $A\subseteq\mathbb R^\iota$ and a cap $u\in\mathbb R^\iota$, the **capped feasible set** is
--   $$\{q\in A:\ 0\le q\le u\},$$
--   with coordinatewise order. A capacity query on $A$ optimizes over this set; the paper requires it to be nonempty for every prescribed query.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Section 1.3, p.5

import Mathlib

namespace MeanBudgetXC.Supplement

/-- The **capped feasible set** `{q ∈ A : 0 ≤ q ≤ u}` of a set `A ⊆ ℝ^ι` under the cap `u`
(Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 1.3, p.5: "each query caps the output q directly by adding the M
inequalities qij ≤ uij"; the capped set includes `q ≥ 0`, as in the definition of `V_A(u)`).
The orders are coordinatewise. -/
def cappedSet {ι : Type*} (A : Set (ι → ℝ)) (u : ι → ℝ) : Set (ι → ℝ) :=
  {q | q ∈ A ∧ 0 ≤ q ∧ q ≤ u}

end MeanBudgetXC.Supplement


