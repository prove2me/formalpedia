-- Prove2me | Definitions.Def_MeanBudgetXC_entry
-- name    : MeanBudgetXC_entry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:40.92996+00:00
-- url     : https://prove2.me/theorems/ee569aba-84ad-44af-a436-46d5612128b3
-- title:
--   The entry $q_{ij}$ of a pair array
-- statement:
--   For a pair array $q$ and two vertices $i,j$, the **entry** $q_{ij}$ is the value of $q$ at the unordered pair $\{i,j\}$ when $i\neq j$, and $0$ when $i=j$. It is symmetric in $i$ and $j$, as on p.15 of the paper ("the same value used in either order").
--
--   It lets stars and degrees be written as sums over vertices: $q(i,T)=\sum_{j\in T}q_{ij}$ and $\deg_q(i)=\sum_{j\ne i}q_{ij}$.
--
--   **Formalization Note** The value $0$ at $i=j$ is a convention, so that a sum over all $j$ equals the sum over $j\neq i$. The paper has no diagonal coordinates.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 3.1, p.10

import Mathlib
import Definitions.Def_MeanBudgetXC_Pair

namespace MeanBudgetXC

variable {V : Type*} [DecidableEq V]

/-- The entry `q_ij` of a pair array `q` at two vertices `i, j` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 3.1, p.10), with the
convention `q_ii = 0`. It is symmetric, `q_ij = q_ji`, as in the paper ("the same value used in
either order", p.15). -/
def entry (q : Pair V → ℝ) (i j : V) : ℝ :=
  if h : i = j then 0 else q ⟨s(i, j), Sym2.mk_isDiag_iff.not.mpr h⟩

end MeanBudgetXC


