-- Prove2me | Definitions.Def_MeanBudgetXC_rltObjective
-- name    : MeanBudgetXC_rltObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:24.35531+00:00
-- url     : https://prove2.me/theorems/b308d58e-1853-487c-b082-be183529be6c
-- title:
--   The RLT objective $J_{p,q}$
-- statement:
--   The **RLT objective** of a singleton vector $p$ and a pair array $q$ at a point $(x,y)$ is
--   $$J_{p,q}(x,y)=p\cdot x-\sum_{i<j}q_{ij}y_{ij}.$$
--   At the incidence vector of a $d$-set $S$ it equals $F_S(p,q)=p(S)-q(E(S))$.
--
--   **Formalization Note** The sum over $i<j$ is a sum over unordered pairs.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 3.4, p.13

import Mathlib
import Definitions.Def_MeanBudgetXC_Pair

namespace MeanBudgetXC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **RLT objective** `J_{p,q}(x, y) = p · x − ∑_{i<j} q_ij y_ij` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 3.4, p.13). -/
def rltObjective (p : V → ℝ) (q : Pair V → ℝ) (xy : (V → ℝ) × (Pair V → ℝ)) : ℝ :=
  ∑ i, p i * xy.1 i - ∑ e, q e * xy.2 e

end MeanBudgetXC


