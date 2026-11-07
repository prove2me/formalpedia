-- Prove2me | Definitions.Def_MeanBudgetXC_restrictE
-- name    : MeanBudgetXC_restrictE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:55.37928+00:00
-- url     : https://prove2.me/theorems/f516a404-4170-4b7a-b4ef-34d82813db78
-- title:
--   Restriction of a pair array to the edges of a graph
-- statement:
--   For a graph $Q$ on the vertex set, with edge set $E$, the **restriction** of a pair array $q$ is $x=(q_e)_{e\in E}$. Edges of a simple graph are pairs of distinct vertices, so they are pair coordinates.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.1, p.17

import Mathlib
import Definitions.Def_MeanBudgetXC_Pair

namespace MeanBudgetXC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The restriction `x = (q_e)_{e ∈ E}` of a pair array `q` to the edges `E` of a graph `Q` on `V`
(Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 4.1, p.17). Edges of a simple graph are
pairs of distinct vertices, so they are pair coordinates. -/
def restrictE (Q : SimpleGraph V) (q : Pair V → ℝ) : Q.edgeSet → ℝ :=
  fun e => q ⟨e.1, Q.not_isDiag_of_mem_edgeSet e.2⟩

end MeanBudgetXC


