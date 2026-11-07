-- Prove2me | Definitions.Def_MeanBudgetXC_coverVec
-- name    : MeanBudgetXC_coverVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:38.029472+00:00
-- url     : https://prove2.me/theorems/ec6be429-6307-49dd-b8b3-ff48e8bf7ed0
-- title:
--   The coverage vector $c_S$
-- statement:
--   For a graph $Q$ with edge set $E$ and a vertex set $S$, the **coverage vector** $c_S\in\mathbb{R}^E$ is
--   $$c_S(e)=\mathbf 1[e\cap S\neq\emptyset],$$
--   the indicator that $S$ covers the edge $e$.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.1, p.17

import Mathlib

namespace MeanBudgetXC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **coverage vector** `c_S ∈ ℝ^E`, `c_S(e) = 1[e ∩ S ≠ ∅]`: the indicator that the vertex
set `S` covers the edge `e` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 4.1, p.17). -/
def coverVec (Q : SimpleGraph V) (S : Finset V) : Q.edgeSet → ℝ :=
  fun e => if ∃ v ∈ S, v ∈ e.1 then 1 else 0

end MeanBudgetXC


