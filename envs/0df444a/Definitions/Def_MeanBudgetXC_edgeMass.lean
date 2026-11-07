-- Prove2me | Definitions.Def_MeanBudgetXC_edgeMass
-- name    : MeanBudgetXC_edgeMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:25.546127+00:00
-- url     : https://prove2.me/theorems/ced8e209-944c-4929-8eff-80891defe14e
-- title:
--   The pair mass $q(E(S))$ of a vertex set
-- statement:
--   For a pair array $q$ and a vertex set $S$, the **pair mass** of $S$ is
--   $$q(E(S))=\sum_{\{i,j\}\subseteq S}q_{ij}.$$
--
--   It appears in the empty-atom value $H(S)=1-p(S)+q(E(S))$ and in the context objective.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 3.1, p.10

import Mathlib
import Definitions.Def_MeanBudgetXC_Pair

namespace MeanBudgetXC

variable {V : Type*} [DecidableEq V]

/-- The pair mass `q(E(S)) = ∑_{{i,j} ⊆ S} q_ij` of a set `S` of vertices (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 3.1, p.10). -/
def edgeMass [Fintype V] (q : Pair V → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e : Pair V => e.1.toFinset ⊆ S), q e

end MeanBudgetXC


