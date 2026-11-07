-- Prove2me | Definitions.Def_MeanBudgetXC_pairProb
-- name    : MeanBudgetXC_pairProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:20.110946+00:00
-- url     : https://prove2.me/theorems/9226020f-5d4c-489e-a4ac-d1129ce3d047
-- title:
--   Pair probability $q_{ij}$
-- statement:
--   The **pair probability** of a system of local laws at a pair $\{i,j\}$ is
--   $$q_{ij}=\Pr[X_i=X_j=1]=\mu_{\{i,j\}}(1,1),$$
--   read on the context $\{i,j\}$. Consistency makes this value the same in every context containing both vertices.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 1.1, p.3

import Mathlib
import Definitions.Def_MeanBudgetXC_Pair

namespace MeanBudgetXC

variable {V : Type*} [DecidableEq V]

/-- The pair probability `q_ij = Pr[X_i = X_j = 1]` of a system of local laws, read on the
context `{i, j}` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 1.1, p.3). -/
def pairProb (μ : (S : Finset V) → (S → Bool) → ℝ) (e : Pair V) : ℝ :=
  μ e.1.toFinset (fun _ => true)

end MeanBudgetXC


