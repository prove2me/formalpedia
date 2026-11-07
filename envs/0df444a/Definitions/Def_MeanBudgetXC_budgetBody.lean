-- Prove2me | Definitions.Def_MeanBudgetXC_budgetBody
-- name    : MeanBudgetXC_budgetBody
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:14.601763+00:00
-- url     : https://prove2.me/theorems/ae0df827-30ac-4eac-ad1b-b219f0fe213f
-- title:
--   The budgeted pair body $P^{(a;B)}_{N,d}$
-- statement:
--   The **budgeted pair body** $P^{(a;B)}_{N,d}$ is the set of pair arrays $q$ arising as the pair probabilities of a consistent system of local laws of context size $d$ and activity $a$ whose singleton means satisfy the mean budget
--   $$\sum_i p_i\le B.$$
--   The budget is imposed on the same system that produces $q$, before the singleton means are projected out. At $a=2$ this is the paper's body $P_B$ (p.4: $P_B=P^{(2;B)}_{N,d}$).
--
--   **Formalization Note** The vertex set is a generic finite type $V$ with $N=|V|$.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 1.1, p.3, and Section 4, p.17

import Mathlib
import Definitions.Def_MeanBudgetXC_pairBody
import Definitions.Def_MeanBudgetXC_singletonMean

namespace MeanBudgetXC

/-- The **budgeted pair body** `P^{(a;B)}_{N,d}` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget
Transition for Local Pair Marginals*, STOC 2027 submission, manuscript sha256 882d9c71…9e76,
Section 1.1, p.3, and Section 4, p.17): the pair arrays `q` arising from a consistent system of
local laws of context size `d` and activity `a` whose singleton means satisfy the mean budget
`∑_i p_i ≤ B`. The budget is imposed on the same system that produces `q`, before the singleton
means are projected out. At `a = 2` this is the paper's `P_B` (p.4: `P_B = P^{(2;B)}_{N,d}`). -/
def budgetBody (V : Type*) [Fintype V] [DecidableEq V] (d a : ℕ) (B : ℝ) : Set (Pair V → ℝ) :=
  {q | ∃ μ : (S : Finset V) → (S → Bool) → ℝ, IsLocalSystem d a μ ∧ (∀ e, q e = pairProb μ e) ∧
    ∑ i, singletonMean μ i ≤ B}

end MeanBudgetXC


