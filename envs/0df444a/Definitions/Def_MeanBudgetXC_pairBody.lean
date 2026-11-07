-- Prove2me | Definitions.Def_MeanBudgetXC_pairBody
-- name    : MeanBudgetXC_pairBody
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:08.080759+00:00
-- url     : https://prove2.me/theorems/766604f8-c58b-487d-8411-6db9d51b7a9b
-- title:
--   The pair body $P^{(a)}_{N,d}$
-- statement:
--   The **pair body** $P^{(a)}_{N,d}$ is the set of pair arrays $q$ arising as the pair probabilities of some consistent system of local laws of context size $d$ and activity $a$. At $a=2$ it is the paper's body $P$ (p.4: $P=P^{(2)}_{N,d}$).
--
--   **Formalization Note** The vertex set is a generic finite type $V$ with $N=|V|$.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 1.1, p.3, and Section 4, p.17

import Mathlib
import Definitions.Def_MeanBudgetXC_IsLocalSystem
import Definitions.Def_MeanBudgetXC_pairProb

namespace MeanBudgetXC

/-- The **pair body** `P^{(a)}_{N,d}` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 1.1, p.3, and Section 4, p.17): the set of pair
arrays `q` arising as the pair probabilities of some consistent system of local laws of context
size `d` and activity `a`. At `a = 2` this is the paper's `P` (p.4: `P = P^{(2)}_{N,d}`).

**Formalization Note** The vertex set is a generic finite type `V` (`N = card V`). -/
def pairBody (V : Type*) [Fintype V] [DecidableEq V] (d a : ℕ) : Set (Pair V → ℝ) :=
  {q | ∃ μ : (S : Finset V) → (S → Bool) → ℝ, IsLocalSystem d a μ ∧ ∀ e, q e = pairProb μ e}

end MeanBudgetXC


