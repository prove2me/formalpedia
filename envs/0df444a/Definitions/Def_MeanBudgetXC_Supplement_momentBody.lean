-- Prove2me | Definitions.Def_MeanBudgetXC_Supplement_momentBody
-- name    : MeanBudgetXC_Supplement_momentBody
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:09:25.587418+00:00
-- url     : https://prove2.me/theorems/bd76dbb0-0dce-423a-9bb6-ca4444a353ef
-- title:
--   The aggregate-moment body $K^{\mathrm{mom}}_{N,d,a}$
-- statement:
--   The **aggregate-moment body** $K^{\mathrm{mom}}_{N,d,a}$ is the set of pair arrays $q$ arising as the pair probabilities of a consistent system of local laws of context size $d$ and activity $a$ whose aggregate moment satisfies
--   $$\Big(\sum_ip_i,\ W(q)\Big)\in M_a,\qquad W(q)=\sum_{i<j}q_{ij}.$$
--   The aggregate constraint is imposed on the same system before the singleton means are projected out. It strengthens the mean budget of $P^{(a;B)}_{N,d}$ by every valid linear inequality in the two aggregate masses.
--
--   **Formalization Note** The vertex set is a generic finite type, instantiated at `Fin N`; the paper defines $M_a$ for $2\le a\le N$, the range in which it is used.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Section 6, p.29

import Mathlib
import Definitions.Def_MeanBudgetXC_IsLocalSystem
import Definitions.Def_MeanBudgetXC_pairProb
import Definitions.Def_MeanBudgetXC_singletonMean
import Definitions.Def_MeanBudgetXC_Supplement_momentPolygon

namespace MeanBudgetXC.Supplement

/-- The **aggregate-moment body** `K^mom_{N,d,a}` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 6, p.29): the pair projection of coherent activity-`a` local laws of context size `d`
after imposing `(∑_i p_i, W(q)) ∈ M_a` on the same system, where `W(q) = ∑_{i<j} q_ij`. Like the
budget of `budgetBody`, the aggregate constraint is imposed before the singleton means are
projected out.

**Formalization Note** The vertex set is a generic finite type `V` (`N = card V`); the paper
defines `M_a` for `2 ≤ a ≤ N`, and every statement uses it in that range. -/
def momentBody (V : Type*) [Fintype V] [DecidableEq V] (d a : ℕ) : Set (Pair V → ℝ) :=
  {q | ∃ μ : (S : Finset V) → (S → Bool) → ℝ, IsLocalSystem d a μ ∧ (∀ e, q e = pairProb μ e) ∧
    (∑ i, singletonMean μ i, ∑ e, q e) ∈ momentPolygon a}

end MeanBudgetXC.Supplement


