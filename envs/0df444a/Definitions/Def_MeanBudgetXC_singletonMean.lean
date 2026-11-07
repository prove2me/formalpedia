-- Prove2me | Definitions.Def_MeanBudgetXC_singletonMean
-- name    : MeanBudgetXC_singletonMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:35.311633+00:00
-- url     : https://prove2.me/theorems/1bd133a6-ee99-4884-84d6-f825e2c37a81
-- title:
--   Singleton mean $p_i$
-- statement:
--   The **singleton mean** of a system of local laws at a vertex $i$ is
--   $$p_i=\Pr[X_i=1]=\mu_{\{i\}}(1),$$
--   read on the context $\{i\}$. Consistency makes this value the same in every context containing $i$.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 1.1, p.3

import Mathlib

namespace MeanBudgetXC

variable {V : Type*} [DecidableEq V]

/-- The singleton mean `p_i = Pr[X_i = 1]` of a system of local laws, read on the context `{i}`
(Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 1.1, p.3). -/
def singletonMean (μ : (S : Finset V) → (S → Bool) → ℝ) (i : V) : ℝ :=
  μ {i} (fun _ => true)

end MeanBudgetXC


