-- Prove2me | Definitions.Def_IncentiveFinNet_Supplement_Dominates
-- name    : IncentiveFinNet_Supplement_Dominates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:27:08.349046+00:00
-- url     : https://prove2.me/theorems/877d5827-97a9-41f4-9117-dbbcbe403fc0
-- title:
--   Domination of feasible tuples $(W,P)$
-- statement:
--   Fix a network setting with utilities $g_i(W,P) = w_i^{\top}(\mu_i - Pe_i) - \gamma_i\, w_i^{\top}\Sigma_i w_i$ (eq. (1)). For two feasible tuples $(W_1,P_1)$ and $(W_2,P_2)$ (Definition 2), $(W_2,P_2)$ **dominates** $(W_1,P_1)$ if
--
--   $$
--   g_i(W_1,P_1) \le g_i(W_2,P_2)\quad\text{for all } i\in[n],
--   $$
--
--   with at least one of these inequalities strict.
--
--   Domination is the Pareto order on utility profiles; Theorem 2 says that no feasible tuple dominates a stable point.
--
--   **Formalization Note** `Dominates S W₂ P₂ W₁ P₁` includes the feasibility of both tuples; "at least one strict" is $\exists k,\ g_k(W_1,P_1) < g_k(W_2,P_2)$.
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, §2.1, p.12 (definition of domination before Theorem 2)

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Stable

open Matrix

namespace IncentiveFinNet.Supplement

/-- **Domination**, Jalan, Chakrabarti, Sarkar, *Incentive-Aware Models of Financial Networks*,
arXiv:2212.06808v3, §2.1, p.12: "For two feasible tuples `(W₁, P₁)` and `(W₂, P₂)`, let `(W₂, P₂)`
dominate `(W₁, P₁)` if for all `i ∈ [n]`, `g_i(W₁, P₁) ≤ g_i(W₂, P₂)`, with at least one inequality
being strict."

`Dominates S W₂ P₂ W₁ P₁` says that `(W₂, P₂)` dominates `(W₁, P₁)`; both tuples are feasible
(Definition 2) and `g_i` is the utility (1).

**Formalization Note** "At least one inequality being strict" is `∃ k, g_k(W₁, P₁) < g_k(W₂, P₂)`. -/
def Dominates {n : ℕ} (S : NetworkSetting n) (W₂ P₂ W₁ P₁ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Feasible S W₁ P₁ ∧ Feasible S W₂ P₂ ∧
    (∀ i, S.utility i W₁ P₁ ≤ S.utility i W₂ P₂) ∧ ∃ k, S.utility k W₁ P₁ < S.utility k W₂ P₂

end IncentiveFinNet.Supplement


