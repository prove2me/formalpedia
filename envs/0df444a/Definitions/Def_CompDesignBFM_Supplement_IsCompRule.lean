-- Prove2me | Definitions.Def_CompDesignBFM_Supplement_IsCompRule
-- name    : CompDesignBFM_Supplement_IsCompRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:03:23.923872+00:00
-- url     : https://prove2.me/theorems/f049c0e0-dfe2-4e2a-9f68-f84566759bf7
-- title:
--   Deterministic budget-feasible compensation rule
-- statement:
--   A **deterministic compensation rule** with budget $B$ is a payment rule $p$ that, for every participating set $S\subseteq N$,
--
--   1. pays every agent a nonnegative amount, $p_i(S)\ge0$;
--   2. pays nothing to agents outside $S$, $p_i(S)=0$ for $i\notin S$;
--   3. is budget feasible, $\sum_{i\in S}p_i(S)\le B$.
--
--   The rule may depend on the value function and the budget but not on the agents' costs. A randomized compensation rule is a distribution over such rules.
--
--   **Formalization Note** Cost obliviousness holds by type: the rule takes only the participating set as input.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1.2.1, p.5 (PDF 7)

import Mathlib

namespace CompDesignBFM

namespace Supplement

/-- A deterministic compensation rule with budget `B` (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1.2.1, p.5, PDF 7): for every
participating set `S` it "assigns a nonnegative payment `pᵢ(S)` to each agent `i ∈ S` and pays zero
to agents outside `S`", and it is budget feasible, `∑_(i ∈ S) pᵢ(S) ≤ B` for every `S ⊆ N`.
**Formalization Note.** The rule is a function of the participating set only, so cost obliviousness
holds by type. -/
def IsCompRule {n : ℕ} (B : ℝ) (p : Finset (Fin n) → Fin n → ℝ) : Prop :=
  (∀ S i, 0 ≤ p S i) ∧ (∀ S i, i ∉ S → p S i = 0) ∧ ∀ S, ∑ i ∈ S, p S i ≤ B

end Supplement

end CompDesignBFM


