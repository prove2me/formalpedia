-- Prove2me | Definitions.Def_ChoiceCDLP_Efficient_frontier
-- name    : ChoiceCDLP_Efficient_frontier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T07:12:22.897034+00:00
-- url     : https://prove2.me/theorems/262e6b35-8ff1-40d3-a7e1-f93dc1ae7922
-- title:
--   The frontier function R̄(q): best mixed revenue with expected consumption at most q
-- statement:
--   **The efficient-frontier function.** For a capacity-consumption level $q \in [0,1]^m$ define
--   $$\bar R(q) = \max_{\alpha} \Big\{ \sum_S \alpha(S) R(S) \;:\; \sum_S \alpha(S) Q(S) \le q,\ \ \sum_S \alpha(S) = 1,\ \ \alpha(S) \ge 0\ \ \forall S \subseteq N \Big\},$$
--   the largest expected revenue that a mixture of offer sets can earn while its expected consumption on every leg stays below $q$.
--
--   **Formalization Note.** $\bar R(q)$ is defined as the supremum (`sSup`) of the attainable values $\sum_S \alpha(S)R(S)$. For $q \ge 0$ the set is nonempty: the weight vector concentrated on the empty offer set is feasible, since $P_j(\emptyset) = 0$ for all $j$ gives $Q(\emptyset) = 0$. It is bounded above by $\max_S R(S)$. Hence on $[0,1]^m$ the supremum is a genuine maximum, and the junk value of `sSup` on empty sets never occurs there.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 307, Appendix, proof of Proposition 3 (definition of R̄)

import Mathlib
import Definitions.Def_ChoiceCDLP_Efficient_ChoiceNetwork

namespace ChoiceCDLP.Efficient

variable {m n : ℕ}

/-- The efficient-frontier function of the appendix (proof of Proposition 3, p. 307):
`R̄(q) = max_α {∑_S α(S) R(S) : ∑_S α(S) Q(S) ≤ q, ∑_S α(S) = 1, α(S) ≥ 0 ∀ S ⊆ N}`,
written as the supremum of the attainable mixed revenues. For `q ∈ [0,1]^m` the set is nonempty
(`α = δ_∅` is feasible since `Q(∅) = 0`) and bounded above by `max_S R(S)`. -/
noncomputable def frontier (N : ChoiceNetwork m n) (q : Fin m → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ α : Finset (Fin n) → ℝ,
    (∀ S, 0 ≤ α S) ∧ (∑ S, α S) = 1 ∧
    (∑ S, α S • consumption N S) ≤ q ∧
    v = ∑ S, α S * revenue N S}

end ChoiceCDLP.Efficient


