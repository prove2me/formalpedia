-- Prove2me | Definitions.Def_ChoiceCDLP_Efficient_IsEfficient
-- name    : ChoiceCDLP_Efficient_IsEfficient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T07:12:01.024453+00:00
-- url     : https://prove2.me/theorems/6d7f845c-9774-4e09-a00f-ebecb255fcdd
-- title:
--   Efficient offer set: no convex mixture of offer sets earns strictly more revenue with no more consumption on any leg
-- statement:
--   **Efficient offer sets.** In the network choice model, an offer set $T \subseteq N$ is **inefficient** if there are convex weights $\alpha(S) \ge 0$, $S \subseteq N$, with $\sum_S \alpha(S) = 1$, such that
--   $$R(T) < \sum_S \alpha(S) R(S) \qquad\text{and}\qquad Q(T) \ge \sum_S \alpha(S) Q(S),$$
--   the second inequality holding componentwise on each of the $m$ legs. That is, a mixture of offer sets produces strictly greater expected revenue and consumes no more capacity (in expectation) on each leg. If no such weights exist, $T$ is **efficient**.
--
--   Efficient sets are those on the efficient frontier of the points $(Q(S), R(S))$; they are the network analogue of the efficient sets of the single-leg choice model of Talluri and van Ryzin (2004).
--
--   **Formalization Note.** The weights range over all offer sets, $T$ included (the paper says "a mixture of other offer sets"); this is equivalent, because the weight vector concentrated on $T$ can never satisfy the strict revenue inequality. The weights are real and may put mass on any subset of offer sets, not only on single sets.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 295, §5, (5)–(6), and p. 296, §5.1

import Mathlib
import Definitions.Def_ChoiceCDLP_Efficient_ChoiceNetwork

namespace ChoiceCDLP.Efficient

variable {m n : ℕ}

/-- An offer set `T` is *efficient* (Liu–van Ryzin 2008, §5, (5)–(6), p. 295, and §5.1, p. 296)
if there are no convex weights `α(S) ≥ 0`, `∑_S α(S) = 1`, over all offer sets `S ⊆ N` with
`R(T) < ∑_S α(S) R(S)` and `Q(T) ≥ ∑_S α(S) Q(S)` (componentwise). -/
def IsEfficient (N : ChoiceNetwork m n) (T : Finset (Fin n)) : Prop :=
  ¬ ∃ α : Finset (Fin n) → ℝ,
      (∀ S, 0 ≤ α S) ∧ (∑ S, α S) = 1 ∧
      revenue N T < ∑ S, α S * revenue N S ∧
      (∑ S, α S • consumption N S) ≤ consumption N T

end ChoiceCDLP.Efficient


