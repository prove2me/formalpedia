-- Prove2me | Definitions.Def_ShapleyScarf_CoreExistence_assignmentPayoff
-- name    : ShapleyScarf_CoreExistence_assignmentPayoff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:38:01.718924+00:00
-- url     : https://prove2.me/theorems/530d2173-18f6-43da-b981-fa53d62bb934
-- title:
--   Sections 2 and 5 — actual payoff of an item assignment
-- statement:
--   Let $N$ be the trader set, let $A=(a_{ij})$ be the real preference matrix, and let $\sigma:N\to N$ give trader $i$ the item originally owned by $\sigma(i)$. Its assignment payoff is
--
--   $$u_\sigma(i)=a_{i,\sigma(i)}\qquad(i\in N).$$
--
--   When $\sigma$ is bijective this is the actual utility vector of a permutation allocation, with every item assigned exactly once. Ties and negative entries of $A$ are allowed. These payoffs distinguish actual trades from disposable payoff thresholds in $V_A(N)$.
--
--   **Formalization Note.** The function is defined on all maps $\sigma$; every theorem asserting realizability explicitly requires bijectivity. This definition neither sums the values of bundles nor assumes any allocation is in the core.
-- source:
--   Shapley and Scarf, On cores and indivisibility, Journal of Mathematical Economics 1 (1974), published, DOI 10.1016/0304-4068(74)90033-0, https://doi.org/10.1016/0304-4068(74)90033-0; Section 2, preference matrix and permutation allocations, printed pp. 106–107 / PDF pp. 3–4; Section 5, realizability paragraph, printed pp. 112–113 / PDF pp. 9–10.

import Mathlib

namespace ShapleyScarf.CoreExistence

/-- Sections 2 and 5, printed pp. 106–107, 112–113 / PDF pp. 3–4, 9–10:
the actual utility from giving trader `i` item `σ i`. The allocation theorems require `σ`
bijective, so this is a realizable permutation payoff, with no disposal or side payments. -/
def assignmentPayoff {N : Type*} (A : N → N → ℝ) (σ : N → N) : N → ℝ :=
  fun i => A i (σ i)

end ShapleyScarf.CoreExistence


