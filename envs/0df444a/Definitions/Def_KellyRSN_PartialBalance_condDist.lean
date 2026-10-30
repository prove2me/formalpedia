-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_condDist
-- name    : KellyRSN_PartialBalance_condDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:37:31.547059+00:00
-- url     : https://prove2.me/theorems/6b32f280-c538-41d2-a6aa-46c12dc00732
-- title:
--   Conditional distribution $\pi(j)/\sum_{k\in\mathcal A}\pi(k)$ on $\mathcal A$
-- statement:
--   For a distribution $\pi$ on $\mathcal S$ and a set $\mathcal A \subseteq \mathcal S$, the **conditional probability distribution** of $\pi$ on $\mathcal A$ is
--   $$
--   \frac{\pi(j)}{\sum_{k \in \mathcal A} \pi(k)}, \qquad j \in \mathcal A .
--   $$
--
--   Theorem 9.5 (ii) asks when this is the equilibrium distribution of the process truncated to $\mathcal A$.
--
--   **Formalization Note** A function on the subtype $\mathcal A$ with values in $[0,\infty]$. The theorems using it assume $\mathcal A$ non-empty; then for a positive probability vector $\pi$ the denominator lies in $(0,1]$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 27 (PDF p. 30), Exercise 1.6.2; p. 200 (PDF p. 203), Theorem 9.5 (ii)

import Mathlib

open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Conditional distribution of `π` on `𝒜`.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.6.2, p. 27 (PDF p. 30) and
Theorem 9.5 (ii), p. 200 (PDF p. 203): "the conditional probability distribution
`π(j) / Σ_{k∈𝒜} π(k)`, `j ∈ 𝒜`".

**Formalization Note.** A function on the subtype `↥A`, in `ℝ≥0∞`. For `A` empty the expression is
meaningless (there is nothing to condition on); statements using it assume `A` non-empty, and then
`0 < Σ_{k∈A} π(k) ≤ 1` for a positive probability vector `π`, so no division by `0` or `∞` occurs. -/
noncomputable def condDist {S : Type*} (π : S → ℝ≥0∞) (A : Set S) : A → ℝ≥0∞ :=
  fun j => π j / ∑' k : A, π k

end KellyRSN.PartialBalance


