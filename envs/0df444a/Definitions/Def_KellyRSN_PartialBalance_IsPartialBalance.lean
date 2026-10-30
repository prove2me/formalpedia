-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_IsPartialBalance
-- name    : KellyRSN_PartialBalance_IsPartialBalance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:37:05.361866+00:00
-- url     : https://prove2.me/theorems/6f471522-6f36-4d99-a105-53804ddaafa3
-- title:
--   Partial balance conditions for a set $\mathcal A$ (1.24)
-- statement:
--   Let $q$ be transition rates on a countable state space $\mathcal S$, $\pi(j)$, $j \in \mathcal S$, a distribution and $\mathcal A \subseteq \mathcal S$. The distribution $\pi$ satisfies the **partial balance conditions for the set $\mathcal A$** if
--   $$
--   \pi(j) \sum_{k \in \mathcal A} q(j,k) = \sum_{k \in \mathcal A} \pi(k)\, q(k,j), \qquad j \in \mathcal A. \tag{1.24}
--   $$
--
--   These equations lie between the detailed balance conditions and the full equilibrium equations (1.3); Theorem 9.5 gives six equivalent characterizations of them.
--
--   **Formalization Note** Sums are over the subtype $\mathcal A$, in $[0,\infty]$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 27 (PDF p. 30), Exercise 1.6.2, equations (1.24)

import Mathlib

open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Partial balance conditions for a set `𝒜`.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.6.2, p. 27 (PDF p. 30),
equations (1.24): "`π(j) Σ_{k∈𝒜} q(j, k) = Σ_{k∈𝒜} π(k) q(k, j)`, `j ∈ 𝒜` (1.24). … we shall call
them the partial balance conditions for the set `𝒜`."

`IsPartialBalance q π A` says that for every `j ∈ A`,
`π j * Σ_{k ∈ A} q j k = Σ_{k ∈ A} π k * q k j`.

**Formalization Note.** Sums are `ℝ≥0∞`-valued `tsum`s over the subtype `↥A`. -/
def IsPartialBalance {S : Type*} (q : S → S → ℝ≥0∞) (π : S → ℝ≥0∞) (A : Set S) : Prop :=
  ∀ j ∈ A, π j * ∑' k : A, q j k = ∑' k : A, π k * q k j

end KellyRSN.PartialBalance


