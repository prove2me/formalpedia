-- Prove2me | Definitions.Def_KellyKolmogorov_DetailedBalance
-- name    : KellyKolmogorov_DetailedBalance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:39:15.86823+00:00
-- url     : https://prove2.me/theorems/b4a83045-5971-46e3-84a2-2f09e8aa28aa
-- title:
--   Detailed balance conditions
-- statement:
--   Let $\mathcal S$ be a set, $\pi(j)$, $j\in\mathcal S$, real numbers and $w(j,k)\ge0$, $j,k\in\mathcal S$, nonnegative weights (transition probabilities or transition rates). The family $\pi$ satisfies the **detailed balance conditions** for $w$ if
--   $$
--   \pi(j)\,w(j,k)=\pi(k)\,w(k,j)\qquad j,k\in\mathcal S .
--   $$
--
--   For transition rates these are the conditions (1.6) of Theorem 1.3; for transition probabilities they are (1.5).
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), §1.2, eq. (1.6), p. 7 (PDF p. 10); eq. (1.5), p. 5 (PDF p. 8)

import Mathlib

open scoped NNReal

namespace KellyKolmogorov

/-- **Detailed balance conditions.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), §1.2, Theorem 1.3, eq. (1.6),
p. 7: "`π(j)q(j, k) = π(k)q(k, j)`, `j, k ∈ 𝒮`" (and (1.5), p. 5, for transition
probabilities `p`).

`DetailedBalance π w` says `π(j) w(j, k) = π(k) w(k, j)` for all states `j, k`, for a family of
real numbers `π` and nonnegative weights `w` (transition rates or transition probabilities). -/
def DetailedBalance {𝒮 : Type*} (π : 𝒮 → ℝ) (w : 𝒮 → 𝒮 → ℝ≥0) : Prop :=
  ∀ j k : 𝒮, π j * (w j k : ℝ) = π k * (w k j : ℝ)

end KellyKolmogorov


