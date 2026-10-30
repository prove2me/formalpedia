-- Prove2me | Definitions.Def_KellyKolmogorov_EquilibriumEq
-- name    : KellyKolmogorov_EquilibriumEq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:39:29.353168+00:00
-- url     : https://prove2.me/theorems/3a74065a-8e7f-46fb-9fef-b9c6925bee37
-- title:
--   Equilibrium equations (1.3)
-- statement:
--   Let $\mathcal S$ be a countable set, $m(j)\ge0$, $j\in\mathcal S$, and $w(j,k)\ge0$ transition rates. The family $m$ satisfies the **equilibrium equations** (1.3) for $w$ if
--   $$
--   m(j)\sum_{k\in\mathcal S}w(j,k)=\sum_{k\in\mathcal S}m(k)\,w(k,j)\qquad j\in\mathcal S .
--   $$
--
--   An equilibrium distribution is a collection of positive numbers summing to unity that satisfies these equations.
--
--   **Formalization Note** Both sides are computed in $[0,\infty]$, where every series of nonnegative terms has a value; a real-valued sum would return $0$ for a divergent series and make the equations hold vacuously. The equations are only used for nonnegative $m$.
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), §1.1, eq. (1.3), p. 3 (PDF p. 6)

import Mathlib

open scoped NNReal ENNReal

namespace KellyKolmogorov

/-- **Equilibrium equations of a continuous-time Markov process.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), §1.1, eq. (1.3), p. 3: "For
continuous time processes the equilibrium equations are
`π(j) Σ_{k∈𝒮} q(j, k) = Σ_{k∈𝒮} π(k)q(k, j)`, `j ∈ 𝒮` (1.3)".

`EquilibriumEq m w` says that for every state `j`,
`m(j) Σ_k w(j, k) = Σ_k m(k) w(k, j)`.

**Formalization Note.** Both sides are computed in `[0, ∞]` (`ℝ≥0∞`), where every series of
nonnegative terms has a value; a real-valued `tsum` would return `0` for a divergent series and
make (1.3) hold vacuously. The equations are used only for nonnegative `m`, whose values are
embedded by `ENNReal.ofReal`. -/
def EquilibriumEq {𝒮 : Type*} (m : 𝒮 → ℝ) (w : 𝒮 → 𝒮 → ℝ≥0) : Prop :=
  ∀ j : 𝒮, ENNReal.ofReal (m j) * ∑' k, (w j k : ℝ≥0∞) = ∑' k, ENNReal.ofReal (m k) * (w k j : ℝ≥0∞)

end KellyKolmogorov


