-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_IsEquilibriumDist
-- name    : KellyRSN_PartialBalance_IsEquilibriumDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:34:33.408818+00:00
-- url     : https://prove2.me/theorems/9f37e84a-087f-4bff-b378-b1271751e3de
-- title:
--   Equilibrium distribution of a Markov process (equations (1.3))
-- statement:
--   Let $T$ be a countable set of states and let $q(j,k) \in [0,\infty]$ be transition rates on $T$. A family $\mu(j)$, $j \in T$, is an **equilibrium distribution** for the rates $q$ if
--
--   1. every $\mu(j)$ is positive;
--   2. $\sum_{j \in T} \mu(j) = 1$;
--   3. the equilibrium equations (1.3) hold:
--   $$
--   \mu(j) \sum_{k \in T} q(j,k) = \sum_{k \in T} \mu(k)\, q(k,j), \qquad j \in T.
--   $$
--
--   This is the book's definition of an equilibrium distribution of a continuous-time Markov process. It is used both for the original process and for processes derived from it (truncated, with altered rates).
--
--   **Formalization Note** Values and sums are in $[0,\infty]$ (`ℝ≥0∞`), so every sum is defined; finiteness of each $\mu(j)$ follows from the normalization.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 3 (PDF p. 6), §1.1, equations (1.3) and the definition of an equilibrium distribution

import Mathlib

open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Equilibrium distribution of a Markov process given by its transition rates.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, §1.1, p. 3 (PDF p. 6), equations (1.3):
"For continuous time processes the equilibrium equations are
`π(j) Σ_{k∈𝒮} q(j, k) = Σ_{k∈𝒮} π(k) q(k, j)`, `j ∈ 𝒮` (1.3)
and an equilibrium distribution is a collection of positive numbers `π(j)`, `j ∈ 𝒮`, summing to
unity which satisfy the equilibrium equations."

`IsEquilibriumDist q μ` says that every `μ j` is positive, that `Σ_j μ j = 1`, and that `μ`
satisfies (1.3) for the rates `q`.

**Formalization Note.** The state type `T` is arbitrary (the definition is used both on the state
space `S` and on a subtype `↥A` for truncated processes). Rates and weights take values in
`ℝ≥0∞` and every sum is an `ℝ≥0∞`-valued `tsum`, which is always defined (no summability side
condition can make (1.3) hold vacuously). `μ j < ⊤` follows from `Σ μ = 1`. -/
def IsEquilibriumDist {T : Type*} (q : T → T → ℝ≥0∞) (μ : T → ℝ≥0∞) : Prop :=
  (∀ j, 0 < μ j) ∧ ∑' j, μ j = 1 ∧ ∀ j, μ j * ∑' k, q j k = ∑' k, μ k * q k j

end KellyRSN.PartialBalance


