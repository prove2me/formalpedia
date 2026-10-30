-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_reversedRates
-- name    : KellyRSN_PartialBalance_reversedRates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:38:19.195075+00:00
-- url     : https://prove2.me/theorems/8a04b5e2-ed17-49eb-a319-7df6dbe5a2e7
-- title:
--   Transition rates of the reversed process
-- statement:
--   For rates $q$ on a countable state space and an equilibrium distribution $\mu$, the **reversed rates** are
--   $$
--   q'(j,k) = \frac{\mu(k)\, q(k,j)}{\mu(j)} .
--   $$
--
--   By Theorem 1.12, if $X(t)$ is a stationary Markov process with rates $q$ and equilibrium distribution $\mu$, the reversed process $X(\tau - t)$ is a stationary Markov process with rates $q'$ and the same equilibrium distribution.
--
--   **Formalization Note** The reversed process itself is not constructed; the statements that use this definition compare only transition rates. The state type is arbitrary, so the definition applies to a truncated process with its own equilibrium distribution.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 28 (PDF p. 31), Theorem 1.12

import Mathlib

open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Transition rates of the reversed process.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Theorem 1.12, p. 28 (PDF p. 31): "If
`X(t)` is a stationary Markov process with transition rates `q(j, k)`, `j, k ∈ 𝒮`, and equilibrium
distribution `π(j)`, `j ∈ 𝒮`, then the reversed process `X(τ − t)` is a stationary Markov process
with transition rates `q'(j, k) = π(k) q(k, j) / π(j)`, `j, k ∈ 𝒮` and the same equilibrium
distribution."

`reversedRates q μ j k = μ k * q k j / μ j`.

**Formalization Note.** The reversed process itself is not constructed: by Theorem 1.12 it is the
stationary Markov process with these rates, which is all that the statements using this definition
compare. The state type is arbitrary, so the definition applies to a truncated process (on `↥A`)
with its own equilibrium distribution. For a positive finite `μ` (an equilibrium distribution) no
division by `0` or `∞` occurs. -/
noncomputable def reversedRates {T : Type*} (q : T → T → ℝ≥0∞) (μ : T → ℝ≥0∞) :
    T → T → ℝ≥0∞ :=
  fun j k => μ k * q k j / μ j

end KellyRSN.PartialBalance


