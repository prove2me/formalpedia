-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_truncRates
-- name    : KellyRSN_PartialBalance_truncRates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:37:16.690003+00:00
-- url     : https://prove2.me/theorems/17eace10-ccf4-4460-b662-47b18b4ce215
-- title:
--   Transition rates of the process truncated to $\mathcal A$
-- statement:
--   A Markov process with rates $q$ on $\mathcal S$ is **truncated to the set $\mathcal A \subseteq \mathcal S$** by changing $q(j,k)$ to zero for $j \in \mathcal A$, $k \in \mathcal S - \mathcal A$. The truncated process, started in $\mathcal A$, stays in $\mathcal A$ and has the rates
--   $$
--   q(j,k), \qquad j, k \in \mathcal A,
--   $$
--   on the state space $\mathcal A$.
--
--   **Formalization Note** The truncated process is represented by the rate matrix on the subtype $\mathcal A$. The book's further requirement that the truncated process be irreducible within $\mathcal A$ is not part of this definition; the theorems using it hold without that requirement.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 25 (PDF p. 28), §1.6, definition of truncation to a set

import Mathlib

open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Transition rates of the process truncated to `𝒜`.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, §1.6, p. 25 (PDF p. 28): "Say that a
Markov process is truncated to the set `𝒜 ⊂ 𝒮` if `q(j, k)` is changed to zero for `j ∈ 𝒜`,
`k ∈ 𝒮 − 𝒜`, and if the resulting process is irreducible within the state space `𝒜`."

`truncRates q A` is the rate matrix on the state space `A`: `q(j, k)` for `j, k ∈ A`.

**Formalization Note.** The truncated process is the process on the state space `A` (once the
rates from `A` to `𝒮 − 𝒜` are zero, a process started in `A` never leaves `A`, and the rates from
`𝒮 − 𝒜` into `A` play no role). The irreducibility requirement on the truncated process is not part
of this definition; it is not needed by the statements that use it (see their notes). -/
def truncRates {S : Type*} (q : S → S → ℝ≥0∞) (A : Set S) : A → A → ℝ≥0∞ :=
  fun j k => q j k

end KellyRSN.PartialBalance


