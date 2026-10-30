-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_ReversalTruncationCommute
-- name    : KellyRSN_PartialBalance_ReversalTruncationCommute
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:38:51.460425+00:00
-- url     : https://prove2.me/theorems/d332c3f5-8185-4938-86e3-588bf158da1d
-- title:
--   Time reversal and truncation to $\mathcal A$ commute
-- statement:
--   Let $X(t)$ be a Markov process with rates $q$ on $\mathcal S$ and equilibrium distribution $\pi$, and let $\mathcal A \subseteq \mathcal S$. Let $Y(t)$ be the stationary process truncated to $\mathcal A$, with equilibrium distribution $\mu$, and let $Z(t)$ be the stationary process obtained by truncating the reversed process $X(-t)$ to $\mathcal A$. **Time reversal and truncation to $\mathcal A$ commute** if $Z(t)$ and $Y(-t)$ have the same transition rates, that is,
--   $$
--   \frac{\mu(k)\, q(k,j)}{\mu(j)} = \frac{\pi(k)\, q(k,j)}{\pi(j)}, \qquad j, k \in \mathcal A,
--   $$
--   for some equilibrium distribution $\mu$ of the truncated rates.
--
--   The left side is the rate of $Y(-t)$ and the right side the rate of $Z(t)$, both by Theorem 1.12.
--
--   **Formalization Note** $\mu$ is existentially quantified as an equilibrium distribution of the truncated rates (it is not taken to be the conditional distribution of $\pi$); it is unique when the truncated process is irreducible, as the book's truncation requires.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 33 (PDF p. 36), Exercise 1.7.7 (definition of 'commute'); p. 28 (PDF p. 31), Theorem 1.12

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_IsEquilibriumDist
import Definitions.Def_KellyRSN_PartialBalance_truncRates
import Definitions.Def_KellyRSN_PartialBalance_reversedRates

open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Time reversal and truncation to `𝒜` commute.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.7.7, p. 33 (PDF p. 36):
"Suppose that a Markov process `X(t)` with transition rates `q(j, k)`, `j, k ∈ 𝒮`, and equilibrium
distribution `π(j)`, `j ∈ 𝒮`, is truncated to the set `𝒜`. Let `Y(t)` be the stationary truncated
process. Let `Z(t)` be the stationary process resulting from truncating the reversed process
`X(−t)` to the set `𝒜`. … If `Z(t)` and `Y(−t)` have the same transition rates we shall say that
for the process `X(t)` the operations of time reversal and truncation to the set `𝒜` commute."

`ReversalTruncationCommute q π A` says: there is an equilibrium distribution `μ` of the truncated
process (`truncRates q A`) such that, for all `j, k ∈ A`, the rates of `Y(−t)`,
`μ(k) q(k, j) / μ(j)`, equal the rates of `Z(t)`, `π(k) q(k, j) / π(j)`.

**Formalization Note.** By Theorem 1.12 (p. 28, PDF p. 31) the reversed stationary process of a
process with rates `r` and equilibrium distribution `ν` has rates `ν(k) r(k, j) / ν(j)`
(`reversedRates`). `Y(−t)` therefore has rates `reversedRates (truncRates q A) μ` with `μ` the
equilibrium distribution of the truncated process `Y` (quantified, not taken to be `π`
conditioned on `A`), and `Z(t)` has the rates of `X(−t)` restricted to `A × A`. The book's
"the stationary truncated process" is read as "a stationary version of the truncated process":
`∃ μ`; under the book's assumption that the truncated process is irreducible, `μ` is unique. -/
def ReversalTruncationCommute {S : Type*} (q : S → S → ℝ≥0∞) (π : S → ℝ≥0∞) (A : Set S) :
    Prop :=
  ∃ μ : A → ℝ≥0∞, IsEquilibriumDist (truncRates q A) μ ∧
    ∀ j k : A, reversedRates (truncRates q A) μ j k = truncRates (reversedRates q π) A j k

end KellyRSN.PartialBalance


