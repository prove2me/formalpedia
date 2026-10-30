-- Prove2me | Definitions.Def_FarmerInfoProvision_expectedProfit
-- name    : FarmerInfoProvision_expectedProfit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:39:48.106329+00:00
-- url     : https://prove2.me/theorems/a40c2763-89e0-479c-ad1e-e280fd1375a9
-- title:
--   Ex-ante expected profit of farmer $i$ under a strategy profile
-- statement:
--   A strategy profile assigns to each farmer $k$ a function $\sigma_k:\mathbb R^2\to\mathbb R$ of her observation; farmer $k$ produces $q_k=\sigma_k(\mathrm{obs}_I(k))$. Farmer $i$'s ex-ante expected profit is
--
--   $$
--   \pi_i(\sigma)=\mathbb E\Bigl[\Bigl(a-b\sum_{k}q_k+u-c\Bigr)q_i\Bigr],
--   $$
--
--   the expectation of the profit in problems (2)–(3).
--
--   **Formalization Note** Quantities are unrestricted real numbers. The expectation is a genuine one at square-integrable profiles, the only ones at which the equilibrium notion evaluates it.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §3, problems (2)–(3), p. 10, and p. 11

import Mathlib
import Definitions.Def_FarmerInfoProvision_obs

open MeasureTheory ProbabilityTheory

namespace FarmerInfoProvision

/-- **Farmer `i`'s ex-ante expected profit under the strategy profile `σ`.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §3, problems (2)–(3), p. 10: farmer `i` earns
"`(a − b(q_i + Σ_{i'∈I, i'≠i} q_{i'} + Σ_{j∈J} q_j) + u)q_i − cq_i`"; and p. 11: "the (ex-ante)
expected profit for any farmer `i ∈ I` is given by `W^I(n1, β, γ) = E_{{x_i},y}{W_i(…)}`".

A strategy profile is `σ : Fin n → ℝ × ℝ → ℝ`; farmer `k` produces `q_k = σ k (obs … I k ω)`.
Then `expectedProfit M a b c α β γ I σ i = E[(a − b Σ_k q_k + u − c) q_i]` with
`u = demandShock M α`.

**Formalization Note.** Quantities are unrestricted real numbers (see `IsBNE`). The integral is
a genuine expectation whenever every `q_k` is square integrable (`Admissible`), since `u` is
Gaussian; `IsBNE` only evaluates it at such profiles. -/
noncomputable def expectedProfit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : GaussianPrimitives P n) (a b c α β γ : ℝ) (I : Finset (Fin n))
    (σ : Fin n → ℝ × ℝ → ℝ) (i : Fin n) : ℝ :=
  ∫ ω, (a - b * ∑ k, σ k (obs M α β γ I k ω) + demandShock M α ω - c) *
    σ i (obs M α β γ I i ω) ∂P

end FarmerInfoProvision


