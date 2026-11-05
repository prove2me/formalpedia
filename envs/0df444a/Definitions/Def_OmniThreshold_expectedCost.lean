-- Prove2me | Definitions.Def_OmniThreshold_expectedCost
-- name    : OmniThreshold_expectedCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:35:41.010563+00:00
-- url     : https://prove2.me/theorems/54d0c3bd-86ec-4e8a-ad74-4137a20cee9e
-- title:
--   Expected total cost $G(S,D)$ of the Global Threshold $S$
-- statement:
--   Let $\mu$ be a law of the random objects $(X,N,\mathcal D^P)$: the order locations, the total number of online orders, and the vector of in-store demands. For a Global Threshold $S$, the **expected value of the objective of the Omni-Channel Fulfillment Model** under $\mu$ is
--   $$
--   G(S,\mu)=\mathbb E_\mu\bigl[Q(\mathcal I,\mathcal D^P,\mathcal D^O,A^O(S))\bigr],
--   $$
--   where $Q$ is the optimal value of LP (1), $\mathcal D^O$ the online demand and $A^O(S)$ the accepted orders.
--
--   With $\mu$ the true law $\mathbb P$ this is the paper's $G(S)$ of Theorem 2. With $\mu=\mathbb P[\,\cdot\mid N>S']$ it is the paper's $G(S,D(S'))$.
--
--   **Formalization Note** The expectation is the Bochner integral over a measure on the sample space. Under the measurability hypotheses of the theorems the integrand is measurable and bounded, hence integrable; this is proved in a verification file.
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, Theorem 2 and its proof, p.9

import Mathlib
import Definitions.Def_OmniThreshold_lp1Value
import Definitions.Def_OmniThreshold_onlineDemand
import Definitions.Def_OmniThreshold_acceptedCount

namespace OmniThreshold

open MeasureTheory

/-- The **expected value of the objective of the Omni-Channel Fulfillment Model under the Global
Threshold `S` and the demand law `μ`**, the paper's `G(S, D)` (Jia, Karp, Ravi & Tayur, *Effective
Online Order Acceptance Policies for Omni-Channel Fulfillment*, SSRN 3932692, Theorem 2, p.9, and
its proof, p.9: "we will define functions `G(S, D)`, … which are the functions `G(S)`, … under
arbitrary demand distributions `D = (D^O, D^P)`"):
```
G(S, μ) = ∫ lp1Value(I, D^P(ω), D^O(ω), A^O_S(ω)) dμ(ω).
```
With `μ = P` this is `G(S)` of Theorem 2; with `μ = P[· | N > S']` it is `G(S, D(S'))`.

The online orders arrive as the sequence of locations `X 0 ω, X 1 ω, …`, of which the first `N ω`
are orders; `DP ω` is the vector of in-store demands.

**Formalization Note** The demand law is a measure `μ` on a sample space carrying the random
objects `X`, `N`, `DP`; `D^O = onlineDemand X N` and `A^O_S = acceptedCount X N S`. The
integral is the Bochner integral; under the measurability hypotheses of the theorems the integrand
is measurable and bounded, so the integral is the expectation. -/
noncomputable def expectedCost {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (p : ℝ) (c : Fin n → ℝ)
    (s : Fin n → Fin n → ℝ) (I : Fin n → ℕ) (X : ℕ → Ω → Fin n) (N : Ω → ℕ)
    (DP : Ω → Fin n → ℕ) (μ : Measure Ω) (S : ℕ) : ℝ :=
  ∫ ω, lp1Value p c s I (DP ω) (onlineDemand X N ω) (acceptedCount X N S ω) ∂μ

end OmniThreshold


