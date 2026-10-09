-- Prove2me | Definitions.Def_MHSpectralGap_RWM_Conductance
-- name    : MHSpectralGap_RWM_Conductance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:26.812837+00:00
-- url     : https://prove2.me/theorems/dc6a7a38-f061-47e4-a2c0-68c03e1a696e
-- title:
--   (2.6) and p. 14 — the conductance C of a Markov kernel and the expected acceptance probability α(x) of a proposal from x
-- statement:
--   Let $P$ be a Markov kernel on a measurable space $X$ and $\mu$ a probability measure on $X$. The **conductance** of $P$ with respect to $\mu$ is
--
--   $$
--   \mathsf C \;=\; \inf_{0<\mu(A)\le 1/2}\ \frac{\int_A P(x,A^c)\,d\mu(x)}{\mu(A)},
--   $$
--
--   the infimum over measurable sets $A$ with $0<\mu(A)\le\tfrac12$; it is the smallest rate at which the stationary chain leaves a set carrying at most half the mass. It takes values in $[0,\infty]$ and equals $+\infty$ when no such set exists.
--
--   For a Metropolis–Hastings kernel with proposal $Q$ and acceptance probability $\alpha(x,y)$, the **expected acceptance probability** of a proposal from $x$ is
--
--   $$
--   \alpha(x)=\int \alpha(x,y)\,Q(x,dy).
--   $$
--
--   Cheeger's inequality $1-\beta\le 2\mathsf C$ turns an upper bound on $\mathsf C$ into an upper bound on the spectral gap; $\alpha(x)$ is the quantity that bounds $\mathsf C$ for random walk Metropolis.
--
--   **Formalization Note** The paper's infimum is over $\mu(A)\le 1/2$; the condition $0<\mu(A)$ is added because the quotient is undefined at $\mu(A)=0$ (in $[0,\infty]$, $0/0=0$ would force $\mathsf C=0$). Both quantities are computed in $[0,\infty]$ with lower Lebesgue integrals.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 14, display (2.6) and the display defining α(x)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.RWM

/-- The conductance (2.6), p. 14:
`C = inf_{μ(A) ≤ 1/2} ∫_A P(x, Aᶜ) dμ(x) / μ(A)`, the infimum taken over measurable `A`
with `0 < μ(A) ≤ 1/2`, computed in `[0, ∞]` (equal to `∞` if no such `A` exists). -/
noncomputable def conductance {X : Type*} [MeasurableSpace X] (P : ProbabilityTheory.Kernel X X)
    (μ : Measure X) : ℝ≥0∞ :=
  ⨅ (A : Set X) (_ : MeasurableSet A) (_ : 0 < μ A) (_ : μ A ≤ 1 / 2),
    (∫⁻ x in A, P x Aᶜ ∂μ) / μ A

/-- The expected acceptance probability of a proposal from `x`, p. 14:
`α(x) = ∫ α(x, y) Q(x, dy)`. -/
noncomputable def accBar {X : Type*} [MeasurableSpace X] (Q : ProbabilityTheory.Kernel X X)
    (α : X → X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ∫⁻ y, α x y ∂(Q x)

end MHSpectralGap.RWM


