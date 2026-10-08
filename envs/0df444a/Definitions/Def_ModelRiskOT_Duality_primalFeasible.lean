-- Prove2me | Definitions.Def_ModelRiskOT_Duality_primalFeasible
-- name    : ModelRiskOT_Duality_primalFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:53:54.249984+00:00
-- url     : https://prove2.me/theorems/6c53c27b-aa59-4ae8-8e57-9f6e26733818
-- title:
--   Primal feasible set $\Phi_{\mu,\delta}$ (6a)
-- statement:
--   Let $S$ be a measurable space, $\mu$ a probability measure on $S$, $c:S\times S\to\mathbb R$ a nonnegative cost and $\delta\in\mathbb R$. The **primal feasible set** is
--
--   $$\Phi_{\mu,\delta}=\Big\{\pi\in\bigcup_{\nu\in P(S)}\Pi(\mu,\nu) : \int c\,d\pi\le\delta\Big\},$$
--
--   the set of probability measures $\pi$ on $S\times S$ whose first marginal is $\mu$ (the second marginal $\nu$ is free) and whose expected transport cost is at most $\delta$. Equivalently, it is the set of transport plans out of $\mu$ into the optimal-transport ball $\{\nu : d_c(\mu,\nu)\le\delta\}$.
--
--   The cost and the budget are parameters so that the variants used in the proof (a continuous cost $c_n$, a smaller budget $\delta_n$) are instances of the same definition.
--
--   **Formalization Note** The first-marginal condition is `π.map Prod.fst = μ`; the cost integral is the lower Lebesgue integral of $\max(c,0)$, compared with $\max(\delta,0)$ in $[0,\infty]$ (the paper's $c$ is nonnegative and $\delta>0$).
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 6, Eq. (6a)

import Mathlib

namespace ModelRiskOT.Duality

open MeasureTheory

/-- The primal feasible set **(6a)** of Blanchet & Murthy, arXiv:1604.01446v2, p. 6:
`Φ_{μ,δ} = {π ∈ ⋃_{ν ∈ P(S)} Π(μ, ν) : ∫ c dπ ≤ δ}`,
the probability measures `π` on `S × S` whose first marginal is `μ` (the second marginal is free)
and whose transport cost `∫ c dπ` is at most `δ`. The cost integral is a lower Lebesgue integral
of the nonnegative cost; the cost `c` is a parameter so that the variants with another cost
(`c_n`, proof of Proposition 6) or another budget (`δ_n`, proof of Proposition 7) are instances. -/
def primalFeasible {S : Type*} [MeasurableSpace S] (c : S → S → ℝ) (μ : Measure S) (δ : ℝ) :
    Set (Measure (S × S)) :=
  {π | IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧
    ∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π ≤ ENNReal.ofReal δ}

end ModelRiskOT.Duality


