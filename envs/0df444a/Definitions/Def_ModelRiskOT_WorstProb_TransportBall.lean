-- Prove2me | Definitions.Def_ModelRiskOT_WorstProb_TransportBall
-- name    : ModelRiskOT_WorstProb_TransportBall
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:39:50.460533+00:00
-- url     : https://prove2.me/theorems/6c30018a-8826-4773-95fb-6f1d17d37dc5
-- title:
--   Assumption (A1), couplings, the optimal transport cost $d_c$ (2) and the primal feasible set $\Phi_{\mu,\delta}$ (6a)
-- statement:
--   Let $S$ be a Polish space with its Borel $\sigma$-algebra $\mathcal B(S)$, and write $P(S)$ for the probability measures on $S$.
--
--   **Assumption (A1).** The cost $c : S \times S \to \mathbb R_+$ is a nonnegative, lower semicontinuous, real-valued function such that $c(x,y) = 0$ if and only if $x = y$.
--
--   **Couplings.** For $\mu_1, \mu_2 \in P(S)$, a coupling (transport plan) of $\mu_1$ and $\mu_2$ is a probability measure $\pi$ on $S \times S$ whose first marginal is $\mu_1$ and whose second marginal is $\mu_2$; $\Pi(\mu_1,\mu_2)$ is the set of couplings.
--
--   **Optimal transport cost (2).**
--   $$d_c(\mu_1,\mu_2) := \inf\Big\{ \int c \, d\pi : \pi \in \Pi(\mu_1,\mu_2) \Big\} \in [0,\infty].$$
--
--   **Primal feasible set (6a).** For a baseline $\mu \in P(S)$ and a budget $\delta$,
--   $$\Phi_{\mu,\delta} := \Big\{ \pi \in \bigcup_{\nu \in P(S)} \Pi(\mu,\nu) : \int c\,d\pi \le \delta \Big\},$$
--   the probability measures on $S \times S$ with first marginal $\mu$ (the second marginal is free) and transport cost at most $\delta$.
--
--   These are the basic objects of the distributionally robust problem: $d_c$ measures how far a model $P$ is from the baseline $\mu$, and $\Phi_{\mu,\delta}$ is the set of transport plans over which the worst case is computed in coupling form.
--
--   **Formalization Note** The cost is real-valued, as in (A1) ($c : S \times S \to \mathbb R_+$), and the integrals $\int c\,d\pi$ are lower Lebesgue integrals of $\max(c,0) = c$ in $[0,\infty]$, so $d_c$ and the constraint never meet $\infty - \infty$. (A1) is a structure with three fields: nonnegativity, lower semicontinuity of $(x,y) \mapsto c(x,y)$ on $S \times S$, and the iff. Measures on $S \times S$ use the product $\sigma$-algebra, which is the Borel one for Polish $S$.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 4, Assumption 1 (A1); p. 5, Eq. (2); p. 6, Eq. (6a)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_AssumptionA1

open MeasureTheory
open scoped ENNReal

namespace ModelRiskOT.WorstProb

/-- `π` is a coupling (transport plan) of `μ₁` and `μ₂`: a probability measure on `S × S` whose
first and second marginals are `μ₁` and `μ₂` (the set `Π(μ₁, μ₂)`, p. 4). -/
def IsCoupling {S : Type*} [MeasurableSpace S] (μ₁ μ₂ : Measure S) (π : Measure (S × S)) : Prop :=
  IsProbabilityMeasure π ∧ π.map Prod.fst = μ₁ ∧ π.map Prod.snd = μ₂

/-- The optimal transport cost (2), p. 5: `d_c(μ₁, μ₂) = inf {∫ c dπ : π ∈ Π(μ₁, μ₂)}`, valued in
`[0, ∞]`. Both marginals are fixed. -/
noncomputable def transportCost {S : Type*} [MeasurableSpace S] (c : S → S → ℝ)
    (μ₁ μ₂ : Measure S) : ℝ≥0∞ :=
  ⨅ (π : Measure (S × S)) (_ : IsCoupling μ₁ μ₂ π), ∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π

/-- The primal feasible set (6a), p. 6:
`Φ_{μ,δ} = {π ∈ ⋃_{ν ∈ P(S)} Π(μ, ν) : ∫ c dπ ≤ δ}`, i.e. probability measures on `S × S` whose
first marginal is `μ` (the second marginal is free) and whose transport cost is at most `δ`. -/
def Phi {S : Type*} [MeasurableSpace S] (c : S → S → ℝ) (μ : Measure S) (δ : ℝ) :
    Set (Measure (S × S)) :=
  {π | IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧
    ∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π ≤ ENNReal.ofReal δ}

end ModelRiskOT.WorstProb


