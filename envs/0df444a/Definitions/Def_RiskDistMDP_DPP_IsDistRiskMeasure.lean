-- Prove2me | Definitions.Def_RiskDistMDP_DPP_IsDistRiskMeasure
-- name    : RiskDistMDP_DPP_IsDistRiskMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:36.964647+00:00
-- url     : https://prove2.me/theorems/39e8e110-0c1e-430a-8e28-0353ec5a37ef
-- title:
--   Law-invariant convex risk measure on $\mathcal P_b(\mathbb R)$ (Definition 2.3, corrected weights in (iii))
-- statement:
--   Let $\mathcal P_b(\mathbb R)=\bigcup_{n\in\mathbb N}\mathcal P([-n,n])$ be the probability measures on $\mathbb R$ with bounded support, and $\mathcal P_b(\mathbb R^2)$ the same on $\mathbb R^2$. A functional $\sigma:\mathcal P_b(\mathbb R)\to(-\infty,\infty]$ is a **law-invariant convex risk measure at the level of distributions** if for all $\mu,\mu'\in\mathcal P_b(\mathbb R)$:
--
--   1. (translation) $\sigma(\mu*\delta_c)=\sigma(\mu)+c$ for every $c\in\mathbb R$;
--   2. (monotonicity) if $\mu((-\infty,r])\ge\mu'((-\infty,r])$ for every $r$, then $\sigma(\mu)\le\sigma(\mu')$;
--   3. (convexity) for $\zeta\in\mathcal P_b(\mathbb R^2)$ with marginals $\zeta_0,\zeta_1$ and $\theta\in[0,1]$, writing $\zeta_\theta$ for the law of $(1-\theta)r_0+\theta r_1$ under $\zeta$,
--   $$\sigma(\zeta_\theta)\le(1-\theta)\,\sigma(\zeta_0)+\theta\,\sigma(\zeta_1).$$
--
--   It is **normalized** if $\sigma(\delta_0)=0$. The mean and the average value-at-risk are examples. These functionals are the building blocks of the dynamic risk measure: they are applied to regular conditional distributions rather than to random variables.
--
--   **Formalization Note** $\sigma$ is a function on all measures on $\mathbb R$ with values in `EReal`; the axioms are imposed on $\mathcal P_b(\mathbb R)$ only. The page prints the weights in (iii) the other way round, $\theta\sigma(\zeta_0)+(1-\theta)\sigma(\zeta_1)$. With those weights, $\theta=0$ and $\zeta=\delta_{(1,0)}$ give $\sigma(\delta_1)\le\sigma(\delta_0)$, while (1) gives $\sigma(\delta_1)=\sigma(\delta_0)+1$, so $\sigma(\delta_0)=+\infty$ for every such $\sigma$ and Assumption 2.6 could never hold. The corrected weights are those of Definition 2.2 (iii).
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Definition 2.3, p. 7; §2, p. 5 ($\mathcal P_b$)

import Mathlib

set_option autoImplicit false

open MeasureTheory Set

namespace RiskDistMDP.DPP

/-- A measure on `ℝ` lies in `𝒫_b(ℝ)` (arXiv:2203.09612v4, §2, p.5): it is a probability measure
whose support is contained in `[-n, n]` for some `n ∈ ℕ`, i.e. `𝒫_b(ℝ) = ⋃_n 𝒫([-n,n])`. -/
def InPb (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∃ n : ℕ, μ (Icc (-(n : ℝ)) n)ᶜ = 0

/-- A measure on `ℝ²` lies in `𝒫_b(ℝ²)` (arXiv:2203.09612v4, §2, p.5, "in a similar manner"):
a probability measure supported in `[-n, n]²` for some `n ∈ ℕ`. -/
def InPb2 (ζ : Measure (ℝ × ℝ)) : Prop :=
  IsProbabilityMeasure ζ ∧ ∃ n : ℕ, ζ (Icc (-(n : ℝ)) n ×ˢ Icc (-(n : ℝ)) n)ᶜ = 0

/-- **Law-invariant convex risk measure at the level of distributions** (arXiv:2203.09612v4,
Definition 2.3, p.7), with axiom (iii) corrected. A functional `σ : 𝒫_b(ℝ) → (−∞, ∞]` such that
for all `μ, μ' ∈ 𝒫_b(ℝ)`:

* (o) `σ(μ) ≠ −∞` (the codomain is `(−∞, ∞]`);
* (i) `σ(μ ∗ δ_c) = σ(μ) + c` for every `c ∈ ℝ`;
* (ii) `μ((−∞,r]) ≥ μ'((−∞,r])` for all `r` implies `σ(μ) ≤ σ(μ')`;
* (iii) for `ζ ∈ 𝒫_b(ℝ²)` with marginals `ζ₀, ζ₁` and `θ ∈ [0,1]`, writing `ζ_θ` for the law of
  `(1 − θ) r₀ + θ r₁` under `ζ`, `σ(ζ_θ) ≤ (1 − θ) σ(ζ₀) + θ σ(ζ₁)`.

**Formalization Note** `σ` is a function on all of `Measure ℝ` with values in `EReal`; the axioms
are imposed only on `𝒫_b(ℝ)` (`InPb`), and its values elsewhere are irrelevant. `μ ∗ δ_c` is the
push-forward of `μ` under `r ↦ r + c`; `ζ_θ` is the push-forward of `ζ` under
`(r₀, r₁) ↦ (1 − θ) r₀ + θ r₁`, which is the measure the page characterizes by its distribution
function. The printed (iii) reads `σ(ζ_θ) ≤ θ σ(ζ₀) + (1 − θ) σ(ζ₁)`: the weights are crossed. With
the printed weights, (iii) at `θ = 0`, `ζ = δ_{(1,0)}` gives `σ(δ₁) ≤ σ(δ₀)` while (i) gives
`σ(δ₁) = σ(δ₀) + 1`, so `σ(δ₀) = +∞` for every such `σ`, contradicting Assumption 2.6; the
corrected weights are those of Definition 2.2 (iii) and Remark 2.5. EReal products use
`0 · (+∞) = 0`. -/
def IsDistRiskMeasure (σ : Measure ℝ → EReal) : Prop :=
  (∀ μ, InPb μ → σ μ ≠ ⊥) ∧
  (∀ μ, InPb μ → ∀ c : ℝ, σ (μ.map (fun r => r + c)) = σ μ + c) ∧
  (∀ μ μ', InPb μ → InPb μ' → (∀ r : ℝ, μ' (Iic r) ≤ μ (Iic r)) → σ μ ≤ σ μ') ∧
  (∀ ζ : Measure (ℝ × ℝ), InPb2 ζ → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    σ (ζ.map (fun p => (1 - θ) * p.1 + θ * p.2)) ≤
      ((1 - θ : ℝ) : EReal) * σ (ζ.map Prod.fst) + (θ : EReal) * σ (ζ.map Prod.snd))

/-- A distribution-level risk measure is **normalized** (arXiv:2203.09612v4, Definition 2.3, p.7)
if `σ(δ₀) = 0`. -/
def Normalized (σ : Measure ℝ → EReal) : Prop :=
  σ (Measure.dirac 0) = 0

end RiskDistMDP.DPP


