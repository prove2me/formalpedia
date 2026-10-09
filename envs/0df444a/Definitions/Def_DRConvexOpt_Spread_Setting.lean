-- Prove2me | Definitions.Def_DRConvexOpt_Spread_Setting
-- name    : DRConvexOpt_Spread_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:51.188066+00:00
-- url     : https://prove2.me/theorems/28e5de1b-c7ae-4e94-afd2-fb6b51163cae
-- title:
--   Notation p. 7, Proposition 2 pp. 17–18 — conditional means, the absolute-mean-spread set and the lifted ambiguity set 𝒫
-- statement:
--   Fix a vector $f\in\mathbb R^P$ and numbers $\theta\in\mathbb R$, $\sigma\ge0$, $\rho\in(0,1)$. For a probability distribution $\mathbb Q$ on $\mathbb R^P$ under which $f^\top\tilde z$ has a finite mean, the two **conditional means** of $f^\top\tilde z$ on either side of the threshold $\theta$ are
--
--   $$
--   \mathbb E_{\mathbb Q}[f^\top\tilde z\mid f^\top\tilde z\ge\theta]=\frac{\mathbb E_{\mathbb Q}\big[f^\top\tilde z\,\mathbf 1\{f^\top\tilde z\ge\theta\}\big]}{\mathbb Q[f^\top\tilde z\ge\theta]},\qquad
--   \mathbb E_{\mathbb Q}[f^\top\tilde z\mid f^\top\tilde z<\theta]=\frac{\mathbb E_{\mathbb Q}\big[f^\top\tilde z\,\mathbf 1\{f^\top\tilde z<\theta\}\big]}{\mathbb Q[f^\top\tilde z<\theta]},
--   $$
--
--   and their difference is the **absolute mean spread** of $f^\top\tilde z$ at $\theta$. The file defines:
--
--   1. the **target set** $\{\mathbb Q\in\mathcal P_0(\mathbb R^P):\ \mathbb E_{\mathbb Q}[f^\top\tilde z\mid f^\top\tilde z\ge\theta]-\mathbb E_{\mathbb Q}[f^\top\tilde z\mid f^\top\tilde z<\theta]\le\sigma,\ \mathbb Q[f^\top\tilde z\ge\theta]=\rho\}$, whose members are required to have $f^\top\tilde z$ integrable;
--   2. the **lifted ambiguity set** $\mathcal P$ of probability distributions $\mathbb P$ of $(\tilde z,\tilde u,\tilde v,\tilde w)$ on $\mathbb R^P\times\mathbb R^3$ with $\tilde w$ integrable, $\mathbb E_{\mathbb P}[\tilde w]=\sigma$, $\mathbb P[f^\top\tilde z\ge\theta]=\rho$, and, with probability one,
--
--   $$
--   f^\top\tilde z=\theta+\tilde u-\tilde v,\qquad \tilde w\ge\rho^{-1}\tilde u+(1-\rho)^{-1}\tilde v,\qquad \tilde u,\tilde v\ge0 .
--   $$
--
--   Together with the marginal map $\mathbb P\mapsto\Pi_{\tilde z}\mathbb P$ these are the objects of Proposition 2: the lifted set is an instance of the paper's standardized ambiguity set (4) that encodes a bound on the absolute mean spread.
--
--   **Formalization Note** The conditional means are elementary conditional expectations, $\mathbb E_{\mathbb Q}[f^\top\tilde z\mid A]=\mathbb E_{\mathbb Q}[f^\top\tilde z\,\mathbf 1_A]/\mathbb Q[A]$; both events have probability $\rho$ or $1-\rho$, which are positive because $\rho\in(0,1)$, so no division by zero occurs. An outcome is $\omega=(z,(u,v,w))\in\mathbb R^P\times(\mathbb R\times\mathbb R\times\mathbb R)$, with $\tilde u,\tilde v,\tilde w$ the projections `uOf`, `vOf`, `wOf`; the marginal $\Pi_{\tilde z}\mathbb P$ is the push-forward of $\mathbb P$ under the first projection. The integrability of $f^\top\tilde z$ in the target set and of $\tilde w$ in the lifted set is what the page's expectations presuppose (Lean's integral of a non-integrable function is $0$). Indices of $\mathbb R^P$ are `Fin P`, 0-based.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 7 (Notation: 𝒫₀, Π_z̃) and pp. 17–18, Proposition 2

import Mathlib

namespace DRConvexOpt.Spread

open MeasureTheory

/-- The auxiliary random variable `ũ` of Proposition 2 (p. 18): the first of the three auxiliary
coordinates of an outcome `ω = (z, (u, v, w)) ∈ ℝ^P × ℝ³`. -/
def uOf {nP : ℕ} (ω : (Fin nP → ℝ) × (ℝ × ℝ × ℝ)) : ℝ := ω.2.1

/-- The auxiliary random variable `ṽ` of Proposition 2 (p. 18): the second auxiliary coordinate. -/
def vOf {nP : ℕ} (ω : (Fin nP → ℝ) × (ℝ × ℝ × ℝ)) : ℝ := ω.2.2.1

/-- The auxiliary random variable `w̃` of Proposition 2 (p. 18): the third auxiliary coordinate. -/
def wOf {nP : ℕ} (ω : (Fin nP → ℝ) × (ℝ × ℝ × ℝ)) : ℝ := ω.2.2.2

/-- Proposition 2, p. 17: the conditional mean `E_Q[fᵀz̃ | fᵀz̃ ≥ θ]`, read as the elementary
conditional expectation `E_Q[fᵀz̃ · 1{fᵀz̃ ≥ θ}] / Q[fᵀz̃ ≥ θ]`. It is meaningful only when `Q` is a
probability measure under which `fᵀz̃` is integrable and the event has positive probability; every
statement using it carries those hypotheses. -/
noncomputable def condMeanGe {nP : ℕ} (ν : Measure (Fin nP → ℝ)) (f : Fin nP → ℝ) (θ : ℝ) : ℝ :=
  (∫ z in {z | θ ≤ f ⬝ᵥ z}, f ⬝ᵥ z ∂ν) / ν.real {z | θ ≤ f ⬝ᵥ z}

/-- Proposition 2, p. 17: the conditional mean `E_Q[fᵀz̃ | fᵀz̃ < θ]`, read as
`E_Q[fᵀz̃ · 1{fᵀz̃ < θ}] / Q[fᵀz̃ < θ]` (same caveats as `condMeanGe`). -/
noncomputable def condMeanLt {nP : ℕ} (ν : Measure (Fin nP → ℝ)) (f : Fin nP → ℝ) (θ : ℝ) : ℝ :=
  (∫ z in {z | f ⬝ᵥ z < θ}, f ⬝ᵥ z ∂ν) / ν.real {z | f ⬝ᵥ z < θ}

/-- Proposition 2, p. 18, right-hand set: the probability distributions `Q` on `ℝ^P` under which
`fᵀz̃` has a finite mean, `Q[fᵀz̃ ≥ θ] = ρ`, and the absolute mean spread
`E_Q[fᵀz̃ | fᵀz̃ ≥ θ] − E_Q[fᵀz̃ | fᵀz̃ < θ]` is at most `σ`. -/
def spreadSet {nP : ℕ} (f : Fin nP → ℝ) (θ σ ρ : ℝ) : Set (Measure (Fin nP → ℝ)) :=
  {ν | IsProbabilityMeasure ν ∧ Integrable (fun z => f ⬝ᵥ z) ν ∧
    ν.real {z | θ ≤ f ⬝ᵥ z} = ρ ∧ condMeanGe ν f θ - condMeanLt ν f θ ≤ σ}

/-- Proposition 2, p. 18: the lifted ambiguity set `𝒫` of probability distributions of
`(z̃, ũ, ṽ, w̃)` on `ℝ^P × ℝ³` with `E_P[w̃] = σ` (`w̃` integrable),
`P[fᵀz̃ = θ + ũ − ṽ, w̃ ≥ ρ⁻¹ũ + (1 − ρ)⁻¹ṽ, ũ ≥ 0, ṽ ≥ 0] = 1` and `P[fᵀz̃ ≥ θ] = ρ`. -/
def liftedSpreadSet {nP : ℕ} (f : Fin nP → ℝ) (θ σ ρ : ℝ) :
    Set (Measure ((Fin nP → ℝ) × (ℝ × ℝ × ℝ))) :=
  {μ | IsProbabilityMeasure μ ∧ Integrable wOf μ ∧ ∫ ω, wOf ω ∂μ = σ ∧
    μ {ω | f ⬝ᵥ ω.1 = θ + uOf ω - vOf ω ∧ ρ⁻¹ * uOf ω + (1 - ρ)⁻¹ * vOf ω ≤ wOf ω ∧
      0 ≤ uOf ω ∧ 0 ≤ vOf ω} = 1 ∧
    μ.real {ω | θ ≤ f ⬝ᵥ ω.1} = ρ}

end DRConvexOpt.Spread


