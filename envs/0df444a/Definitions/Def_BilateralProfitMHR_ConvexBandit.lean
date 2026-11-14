-- Prove2me | Definitions.Def_BilateralProfitMHR_ConvexBandit
-- name    : BilateralProfitMHR_ConvexBandit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-13T19:18:34.791736+00:00
-- url     : https://prove2.me/theorems/2f2e84d9-b2b7-4b51-a3a2-982f3a4d6acb
-- title:
--   §3.3 — stochastic convex bandits: query algorithms, observation kernels, the noise condition and the expected cumulative loss
-- statement:
--   This file sets up the stochastic convex bandit problem of Corollary 3.1.
--
--   A learner makes queries $x_1,x_2,\dots$ in a set $\mathcal K$ and, after querying $x_\tau$, observes $L(x_\tau)+\xi_\tau$. A **query algorithm** draws a seed $\omega$ from a probability space and chooses $x_\tau$ as a measurable function of $\omega$ and the earlier observations. An **environment** is a measurable kernel that gives the law of the next observation as a function of the past queries, the past observations and the current query.
--
--   The **noise condition** with loss $L$ and level $\gamma\ge0$ requires that, for every history of queries in $\mathcal K$ and observations and every query $x\in\mathcal K$, the observation has a probability law with mean $L(x)$ and the centered observation $\xi$ satisfies $\|\xi\|_{\psi_2}\le\gamma$, where $\|\cdot\|_{\psi_2}$ is the subgaussian norm of Definition 5.2.
--
--   For a nonnegative per-query quantity $g$ (for example $g(x)=L(x)-\min_{\mathcal K}L$), the **expected cumulative loss**
--   $$\mathbb E\Big[\sum_{\tau=1}^n g(x_\tau)\Big]$$
--   is computed over the seed and the observations by integrating the observations one query at a time.
--
--   **Formalization Note** The environment sees the learner's seed only through the queries. Expectations are taken in $[0,\infty]$, so no integrability side condition is needed.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), §3.3 "Stochastic Convex Bandits", p.10 (PDF 12); Corollary 3.1, pp.10–11, 30 (PDF 12–13, 32); Definition 5.2, p.31 (PDF 33). After Lattimore and György, Improved regret for zeroth-order stochastic convex bandits, COLT 2021, PMLR 134:2938–2964

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2

namespace BilateralProfitMHR

open MeasureTheory
open scoped ENNReal

/-! # Stochastic convex bandits (the setting of Corollary 3.1)

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), §3.3 "Stochastic Convex
Bandits", p.10 (PDF 12) and Corollary 3.1, pp.10–11, 30, 58 (PDF 12–13, 32, 60), after
Lattimore and György, *Improved regret for zeroth-order stochastic convex bandits*, COLT 2021.

A learner queries points `x_τ ∈ 𝒦` and observes `L(x_τ) + ξ_τ`; conditional on previous queries
and observations, and on `x_τ`, the noise `ξ_τ` has mean zero and `ψ₂` norm at most `γ`.

**Formalization Note.** Queries live in a measurable space `X` (`ℝ^d` or `ℝ²`). An algorithm
is a seed `ω` from a probability space and, for every `τ`, a query `x_τ = query τ ω (y_0, …,
y_{τ−1})` that is a measurable function of the seed and the past observations (the past queries
are functions of these). An *environment* is a measurable kernel `ν` giving the law of the
observation at the query `x` after the past queries `xs` and past observations `ys`; the noise
condition is imposed for every history whose queries lie in `𝒦`. The environment sees the
seed only through the queries (the learner's private randomness is independent of the noise
given the visible history). The expected cumulative value of a nonnegative per-query quantity
`g(x_τ)` over `n` queries is computed by nested integration over the observations, in
`ℝ≥0∞` (no integrability side conditions). -/

/-- A query algorithm with seed space `Ω` and query space `X`. -/
structure QueryAlg (X Ω : Type) [MeasurableSpace X] [MeasurableSpace Ω] where
  /-- the `τ`-th query (0-based) given the seed and the observations `y_0, …, y_{τ−1}` -/
  query : (τ : ℕ) → Ω → (Fin τ → ℝ) → X
  query_measurable : ∀ τ, Measurable fun z : Ω × (Fin τ → ℝ) => query τ z.1 z.2

variable {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]

/-- Every query of the algorithm lies in `𝒦`. -/
def QueryAlg.IsOn (A : QueryAlg X Ω) (K : Set X) : Prop := ∀ τ ω y, A.query τ ω y ∈ K

/-- The past queries `x_0, …, x_{τ−1}` determined by the seed and the observations `y`. -/
def QueryAlg.pastQueries (A : QueryAlg X Ω) (ω : Ω) {τ : ℕ} (y : Fin τ → ℝ) : Fin τ → X :=
  fun i => A.query i ω (fun j => y (Fin.castLE i.isLt.le j))

/-- An environment: the law of the observation at the query `x`, given the past queries and
observations. -/
abbrev ObsKernel (X : Type) : Type :=
  (τ : ℕ) → (Fin τ → X) → (Fin τ → ℝ) → X → Measure ℝ

/-- The environment is a measurable kernel in the history and the query. -/
def ObsKernel.IsMeasurable (ν : ObsKernel X) : Prop :=
  ∀ τ, Measurable fun w : (Fin τ → X) × (Fin τ → ℝ) × X => ν τ w.1 w.2.1 w.2.2

/-- The noise condition of Corollary 3.1 for the loss `L` on `𝒦` with `ψ₂` bound `γ`: given any
history of queries in `𝒦` and observations, and a query `x ∈ 𝒦`, the observation is
`L(x) + ξ` with `ξ` of mean zero and `‖ξ‖_{ψ₂} ≤ γ`. -/
def NoiseCond (K : Set X) (L : X → ℝ) (γ : ℝ) (ν : ObsKernel X) : Prop :=
  ∀ (τ : ℕ) (xs : Fin τ → X) (ys : Fin τ → ℝ) (x : X), (∀ i, xs i ∈ K) → x ∈ K →
    IsProbabilityMeasure (ν τ xs ys x) ∧ Integrable (fun z : ℝ => z) (ν τ xs ys x) ∧
      ∫ z, z ∂(ν τ xs ys x) = L x ∧
      HighDimProb.Concentration.subgaussianNorm (ν τ xs ys x) (fun z => z - L x) ≤
        ENNReal.ofReal γ

/-- `cumLoss A ν g ω m τ y`: the conditional expectation, given the seed `ω` and the first `τ`
observations `y`, of `∑_{s = τ}^{τ + m − 1} g(x_s)`. -/
noncomputable def cumLoss (A : QueryAlg X Ω) (ν : ObsKernel X) (g : X → ℝ≥0∞) (ω : Ω) :
    (m τ : ℕ) → (Fin τ → ℝ) → ℝ≥0∞
  | 0, _, _ => 0
  | m + 1, τ, y =>
      g (A.query τ ω y) +
        ∫⁻ z, cumLoss A ν g ω m (τ + 1) (Fin.snoc (α := fun _ => ℝ) y z)
          ∂(ν τ (A.pastQueries ω y) y (A.query τ ω y))

/-- `E[∑_{τ=1}^n g(x_τ)]` over the seed `ω ∼ P` and the observations. -/
noncomputable def expectedCumLoss (A : QueryAlg X Ω) (P : Measure Ω) (ν : ObsKernel X)
    (g : X → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, cumLoss A ν g ω n 0 Fin.elim0 ∂P

end BilateralProfitMHR


