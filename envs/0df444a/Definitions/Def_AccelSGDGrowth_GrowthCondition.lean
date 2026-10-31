-- Prove2me | Definitions.Def_AccelSGDGrowth_GrowthCondition
-- name    : AccelSGDGrowth_GrowthCondition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:30.371126+00:00
-- url     : https://prove2.me/theorems/b1da2d15-9e7e-40e1-81b5-d1edb9d1c063
-- title:
--   The growth condition (Definition 1.1) in the conditional form (2.5)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a measure space with a filtration $(\mathcal G_k)_{k\in\mathbb N}$, let $f:\mathbb R^d\to\mathbb R$, and let $x_k,g_k:\Omega\to\mathbb R^d$ be the iterates and the stochastic gradients. Write $\varepsilon_k=g_k-\nabla f(x_k)$ for the gradient noise. The pair $(x,g)$ satisfies the **growth condition** with constants $\delta$ and $\sigma^2$ if, for every $k\ge1$:
--
--   1. $g_k$ is $\mathcal G_{k+1}$-measurable;
--   2. $\|\varepsilon_k\|^2$ is integrable;
--   3. $\mathbb E[\varepsilon_k\mid\mathcal G_k]=0$ almost surely;
--   4. almost surely,
--   $$
--   \mathbb E\big[\|\varepsilon_k\|^2\,\big|\,\mathcal G_k\big]\le\delta\,\|\nabla f(x_k)\|^2+\sigma^2 .
--   $$
--
--   This is Definition 1.1, $\mathbb E\|\varepsilon(x)\|^2\le\delta\|\nabla f(x)\|^2+\sigma^2$, applied along the iterates in the form (2.5) the paper uses in its analysis. With $\delta=0$ it reduces to a bounded-variance oracle.
--
--   **Formalization Note** Indices start at 1; index 0 is unused. Integrability of $\|\varepsilon_k\|^2$ is explicit because Lean's conditional expectation of a non-integrable function is $0$. $\delta\ge0$ and $\sigma^2\ge0$ are imposed by the theorems.
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, Definition 1.1 and (1.7), p.3; (2.5), p.6

import Mathlib

open MeasureTheory

namespace AccelSGDGrowth

/-- The growth condition of Chen, Na, Kolar, arXiv:2006.06782v4, Definition 1.1, p.3, in the
conditional form (2.5), p.6, along a sequence of query points.

On a measure space `(Ω, μ)` with a filtration `𝒢` indexed by `ℕ`, the iterates `x k : Ω → ℝ^d` and
the stochastic gradients `g k : Ω → ℝ^d` satisfy, for every `k ≥ 1`, with the noise
`ε_k = g_k - ∇f(x_k)`:
1. `g k` is `𝒢 (k+1)`-strongly measurable (the gradient realized at step `k` is known at step `k+1`);
2. `‖ε_k‖²` is integrable;
3. `E[ε_k | 𝒢_k] = 0` almost surely;
4. `E[‖ε_k‖² | 𝒢_k] ≤ δ‖∇f(x_k)‖² + σ²` almost surely, with `sig2 = σ²`.

**Formalization Note.** Indices start at 1; index 0 of the sequences is unused. The paper writes
(1.7) for a noise family `ε(x)` and derives (2.5) from it; (2.5) is assumed directly, which every
oracle of Definition 1.1 satisfies. Integrability of `‖ε_k‖²` is explicit because Lean's conditional
expectation of a non-integrable function is `0`. The constants' signs `δ ≥ 0`, `σ² ≥ 0` are carried by
the theorems. -/
def GrowthCondition {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (𝒢 : Filtration ℕ mΩ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (δ sig2 : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    StronglyMeasurable[𝒢 (k + 1)] (g k) ∧
    Integrable (fun ω => ‖g k ω - gradient f (x k ω)‖ ^ 2) μ ∧
    μ[fun ω => g k ω - gradient f (x k ω) | 𝒢 k] =ᵐ[μ] 0 ∧
    μ[fun ω => ‖g k ω - gradient f (x k ω)‖ ^ 2 | 𝒢 k] ≤ᵐ[μ]
      fun ω => δ * ‖gradient f (x k ω)‖ ^ 2 + sig2

end AccelSGDGrowth


