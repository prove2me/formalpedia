-- Prove2me | Definitions.Def_LeiBR_Rand_Assumption1
-- name    : LeiBR_Rand_Assumption1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:26.914892+00:00
-- url     : https://prove2.me/theorems/ac9bc715-3453-4597-a8da-a9b5abe84e13
-- title:
--   Assumption 1 — the stochastic Nash game (SNash) and the constant $Q_i$
-- statement:
--   In the **stochastic Nash game** (SNash), player $i$'s cost is an expectation,
--   $$f_i(x_i, x_{-i}) = \mathbb E\big[\psi_i(x_i, x_{-i}; \xi)\big],$$
--   where $\xi$ is a random vector in $\mathbb R^d$ with law $\mu_\xi$ and $\psi_i$ is a scalar sampled cost. A stochastic oracle returns sampled gradients $\nabla_{x_i}\psi_i(x; \xi)$. **Assumption 1** requires:
--
--   1. each $X_i$ is closed, compact, convex (and nonempty);
--   2. $f_i(\cdot, x_{-i})$ is convex on an open set containing $X_i$ for every $x_{-i} \in X_{-i}$, and $f_i$ is twice continuously differentiable on an open set containing $X$;
--   3. for all $x_{-i} \in X_{-i}$ and (almost) every sample, $\psi_i(\cdot, x_{-i}; \xi)$ is differentiable on an open set containing $X_i$, and $\nabla_{x_i} f_i(x) = \mathbb E[\nabla_{x_i}\psi_i(x; \xi)]$ for $x \in X$;
--   4. there are constants $M_i > 0$ with $\mathbb E\big[\|\nabla_{x_i}\psi_i(x; \xi)\|^2\big] \le M_i^2$ for all $x \in X$.
--
--   With $D_{X_i} = \sup\{\|x_i - x_i'\| : x_i, x_i' \in X_i\}$ the diameter of $X_i$, define
--   $$Q_i = \frac{2M_i^2}{\mu^2} + 2D_{X_i}^2.$$
--
--   These are the standing hypotheses of every convergence and complexity statement of the paper; $Q_i$ is the constant of the $O(1/t)$ error bound of the stochastic gradient scheme.
--
--   **Formalization Note** The law of $\xi$ is a probability measure `μξ` on `EuclideanSpace ℝ (Fin d)`; `gψ i x s` is the sampled partial gradient $\nabla_{x_i}\psi_i(x; s)$. Expectations are Bochner integrals, and every one comes with an integrability hypothesis. Item 2 asks for joint $C^2$ regularity of $f_i$ in the whole profile (the paper says "in $x_i$"), because the mixed Hessian blocks $\nabla^2_{x_i x_j} f_i$ of (4) require it. The differentiability in item 3 is asked for $\mu_\xi$-almost every sample. Measurability of the sampled gradient in $(x, s)$, implicit in the paper, is stated as a field.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 4, (SNash_i); p. 5, Assumption 1; p. 8, (16); p. 10, Lemma 3 (Q_i)

import Mathlib
import Definitions.Def_LeiBR_Rand_Game

namespace LeiBR.Rand

open MeasureTheory

variable {N : ℕ} {n : Fin N → ℕ}

/-- Assumption 1 for the stochastic Nash game (SNash) (pp. 4–5). The random vector `ξ` takes values
in `ℝ^d` and has law `μξ`; `ψ i x s = ψ_i(x; s)` is player `i`'s sampled cost and
`gψ i x s = ∇_{x_i} ψ_i(x_i, x_{-i}; s)` its sampled partial gradient in `x_i`.

* `f_eq`: `f_i(x) = E[ψ_i(x; ξ)]` at every feasible profile, (SNash_i).
* (a) every `X_i` is closed, compact, convex and nonempty.
* (b) `f_i` is convex in `x_i` on an open set containing `X_i` for every feasible `x_{-i}`, and
  twice continuously differentiable (jointly in the whole profile, which the mixed Hessian blocks
  of (4) need) on an open set containing `X`.
* (c) `ψ_i(·, x_{-i}; s)` is differentiable with gradient `gψ` on an open set containing `X_i`
  (for a.e. sample `s`), and `∇_{x_i} f_i(x) = E[∇_{x_i} ψ_i(x; ξ)]` for feasible `x`.
* (d) `E‖∇_{x_i} ψ_i(x; ξ)‖² ≤ M_i²` for feasible `x`, with `M_i > 0`.
* Standing convention: the sampled gradient is jointly measurable in `(x, s)`. -/
structure Assumption1 (G : Game N n) {d : ℕ} (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ) : Prop where
  prob : IsProbabilityMeasure μξ
  f_eq : ∀ i x, G.Feasible x → Integrable (ψ i x) μξ ∧ G.f i x = ∫ s, ψ i x s ∂μξ
  closed : ∀ i, IsClosed (G.X i)
  compact : ∀ i, IsCompact (G.X i)
  convex : ∀ i, Convex ℝ (G.X i)
  nonempty : ∀ i, (G.X i).Nonempty
  convexOn : ∀ i y, G.Feasible y → ∃ V : Set (LeiBR.Sync.Strat n i), IsOpen V ∧ G.X i ⊆ V ∧
    ConvexOn ℝ V (fun z => G.f i (Function.update y i z))
  smooth : ∃ U : Set (LeiBR.Sync.Profile n), IsOpen U ∧ {x | G.Feasible x} ⊆ U ∧
    ∀ i, ContDiffOn ℝ 2 (G.f i) U
  gψ_meas : ∀ i, Measurable (Function.uncurry (gψ i))
  ψ_grad : ∀ i y, G.Feasible y → ∀ᵐ s ∂μξ, ∃ V : Set (LeiBR.Sync.Strat n i), IsOpen V ∧ G.X i ⊆ V ∧
    ∀ z ∈ V, HasGradientAt (fun z' => ψ i (Function.update y i z') s)
      (gψ i (Function.update y i z) s) z
  unbiased : ∀ i y, G.Feasible y → Integrable (gψ i y) μξ ∧
    gradient (fun z => G.f i (Function.update y i z)) (y i) = ∫ s, gψ i y s ∂μξ
  M_pos : ∀ i, 0 < M i
  moment : ∀ i x, G.Feasible x → Integrable (fun s => ‖gψ i x s‖ ^ 2) μξ ∧
    ∫ s, ‖gψ i x s‖ ^ 2 ∂μξ ≤ M i ^ 2

/-- `Q_i = 2M_i²/µ² + 2D_{X_i}²` (Lemma 3, p. 10), with `D_{X_i}` the diameter (16) of `X_i`. -/
noncomputable def Qconst (G : Game N n) (M : Fin N → ℝ) (mu : ℝ) (i : Fin N) : ℝ :=
  2 * M i ^ 2 / mu ^ 2 + 2 * Metric.diam (G.X i) ^ 2

end LeiBR.Rand


