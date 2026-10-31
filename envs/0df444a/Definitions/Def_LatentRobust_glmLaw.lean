-- Prove2me | Definitions.Def_LatentRobust_glmLaw
-- name    : LatentRobust_glmLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:24.925428+00:00
-- url     : https://prove2.me/theorems/b7029842-bb45-43ab-abaa-82420567db26
-- title:
--   The latent generalized linear model (6)
-- statement:
--   The **latent generalized linear model** (6) has parameters $W\in\mathbb R^{d\times k}$, a linear predictor $\beta\in\mathbb R^k$, a link function $f:\mathbb R\to[0,1]$ and $\varphi:\mathbb R\to\mathbb R$:
--   $$
--   y=\begin{cases}+1&\text{w.p. } f(z^\top\beta),\\ -1&\text{w.p. } 1-f(z^\top\beta),\end{cases}\qquad x=\varphi(Wz),\qquad z\sim\mathsf N(0,I_k).
--   $$
--   The joint law of $(x,y)$ is the pushforward of $\mathsf N(0,I_k)$ reweighted by the conditional label probabilities:
--   $$
--   \mathrm{Law}_{f(z^\top\beta)\,\mathsf N(0,I_k)}\big(\varphi(Wz),+1\big)+\mathrm{Law}_{(1-f(z^\top\beta))\,\mathsf N(0,I_k)}\big(\varphi(Wz),-1\big).
--   $$
--
--   This is the second classification setting of the paper; Corollary 2.3 gives its Bayes-optimal classifier.
--
--   **Formalization Note** The law is a measure on $\mathbb R^d\times\mathbb R$; it is a probability measure when $f$ is measurable with values in $[0,1]$.
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, §2.2, pp.6–7 eq. (6)

import Mathlib
import Definitions.Def_LatentRobust_latentFeature

namespace LatentRobust

open MeasureTheory

/-- The parameters of the latent generalized linear model (6) (Javanmard, Mehrabi,
arXiv:2110.11950v2, §2.2, pp.6–7): the weight matrix `W ∈ ℝ^{d×k}`, the linear predictor
`β ∈ ℝ^k`, the link function `f : ℝ → [0, 1]`, and the entrywise map `φ : ℝ → ℝ`. -/
structure LatentGLM (d k : ℕ) where
  /-- the weight matrix `W ∈ ℝ^{d×k}` -/
  W : Matrix (Fin d) (Fin k) ℝ
  /-- the linear predictor `β ∈ ℝ^k` -/
  β : Fin k → ℝ
  /-- the link function `f` -/
  f : ℝ → ℝ
  /-- the entrywise map `φ : ℝ → ℝ` -/
  φ : ℝ → ℝ

/-- The joint law of `(x, y)` under the latent generalized linear model (6) (Javanmard, Mehrabi,
arXiv:2110.11950v2, p.7): `z ∼ N(0, I_k)`, `y = +1` with probability `f(zᵀβ)` and `y = −1`
with probability `1 − f(zᵀβ)` given `z`, and `x = φ(Wz)`.

**Formalization Note** The law on `ℝ^d × ℝ` (feature, label) is
`Law_{z ∼ f(zᵀβ)·N(0,I_k)}(φ(Wz), +1) + Law_{z ∼ (1 − f(zᵀβ))·N(0,I_k)}(φ(Wz), −1)`, i.e. the
pushforwards of `N(0, I_k)` reweighted by the conditional label probabilities. It is a
probability measure when `0 ≤ f ≤ 1` and `f` is measurable. -/
noncomputable def glmLaw {d k : ℕ} (N : LatentGLM d k) : Measure ((Fin d → ℝ) × ℝ) :=
  ((stdNormal k).withDensity (fun z => ENNReal.ofReal (N.f (z ⬝ᵥ N.β)))).map
      (fun z => (latentFeature N.W N.φ z, (1 : ℝ))) +
    ((stdNormal k).withDensity (fun z => ENNReal.ofReal (1 - N.f (z ⬝ᵥ N.β)))).map
      (fun z => (latentFeature N.W N.φ z, (-1 : ℝ)))

end LatentRobust


