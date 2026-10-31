-- Prove2me | Definitions.Def_LatentRobust_gmmLaw
-- name    : LatentRobust_gmmLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:29.361319+00:00
-- url     : https://prove2.me/theorems/d9295d89-0462-4f04-923b-2118803c7af2
-- title:
--   The latent Gaussian mixture model (5)
-- statement:
--   The **latent Gaussian mixture model** (5) has parameters $W\in\mathbb R^{d\times k}$, $\mu\in\mathbb R^k$, $\pi$ and $\varphi:\mathbb R\to\mathbb R$:
--   $$
--   y\sim\mathrm{Bern}(\pi,\{+1,-1\}),\qquad x=\varphi(Wz),\qquad z\sim\mathsf N(y\mu,I_k).
--   $$
--   The label is $+1$ with probability $\pi$ and $-1$ with probability $1-\pi$. Given $y$, $z=y\mu+g$ with $g\sim\mathsf N(0,I_k)$, so the joint law of $(x,y)$ is
--   $$
--   \pi\cdot\mathrm{Law}\big(\varphi(W(\mu+g)),+1\big)+(1-\pi)\cdot\mathrm{Law}\big(\varphi(W(-\mu+g)),-1\big).
--   $$
--
--   This is the data model of Theorem 3.1: features lie on the image of a $k$-dimensional space in $\mathbb R^d$.
--
--   **Formalization Note** The law is a measure on $\mathbb R^d\times\mathbb R$ built from the two pushforwards of $\mathsf N(0,I_k)$; the pushforward maps are measurable whenever $\varphi$ is (every theorem assumes $\varphi$ differentiable). It is a probability measure when $0\le\pi\le1$.
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, §2.2, p.6 eq. (5)

import Mathlib
import Definitions.Def_LatentRobust_latentFeature

namespace LatentRobust

open MeasureTheory

/-- The parameters of the latent Gaussian mixture model (5) (Javanmard, Mehrabi,
arXiv:2110.11950v2, §2.2, p.6): the weight matrix `W ∈ ℝ^{d×k}`, the mean `μ ∈ ℝ^k`, the
probability `π` of the label `+1`, and the entrywise link `φ : ℝ → ℝ`. -/
structure LatentGMM (d k : ℕ) where
  /-- the weight matrix `W ∈ ℝ^{d×k}` -/
  W : Matrix (Fin d) (Fin k) ℝ
  /-- the latent mean `μ ∈ ℝ^k` -/
  μ : Fin k → ℝ
  /-- the probability `π` of the label `+1` -/
  π : ℝ
  /-- the entrywise map `φ : ℝ → ℝ` -/
  φ : ℝ → ℝ

/-- The joint law of `(x, y)` under the latent Gaussian mixture model (5) (Javanmard, Mehrabi,
arXiv:2110.11950v2, §2.2, p.6):
`y ∼ Bern(π, {+1, −1})`, `x = φ(Wz)`, `z ∼ N(yμ, I_k)`.

Given `y`, `z = yμ + g` with `g ∼ N(0, I_k)`, so the law is
`π · Law(φ(W(μ + g)), +1) + (1 − π) · Law(φ(W(−μ + g)), −1)`.

**Formalization Note** The law lives on `ℝ^d × ℝ` (feature, label). It is the mixture of the two
pushforwards of `N(0, I_k)`; the pushforward maps are measurable whenever `φ` is (in particular
when `φ` is differentiable, as every theorem assumes). It is a probability measure when
`0 ≤ π ≤ 1`. -/
noncomputable def gmmLaw {d k : ℕ} (M : LatentGMM d k) : Measure ((Fin d → ℝ) × ℝ) :=
  ENNReal.ofReal M.π •
      (stdNormal k).map (fun g => (latentFeature M.W M.φ (M.μ + g), (1 : ℝ))) +
    ENNReal.ofReal (1 - M.π) •
      (stdNormal k).map (fun g => (latentFeature M.W M.φ (-M.μ + g), (-1 : ℝ)))

end LatentRobust


