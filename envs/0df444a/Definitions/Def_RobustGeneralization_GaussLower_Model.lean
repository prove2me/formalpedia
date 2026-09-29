-- Prove2me | Definitions.Def_RobustGeneralization_GaussLower_Model
-- name    : RobustGeneralization_GaussLower_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:14:17.873807+00:00
-- url     : https://prove2.me/theorems/d1eab6bc-752d-4da5-8eea-c70b35535020
-- title:
--   The (θ⋆, σ)-Gaussian model, ℓ∞^ε-robust classification error, and the expected robust error of a learning algorithm (Defs. 1–3, §A.2)
-- statement:
--   This file fixes the objects of the Gaussian lower bound of Schmidt, Santurkar, Tsipras, Talwar and Mądry.
--
--   Write $\mathbb R^d$ for the feature space and $\{\pm1\}$ for the labels. For $x \in \mathbb R^d$ and $\varepsilon \in \mathbb R$ the **$\ell_\infty$ perturbation set** is
--
--   $$\mathcal B_\infty^\varepsilon(x) = \{x' \in \mathbb R^d : \|x' - x\|_\infty \le \varepsilon\}.$$
--
--   For $m \in \mathbb R^d$ and $s \in \mathbb R$, $\mathcal N(m, s^2 I)$ is the law of $m + s v$ with $v$ a standard Gaussian vector in $\mathbb R^d$.
--
--   1. **Gaussian model** (Definition 1). For $\theta^\star \in \mathbb R^d$ and $\sigma > 0$, the $(\theta^\star, \sigma)$-Gaussian model is the law of $(x, y)$ where $y$ is uniform on $\{\pm 1\}$ and, given $y$, $x \sim \mathcal N(y\,\theta^\star, \sigma^2 I)$.
--   2. **Robust classification error** (Definitions 2–3). For a distribution $P$ on $\mathbb R^d \times \{\pm1\}$ and a classifier $f : \mathbb R^d \to \{\pm 1\}$,
--   $$\beta_\varepsilon(f; P) = \mathbb P_{(x,y)\sim P}\big[\exists\, x' \in \mathcal B_\infty^\varepsilon(x) : f(x') \ne y\big].$$
--   3. **Expected robust error of a learning algorithm** (proof of Theorem 11). A learning algorithm $g_n$ maps $n$ samples $S = ((x_1,y_1),\dots,(x_n,y_n))$ to a classifier $f_n = g_n(S)$. Its expected robust error is
--   $$\Xi = \mathbb E_{\theta \sim \mathcal N(0, I)}\ \mathbb E_{S \sim P_{\theta,\sigma}^{\otimes n}}\big[\beta_\varepsilon(g_n(S); P_{\theta,\sigma})\big],$$
--   where $P_{\theta,\sigma}$ is the $(\theta,\sigma)$-Gaussian model. The learner sees the samples but not $\theta$.
--   4. **Marginal of the unlabelled samples and posterior** (§A.2, p. 28). $\mathcal M$ is the law of $(z_1,\dots,z_n)$ when $\theta \sim \mathcal N(0,I)$ and, given $\theta$, the $z_i$ are i.i.d. $\mathcal N(\theta, \sigma^2 I)$. For $z = (z_1,\dots,z_n)$ the posterior is $\mathcal N(\mu', \Sigma')$ with
--   $$\mu' = \frac{1}{\sigma^2 + n}\sum_{i=1}^n z_i, \qquad \Sigma' = \frac{\sigma^2}{\sigma^2+n} I.$$
--
--   These are the objects in which Theorem 11 and Corollary 23 are stated.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with its Borel σ-algebra. It carries the $\ell_2$ norm, so the $\ell_\infty$ ball is written coordinatewise, $|x'_i - x_i| \le \varepsilon$ for all $i$. The label $+1$ is `true` and $-1$ is `false`. The parameter `s` of `gaussVec m s` is the **standard deviation**. Definition 1 calls $\sigma$ "the variance parameter", but it samples from $\mathcal N(y\theta^\star, \sigma^2 I)$. The robust event is an $\ell_\infty$-thickening and need not be Borel, so the measure of it is the outer measure, which is its probability under the completion of $P$. A learning algorithm is a function `(Fin n → ℝ^d × Bool) → ℝ^d → Bool`, and the samples form the product measure `Measure.pi`. The expectations are lower Lebesgue integrals `∫⁻`. The posterior mean is written as $(\sigma^2+n)^{-1}\sum_i z_i$, which equals $\frac{n}{\sigma^2+n}\bar z$ with $\bar z$ the sample mean and is defined at $n = 0$.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 4, Definition 1; p. 5, Definitions 2–3 and B∞^ε; p. 28, §A.2, proof of Theorem 11 (Ξ, µ′, Σ′, M)

import Mathlib

namespace RobustGeneralization.GaussLower

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The feature space `ℝ^d`, with its Euclidean structure and Borel σ-algebra. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The ℓ∞ perturbation set `B∞^ε(x) = {x' ∈ ℝ^d | ‖x' − x‖∞ ≤ ε}` (Schmidt et al., arXiv:1804.11285v2,
p. 5, after Definition 3), written coordinatewise: `E d` carries the ℓ2 norm, so
`Metric.closedBall` would be the ℓ2 ball. -/
def linfBall {d : ℕ} (x : E d) (ε : ℝ) : Set (E d) :=
  {x' | ∀ i, |x' i - x i| ≤ ε}

/-- The Gaussian `N(m, s²I)` on `ℝ^d`: the law of `m + s • v` for `v` standard Gaussian.
`s` is the standard deviation. -/
noncomputable def gaussVec {d : ℕ} (m : E d) (s : ℝ) : Measure (E d) :=
  (stdGaussian (E d)).map (fun v => m + s • v)

/-- The `(θ⋆, σ)`-Gaussian model (Definition 1, p. 4): the label `y ∈ {±1}` is uniform
(`true` = +1, `false` = −1) and, given `y`, `x ∼ N(y · θ⋆, σ²I)`. The measure is the joint
law of `(x, y)` on `ℝ^d × {±1}`. -/
noncomputable def gaussModel {d : ℕ} (θ : E d) (σ : ℝ) : Measure (E d × Bool) :=
  (1 / 2 : ℝ≥0∞) • (gaussVec θ σ).map (fun x => (x, true)) +
    (1 / 2 : ℝ≥0∞) • (gaussVec (-θ) σ).map (fun x => (x, false))

/-- The `ℓ∞^ε`-robust classification error of a classifier `f : ℝ^d → {±1}` under a
distribution `P` on `ℝ^d × {±1}` (Definition 3, p. 5, with `B = B∞^ε`):
`P_{(x,y)∼P}[∃ x' ∈ B∞^ε(x) : f(x') ≠ y]`. For a non-measurable event this is the outer
measure, i.e. the probability under the completion of `P`. -/
noncomputable def robustErr {d : ℕ} (P : Measure (E d × Bool)) (f : E d → Bool) (ε : ℝ) : ℝ≥0∞ :=
  P {p | ∃ x' ∈ linfBall p.1 ε, f x' ≠ p.2}

/-- The expected `ℓ∞^ε`-robust classification error `Ξ` of a learning algorithm
`g` on `n` samples (§A.2, proof of Theorem 11, p. 28): draw `θ ∼ N(0, I)`, then `n` i.i.d.
samples `S` from the `(θ, σ)`-Gaussian model, and average the robust error of `f_n = g S`
under the same model. The learner sees only `S`, never `θ`. -/
noncomputable def expRobErr {d n : ℕ} (g : (Fin n → E d × Bool) → E d → Bool) (σ ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ, ∫⁻ S, robustErr (gaussModel θ σ) (g S) ε
      ∂(Measure.pi fun _ : Fin n => gaussModel θ σ) ∂(stdGaussian (E d))

/-- The marginal law `M` of `(z_1, …, z_n)` (§A.2, p. 28), where `θ ∼ N(0, I)` and, given `θ`,
the `z_i` are i.i.d. `N(θ, σ²I)`. -/
noncomputable def sampleMarginal (d n : ℕ) (σ : ℝ) : Measure (Fin n → E d) :=
  (stdGaussian (E d)).bind (fun θ => Measure.pi fun _ : Fin n => gaussVec θ σ)

/-- The posterior of `θ` given `z_1, …, z_n` (§A.2, p. 28): `N(µ′, Σ′)` with
`µ′ = (σ² + n)⁻¹ ∑_i z_i` (that is, `n/(σ²+n)` times the sample mean) and
`Σ′ = σ²/(σ²+n) I`, i.e. standard deviation `σ / √(σ² + n)`. -/
noncomputable def posterior {d n : ℕ} (z : Fin n → E d) (σ : ℝ) : Measure (E d) :=
  gaussVec ((σ ^ 2 + n)⁻¹ • ∑ i, z i) (σ / Real.sqrt (σ ^ 2 + n))

end RobustGeneralization.GaussLower


