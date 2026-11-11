-- Prove2me | Definitions.Def_MemoSDPI_Main_ProductBernoulli
-- name    : MemoSDPI_Main_ProductBernoulli
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:41:05.565015+00:00
-- url     : https://prove2.me/theorems/23a1b5d2-11e3-4d11-9eaa-2c422ae9f596
-- title:
--   Product Bernoulli laws on {0,1}^d and the product probit-normal prior of scale σ
-- statement:
--   For $\theta \in [0,1]^d$, the **product Bernoulli distribution** $\mathrm{Ber}(\theta_1) \otimes \cdots \otimes \mathrm{Ber}(\theta_d)$ on $\{0,1\}^d$ has independent coordinates with $\Pr[x_j = 1] = \theta_j$; its mean is $\theta$.
--
--   Let $\Phi$ be the cumulative distribution function of the standard Gaussian. The **probit-normal prior of scale $\sigma$** is the law of $\Phi(G)$ for $G \sim N(0, \sigma^2)$; the **product probit-normal prior** on $[0,1]^d$ is the law of
--   $$
--   \theta = (\Phi(G_1), \dots, \Phi(G_d)), \qquad G_1, \dots, G_d \text{ independent } N(0,\sigma^2).
--   $$
--   These are the data distributions and the prior of the average-case problems of Theorems 3.3 and 4.2.
--
--   **Formalization Note** $\{0,1\}$ is `Bool` (`true` $= 1$) and $[d]$ is `Fin d`. A mean vector is `θ : Fin d → unitInterval`, so $\theta \in [0,1]^d$ by its type; coordinate $j$ is Mathlib's `bernoulliMeasure true false (θ j)` (mass $\theta_j$ on `true`). The module records that the product law is a probability measure and bundles it as a `ProbabilityMeasure` (a member of the family of all product Bernoulli distributions). $\Phi$ is `cdf (gaussianReal 0 1)`, packaged with its values in $[0,1]$; the prior is the pushforward of $N(0,\sigma^2)^{\otimes d}$ (variance `(σ^2).toNNReal`) under $g \mapsto (\Phi(g_j))_j$.
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 12, §3.2; p. 13, §3.2 (probit-normal prior); p. 16, Theorem 4.2

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MemoSDPI.Main

/-- **Product Bernoulli distribution** `Ber(θ_1) ⊗ ⋯ ⊗ Ber(θ_d)` on `{0,1}^d` with mean
`θ ∈ [0, 1]^d` (Feldman, Lyu, Talwar, *Lower Bounds for Memorization, Privacy and Replicability
from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission (manuscript sha256
dbb300da…), p. 12, §3.2).

**Formalization Note.** `{0,1}` is `Bool` (`true` = 1) and `[d]` is `Fin d`; the mean vector is
`θ : Fin d → unitInterval`, so `θ ∈ [0, 1]^d` by its type. Coordinate `j` is Mathlib's
`bernoulliMeasure true false (θ j)`, mass `θ j` on `true`. -/
noncomputable def prodBernoulli {d : ℕ} (θ : Fin d → unitInterval) : Measure (Fin d → Bool) :=
  Measure.pi fun j => bernoulliMeasure true false (θ j)

/-- The product Bernoulli law is a probability measure. -/
instance prodBernoulli_isProb {d : ℕ} (θ : Fin d → unitInterval) :
    IsProbabilityMeasure (prodBernoulli θ) := by
  unfold prodBernoulli; infer_instance

/-- The product Bernoulli law as a bundled probability measure (a member of the family of all
product Bernoulli distributions on `{0,1}^d`). -/
noncomputable def prodBernoulliPM {d : ℕ} (θ : Fin d → unitInterval) :
    ProbabilityMeasure (Fin d → Bool) :=
  ⟨prodBernoulli θ, inferInstance⟩

/-- **Probit map** `g ↦ Φ(g)` (p. 13, §3.2), with `Φ` the cdf of the standard Gaussian, as a
point of `[0, 1]`. -/
noncomputable def probit (g : ℝ) : unitInterval :=
  ⟨cdf (gaussianReal 0 1) g, cdf_nonneg _ g, cdf_le_one _ g⟩

/-- **Product probit-normal prior of scale `σ`** on `[0, 1]^d` (p. 13, §3.2; p. 16, Theorem 4.2):
the law of `θ = (Φ(G_1), …, Φ(G_d))` for independent `G_j ∼ N(0, σ²)`.

**Formalization Note.** Pushforward of `N(0, σ²)^{⊗d}` (variance `σ²` as an `ℝ≥0`) under the
coordinatewise probit map. -/
noncomputable def probitPrior (σ : ℝ) (d : ℕ) : Measure (Fin d → unitInterval) :=
  (Measure.pi fun _ : Fin d => gaussianReal 0 (σ ^ 2).toNNReal).map fun g j => probit (g j)

end MemoSDPI.Main


