-- Prove2me | Definitions.Def_AgnHalfMem_halfVarRadius
-- name    : AgnHalfMem_halfVarRadius
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:10:44.952273+00:00
-- url     : https://prove2.me/theorems/c157e63e-6595-41ee-961f-dedece60b441
-- title:
--   The normalized difference law $\mu'$ and the half-variance radius $L_\mu$
-- statement:
--   Let $\mu$ be a probability distribution on $\mathbb R$ with variance $0<\sigma^2<\infty$, and let $X,X'$ be independent with law $\mu$. The law $\mu'$ is the distribution of
--   $$
--   Z=\frac{X-X'}{\sqrt2\,\sigma},
--   $$
--   and the **half-variance radius** of $\mu$ is
--   $$
--   L_\mu=\inf\Big\{L\ge 1:\ \mathbb E\big[Z^2\,\mathbf 1\{|Z|\le L\}\big]\ge \tfrac12\Big\}.
--   $$
--   Since $\mathbb E[Z^2]=1$, the set is nonempty and $1\le L_\mu<\infty$. The parameter measures how much of the variance of $\mu$ comes from typical rather than rare large deviations; the lower bound holds for $\varepsilon\ge CL_\mu/\sqrt d$.
--
--   **Formalization Note** $\sigma=\sqrt{\mathrm{Var}(X)}$; the truncated second moment is a set integral of $z^2$ over $\{|z|\le L\}$ against $\mu'$.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Definition 4.6, p.13; proof of Lemma 4.7, p.13

import Mathlib

open MeasureTheory ProbabilityTheory

namespace AgnHalfMem

/-- **The law `μ′` of the normalized difference `Z = (X − X′)/(√2 σ)`.** S. Garg, T. Jadhav,
*Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript,
PDF sha256 386bc9b3…43f84d5), Definition 4.6, p.13: "Let X, X′ be independent and drawn from
distribution μ, where 0 < σ² = Var(X) < ∞, and define Z = (X − X′)/(√2 σ)"; p.13 (proof of
Lemma 4.7): "We denote the distribution of Z₁ by μ′."

**Formalization Note.** `σ = √Var(X)` with `Var` Mathlib's `variance id μ`; the law is the image
of `μ ⊗ μ` under `(x, x′) ↦ (x − x′)/(√2 σ)`. It is used only for probability measures `μ` with
finite non-zero variance. -/
noncomputable def diffLaw (μ : Measure ℝ) : Measure ℝ :=
  (μ.prod μ).map (fun p : ℝ × ℝ => (p.1 - p.2) / (Real.sqrt 2 * Real.sqrt (variance id μ)))

/-- **Half-variance radius (Definition 4.6, p.13).** "We call Lμ ≥ 1 the half-variance radius for
distribution μ, which is defined as follows: Lμ = inf_{L ≥ 1} { E[Z² 1{|Z| ≤ L}] ≥ 1/2 }. Note that
since E[Z²] = 1, Lμ is finite."

`halfVarRadius μ` is the infimum of the `L ≥ 1` with `E[Z² 1{|Z| ≤ L}] ≥ 1/2`, `Z ∼ μ′`.

**Formalization Note.** The truncated second moment is the set integral of `z²` over
`{|z| ≤ L}` against `μ′ = diffLaw μ` (the integrand is bounded there, so the integral is always
the true one). For a probability measure with finite non-zero variance the defining set is
nonempty (as the page notes) and bounded below by `1`, so the infimum is a real number `≥ 1`. -/
noncomputable def halfVarRadius (μ : Measure ℝ) : ℝ :=
  sInf {L : ℝ | 1 ≤ L ∧ (1 / 2 : ℝ) ≤ ∫ z in {z : ℝ | |z| ≤ L}, z ^ 2 ∂(diffLaw μ)}

end AgnHalfMem


