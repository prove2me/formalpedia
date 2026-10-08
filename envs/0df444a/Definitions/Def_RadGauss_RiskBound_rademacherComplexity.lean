-- Prove2me | Definitions.Def_RadGauss_RiskBound_rademacherComplexity
-- name    : RadGauss_RiskBound_rademacherComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:01:18.753648+00:00
-- url     : https://prove2.me/theorems/cc1db189-47ea-406f-a7c2-d866cd1fe7d8
-- title:
--   Definition 2 — Rademacher complexity $R_n(F) = \mathbf E\sup_{f\in F}\left|\frac2n\sum_i \sigma_i f(X_i)\right|$
-- statement:
--   Let $\mu$ be a probability measure on a measurable space $\mathcal Z$, let $n \ge 1$, and let $G$ be a class of functions $\mathcal Z \to \mathbb R$. For a sample $x = (x_1, \dots, x_n) \in \mathcal Z^n$, the **empirical Rademacher complexity** of $G$ is
--
--   $$\hat R_n(G)(x) = \mathbf E_\sigma\left[\sup_{g \in G}\left|\frac{2}{n}\sum_{i=1}^n \sigma_i\, g(x_i)\right|\right] = \frac{1}{2^n}\sum_{\sigma \in \{\pm1\}^n}\ \sup_{g\in G}\left|\frac{2}{n}\sum_{i=1}^n \sigma_i\, g(x_i)\right|,$$
--
--   where $\sigma_1, \dots, \sigma_n$ are independent signs, each uniform on $\{-1, +1\}$; the expectation over the signs is exactly the average over all $2^n$ sign vectors. The **Rademacher complexity** of $G$ is the expectation of $\hat R_n(G)$ over an i.i.d. sample $X_1, \dots, X_n$ drawn from $\mu$:
--
--   $$R_n(G) = \mathbf E\, \hat R_n(G)(X_1, \dots, X_n).$$
--
--   Both quantities measure how well functions in $G$ can correlate with a random sign sequence on the sample. They are the complexity penalties of the risk bounds of Bartlett and Mendelson; note the factor $2/n$ and the absolute value inside the supremum, which distinguish this normalization from the $1/n$, absolute-value-free one of other texts.
--
--   **Formalization Note** The sign vector is a map $\sigma : \{1,\dots,n\} \to \mathrm{Bool}$ with `true` read as $+1$ and `false` as $-1$ (`signVal`). Both complexities take values in $[0, \infty]$ (`ℝ≥0∞`): the supremum is the supremum of $[0,\infty]$-valued terms, so an unbounded class has complexity $+\infty$ and the empty class has complexity $0$, and $R_n$ is the Lebesgue (lower) integral of $\hat R_n$ against the product measure $\mu^n$. This avoids the junk value $0$ that a real supremum of an unbounded set or a Bochner integral of a non-integrable function would give.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 464 (PDF p. 2), Definition 2

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace RadGauss.RiskBound

/-- The ±1 value encoded by a Boolean sign: `true ↦ 1`, `false ↦ -1`. -/
def signVal (b : Bool) : ℝ := if b then 1 else -1

/-- **Definition 2** (p. 464), the empirical Rademacher complexity
`R̂_n(G) = E[ sup_{g ∈ G} |(2/n) Σ_{i=1}^n σ_i g(x_i)| | x_1, …, x_n ]` of a class `G` of real
functions at the sample `x = (x_1, …, x_n)`. The expectation over independent uniform signs
`σ_1, …, σ_n ∈ {±1}` is the average over all `2^n` sign vectors `σ : Fin n → Bool`
(encoded by `signVal`). Values are in `ℝ≥0∞`, so an unbounded class has complexity `⊤`
and the empty class has complexity `0`. -/
noncomputable def empiricalRademacher {Z : Type*} (n : ℕ) (G : Set (Z → ℝ))
    (x : Fin n → Z) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) ^ n)⁻¹ *
    ∑ σ : Fin n → Bool, ⨆ g ∈ G, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, signVal (σ i) * g (x i)|

/-- **Definition 2** (p. 464), the Rademacher complexity `R_n(G) = E R̂_n(G)`: the expectation
of the empirical Rademacher complexity over an i.i.d. sample `x_1, …, x_n` drawn from the
probability measure `μ`, as a lower Lebesgue integral in `ℝ≥0∞`. -/
noncomputable def rademacherComplexity {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (n : ℕ) (G : Set (Z → ℝ)) : ℝ≥0∞ :=
  ∫⁻ x, empiricalRademacher n G x ∂(Measure.pi fun _ : Fin n => μ)

end RadGauss.RiskBound


