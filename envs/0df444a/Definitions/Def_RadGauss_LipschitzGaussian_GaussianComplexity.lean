-- Prove2me | Definitions.Def_RadGauss_LipschitzGaussian_GaussianComplexity
-- name    : RadGauss_LipschitzGaussian_GaussianComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:40:13.515477+00:00
-- url     : https://prove2.me/theorems/3f84b965-be60-4d50-aad2-cfaac3b10888
-- title:
--   Definition 2 — Gaussian complexity Ĝ_n(F) = E[sup_{f∈F} |(2/n) Σ g_i f(X_i)| | X_1,…,X_n], G_n(F) = E Ĝ_n(F)
-- statement:
--   Let $\mathcal Z$ be a set and $F$ a class of functions $f : \mathcal Z \to \mathbb R$. For a sample size $n$ and a sample $x = (x_1, \dots, x_n) \in \mathcal Z^n$, the **empirical Gaussian complexity** of $F$ at $x$ is
--
--   $$
--   \hat G_n(F)(x) = \mathbb E\left[\,\sup_{f\in F}\left|\frac 2n \sum_{i=1}^n g_i f(x_i)\right|\,\right],
--   $$
--
--   where $g_1, \dots, g_n$ are independent standard Gaussian $N(0,1)$ random variables. If $\mu$ is a probability measure on $\mathcal Z$ and $X_1, \dots, X_n$ are independent with law $\mu$, the **Gaussian complexity** of $F$ is $G_n(F) = \mathbb E\, \hat G_n(F)(X_1, \dots, X_n)$.
--
--   These are the Gaussian averages of Bartlett and Mendelson's Definition 2; they measure how well functions of the class can correlate with Gaussian noise on the sample, and every statement of this mission is phrased in terms of them.
--
--   **Formalization Note** The Gaussian vector $(g_1,\dots,g_n)$ is the coordinate vector under the product measure $N(0,1)^{\otimes n}$ on $\mathbb R^n$, and the sample is drawn from the product measure $\mu^{\otimes n}$. Both expectations are lower Lebesgue integrals with values in $[0,\infty]$: an unbounded class has complexity $+\infty$ (rather than the junk value $0$ a real supremum would give), and the empty class has complexity $0$.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 464 (PDF p. 2), Definition 2

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RadGauss.LipschitzGaussian

/-- **Definition 2** (p. 464), the empirical Gaussian complexity
`Ĝ_n(F) = E[ sup_{f ∈ F} |(2/n) Σ_{i=1}^n g_i f(x_i)| | x_1, …, x_n ]` of a class `F` of real
functions at the sample `x = (x_1, …, x_n)`, where `g_1, …, g_n` are independent standard
Gaussian `N(0,1)` variables. The Gaussian vector is the coordinate vector of the product measure
`N(0,1)^{⊗n}` on `Fin n → ℝ`, and the expectation is a lower Lebesgue integral in `ℝ≥0∞`, so an
unbounded class has complexity `⊤` and the empty class has complexity `0`. -/
noncomputable def empiricalGaussian {Z : Type*} (n : ℕ) (F : Set (Z → ℝ)) (x : Fin n → Z) :
    ℝ≥0∞ :=
  ∫⁻ g : Fin n → ℝ, ⨆ f ∈ F, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, g i * f (x i)|
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)

/-- **Definition 2** (p. 464), the Gaussian complexity `G_n(F) = E Ĝ_n(F)`: the expectation of
the empirical Gaussian complexity over an i.i.d. sample `X_1, …, X_n` drawn from the
probability measure `μ` (the product measure `μ^{⊗n}`), as a lower Lebesgue integral in `ℝ≥0∞`. -/
noncomputable def gaussianComplexity {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (n : ℕ)
    (F : Set (Z → ℝ)) : ℝ≥0∞ :=
  ∫⁻ x, empiricalGaussian n F x ∂(Measure.pi fun _ : Fin n => μ)

end RadGauss.LipschitzGaussian


