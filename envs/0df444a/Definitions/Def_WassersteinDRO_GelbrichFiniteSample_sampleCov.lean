-- Prove2me | Definitions.Def_WassersteinDRO_GelbrichFiniteSample_sampleCov
-- name    : WassersteinDRO_GelbrichFiniteSample_sampleCov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:55:25.484281+00:00
-- url     : https://prove2.me/theorems/4f0f9b16-b3a7-4177-915c-e691379fe38f
-- title:
--   Sample covariance matrix $\widehat\Sigma$ (normalized by $1/N$)
-- statement:
--   Let $\widehat\xi_1, \dots, \widehat\xi_N \in \mathbb R^m$ be training samples with sample mean $\widehat\mu$. The **sample covariance matrix** is
--
--   $$\widehat\Sigma = \frac1N \sum_{i=1}^N (\widehat\xi_i - \widehat\mu)(\widehat\xi_i - \widehat\mu)^\top,$$
--
--   the covariance matrix of the empirical distribution of the samples. It is the $\widehat\Sigma$ of Theorems 21 and 22. It is symmetric positive semidefinite.
--
--   **Formalization Note** The normalization is $1/N$, as in the paper, not the unbiased $1/(N-1)$. For $N = 0$ the formula returns the zero matrix; every statement using it assumes $N \ge 1$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §4.3, definition of the sample mean and covariance, p. 27

import Mathlib
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_sampleMean

namespace WassersteinDRO.GelbrichFiniteSample

/-- **The sample covariance matrix `Σ̂`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, §4.3, definition of the sample mean and covariance, p. 27: "the sample mean µ̂ and the sample
covariance matrix Σ̂, which we define as the actual mean and covariance matrix of the empirical
distribution, i.e., … Σ̂ = (1/N) Σ_{i=1}^N (ξ̂i − µ̂)(ξ̂i − µ̂)⊤". This is the Σ̂ of Theorems 21
and 22 (p. 23).

`sampleCov ξh` is the `m × m` matrix with entries
`Σ̂_{jk} = N⁻¹ ∑ᵢ (ξh i − µ̂)_j (ξh i − µ̂)_k`, where `µ̂ = sampleMean ξh`.

**Formalization Note.** The normalization is `1/N` (the covariance of the empirical distribution,
as the paper defines it), not the unbiased `1/(N − 1)`. For `N = 0` the value is the zero
matrix; every statement that uses it assumes `0 < N`. -/
noncomputable def sampleCov {m N : ℕ} (ξh : Fin N → EuclideanSpace ℝ (Fin m)) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun j k => (N : ℝ)⁻¹ * ∑ i, (ξh i - sampleMean ξh) j * (ξh i - sampleMean ξh) k

end WassersteinDRO.GelbrichFiniteSample


