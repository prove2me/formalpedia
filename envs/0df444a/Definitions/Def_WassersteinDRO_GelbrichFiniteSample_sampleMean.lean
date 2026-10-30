-- Prove2me | Definitions.Def_WassersteinDRO_GelbrichFiniteSample_sampleMean
-- name    : WassersteinDRO_GelbrichFiniteSample_sampleMean
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:54:52.218995+00:00
-- url     : https://prove2.me/theorems/1aa8013d-136d-41f9-9437-31d172da642c
-- title:
--   Sample mean $\widehat\mu$
-- statement:
--   Let $\widehat\xi_1, \dots, \widehat\xi_N \in \mathbb R^m$ be training samples. The **sample mean** is
--
--   $$\widehat\mu = \frac1N \sum_{i=1}^N \widehat\xi_i,$$
--
--   the mean vector of the empirical distribution of the samples. It is the $\widehat\mu$ of Theorems 21 and 22.
--
--   **Formalization Note** $\mathbb R^m$ is `EuclideanSpace ℝ (Fin m)` and the samples are indexed by `Fin N`. For $N = 0$ the formula returns $0$; every statement using it assumes $N \ge 1$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §4.3, definition of the sample mean and covariance, p. 27

import Mathlib

namespace WassersteinDRO.GelbrichFiniteSample

/-- **The sample mean `µ̂`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, §4.3, definition of the sample mean and covariance, p. 27: "the sample mean µ̂ and the sample
covariance matrix Σ̂, which we define as the actual mean and covariance matrix of the empirical
distribution, i.e., µ̂ = (1/N) Σ_{i=1}^N ξ̂i". This is the µ̂ of Theorems 21 and 22 (p. 23).

`sampleMean ξh = N⁻¹ • ∑ᵢ ξh i` for the training samples `ξh : Fin N → ℝ^m`.

**Formalization Note.** `ℝ^m` is `EuclideanSpace ℝ (Fin m)`, whose norm is the Euclidean norm
`‖·‖₂`. The samples are indexed by `Fin N` (the paper's `i ∈ {1, …, N}`). For `N = 0` the value
is `0` (`0⁻¹ = 0` in Lean); every statement that uses it assumes `0 < N`. -/
noncomputable def sampleMean {m N : ℕ} (ξh : Fin N → EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  (N : ℝ)⁻¹ • ∑ i, ξh i

end WassersteinDRO.GelbrichFiniteSample


