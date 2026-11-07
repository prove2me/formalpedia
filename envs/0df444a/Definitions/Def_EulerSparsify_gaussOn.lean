-- Prove2me | Definitions.Def_EulerSparsify_gaussOn
-- name    : EulerSparsify_gaussOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:25.12185+00:00
-- url     : https://prove2.me/theorems/96525209-ff16-44ce-9872-da9268647888
-- title:
--   Gaussian measure restricted to a subspace $\gamma_S(K)$
-- statement:
--   $\gamma_d$ denotes the standard Gaussian measure on $\mathbb R^d$: $\gamma_d(K)=\Pr_{g\sim N(0_d,I_d)}[g\in K]$. For a linear subspace $S\subseteq\mathbb R^d$,
--
--   $$\gamma_S(K)=\Pr_{g\sim N(0_d,P_S)}[g\in K]=\Pr_{g\sim N(0_d,I_d)}[P_Sg\in K],$$
--
--   the Gaussian measure of $K$ restricted to $S$.
--
--   **Formalization Note** Mathlib's `stdGaussian` on the Euclidean space $\mathbb R^d$ (independent standard normal coordinates) and the orthogonal projection onto $S$.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §3, Distributions, p.8 (PDF p.10)

import Mathlib

namespace EulerSparsify

open MeasureTheory ProbabilityTheory

/-- **Gaussian measure restricted to a subspace** `γ_S(K)` (§3, "Distributions", p.8, PDF p.10).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), p.8: "We use γ_d to denote the Gaussian measure in dimension d, i.e., for K ⊆ ℝ^d,
γ_d(K) := Pr_{g∼N(0_d,I_d)}[g ∈ K]; when S is a linear subspace of ℝ^d, we define
γ_S(K) := Pr_{g∼N(0_d,P_S)}[g ∈ K]."

`gaussOn S K` is the standard Gaussian measure of `{g : P_S g ∈ K}`: `N(0, P_S)` is the law of
`P_S g` for `g ∼ N(0, I_d)`. The plain `γ_d` is `stdGaussian (EuclideanSpace ℝ (Fin d))`.

**Formalization Note.** The measure is Mathlib's `stdGaussian` on `EuclideanSpace ℝ (Fin d)`
(independent standard normal coordinates); `P_S` is the orthogonal projection
`S.starProjection`. -/
noncomputable def gaussOn {d : ℕ} (S : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (K : Set (EuclideanSpace ℝ (Fin d))) : ENNReal :=
  stdGaussian (EuclideanSpace ℝ (Fin d)) ((fun g => S.starProjection g) ⁻¹' K)

end EulerSparsify


