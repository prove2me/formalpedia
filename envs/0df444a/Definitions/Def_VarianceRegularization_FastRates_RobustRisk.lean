-- Prove2me | Definitions.Def_VarianceRegularization_FastRates_RobustRisk
-- name    : VarianceRegularization_FastRates_RobustRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:13:32.37426+00:00
-- url     : https://prove2.me/theorems/72d882c9-d273-41de-a277-d858dd339b7d
-- title:
--   Eq. (8) — the χ² ball 𝒫_n, the robust value, and the empirical mean and variance
-- statement:
--   Fix a sample size $n\ge 1$ and a radius $\rho\ge 0$. With $\phi(t)=\frac12(t-1)^2$, the $\chi^2$-neighbourhood of the empirical distribution $\widehat P_n$ consists of distributions supported on the sample, which we write as weight vectors
--
--   $$\mathcal P_n=\Big\{p\in\mathbb R^n_+ : \tfrac12\|np-\mathbf 1\|_2^2\le\rho,\ \langle\mathbf 1,p\rangle=1\Big\}.$$
--
--   For a vector $z\in\mathbb R^n$ of sample values, the **robust value** is
--   $$\sup_{p\in\mathcal P_n}\sum_{i=1}^n p_i z_i ,$$
--   which is the robustly regularized risk $R_n(\theta,\mathcal P_n)$ of eq. (4) when $z_i=\ell(\theta;X_i)$. The **empirical mean** and **empirical variance** are
--   $$\mathbb E_{\widehat P_n}[Z]=\frac1n\sum_{i=1}^n z_i,\qquad s_n^2=\mathrm{Var}_{\widehat P_n}(Z)=\frac1n\sum_{i=1}^n z_i^2-\Big(\frac1n\sum_{i=1}^n z_i\Big)^2 .$$
--
--   These are the objects in which the paper's variance expansion and its fast-rate theorem are stated.
--
--   **Formalization Note** The ball is the vector form (8) of the set $\{P: D_\phi(P\|\widehat P_n)\le\rho/n\}$ of eq. (4); with tied sample values the supremum of a linear functional over the two sets is the same. For $n\ge1$ and $\rho\ge0$ the set is nonempty and compact, so the real supremum is a maximum. The variance is normalized by $1/n$, as in the paper.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 2, eq. (4); p. 5, eq. (8); p. 7, Theorem 1 (definition of s_n^2)

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_chiSqBall
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_VarianceRegularization_Expansion_robustSup

namespace VarianceRegularization.FastRates

/-- Empirical variance `s_n² = 𝔼_{P̂_n}[Z²] − 𝔼_{P̂_n}[Z]²` (p. 7), normalised by `1/n`. -/
noncomputable def empVar {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (z i) ^ 2 - (VarianceRegularization.Expansion.empMean z) ^ 2

end VarianceRegularization.FastRates


