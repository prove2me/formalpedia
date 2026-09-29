-- Prove2me | Definitions.Def_RobustMeanCov_Projection_MeanCovClass
-- name    : RobustMeanCov_Projection_MeanCovClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:42:42.223935+00:00
-- url     : https://prove2.me/theorems/d843d020-c8a4-481f-894a-b39b72f88f10
-- title:
--   The class $\mathbb{M}^n_{(\mu,\Sigma)}$ of laws on $\mathbb{R}^n$ with mean $\mu$ and covariance $\Sigma$
-- statement:
--   Fix a dimension $n$, a vector $\mu \in \mathbb{R}^n$ and a real $n\times n$ matrix $\Sigma$. The class $\mathbb{M}^n_{(\mu,\Sigma)}$ is the set of Borel probability measures $P$ on $\mathbb{R}^n$ such that
--
--   1. every coordinate $R_i$ has a finite second moment under $P$;
--   2. the mean vector of $P$ is $\mu$;
--   3. the covariance matrix of $P$ is $\Sigma$:
--
--   $$
--   \int R_i \, dP(R) = \mu_i, \qquad \int (R_i-\mu_i)(R_j-\mu_j)\, dP(R) = \Sigma_{ij} \quad (1\le i,j\le n).
--   $$
--
--   Writing $\mathbf R \sim (\mu,\Sigma)$ means that the law of the random vector $\mathbf R$ lies in this class. It is the ambiguity set of the robust mean-covariance problem $\min_{\mathbf R\sim(\mu,\Sigma)} E[u(x'\mathbf R)]$.
--
--   **Formalization Note** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)` with its Borel σ-algebra, and $\Sigma$ is written `S` because `Σ` is a reserved token in Lean. The finite-second-moment clause (`MemLp … 2`) makes the mean and covariance integrals genuine; without it a heavy-tailed law would receive the default value $0$. Positive semidefiniteness of $\Sigma$ is not part of the class; it is a hypothesis of the theorems.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, https://doi.org/10.1287/opre.1060.0353, p. 98 (§1, after (1): notation R ∼ (μ, Σ) and 𝕄ⁿ_(μ,Σ)) and p. 100 (§2.1, after Proposition 1: 'the set of probability measures on ℝⁿ with mean μ and covariance Σ')

import Mathlib
open MeasureTheory

namespace RobustMeanCov.Projection

/-- The class `𝕄ⁿ_(μ,Σ)` (Popescu 2007, p. 98 and p. 100): probability measures `P` on `ℝⁿ`
(modelled as `EuclideanSpace ℝ (Fin n)` with its Borel σ-algebra) whose coordinates have finite
second moments, with mean vector `μ` and covariance matrix `S` (the paper's `Σ`). -/
def MeanCovClass {n : ℕ} (μ : EuclideanSpace ℝ (Fin n)) (S : Matrix (Fin n) (Fin n) ℝ) :
    Set (Measure (EuclideanSpace ℝ (Fin n))) :=
  {P | IsProbabilityMeasure P ∧
    (∀ i, MemLp (fun R : EuclideanSpace ℝ (Fin n) => R i) 2 P) ∧
    (∀ i, ∫ R, R i ∂P = μ i) ∧
    (∀ i j, ∫ R, (R i - μ i) * (R j - μ j) ∂P = S i j)}

end RobustMeanCov.Projection


