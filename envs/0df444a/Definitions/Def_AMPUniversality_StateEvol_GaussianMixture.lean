-- Prove2me | Definitions.Def_AMPUniversality_StateEvol_GaussianMixture
-- name    : AMPUniversality_StateEvol_GaussianMixture
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:26:31.34899+00:00
-- url     : https://prove2.me/theorems/5c3e45aa-b498-44cb-a396-c6c5d0fb309e
-- title:
--   Finite mixtures of possibly degenerate Gaussian laws, Definition 5(iv)
-- statement:
--   A finite Gaussian mixture is a probability law obtained by assigning nonnegative weights summing to one to finitely many multivariate Gaussian laws. Each component has a mean vector and a positive semidefinite covariance matrix; singular covariances, including point masses, are allowed.
--
--   This general distribution class supplies the label laws in Definition 5 and can be reused separately from the AMP model.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 8, Definition 5(iv)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AMPUniversality.StateEvol

/-- A finite mixture of possibly degenerate Gaussian measures. -/
def IsGaussianMixture {h : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin h))) : Prop :=
  ∃ (l : ℕ) (w : Fin l → ℝ≥0)
      (mean : Fin l → EuclideanSpace ℝ (Fin h))
      (cov : Fin l → Matrix (Fin h) (Fin h) ℝ),
    (∑ j, w j) = 1 ∧
    (∀ j, (cov j).PosSemidef) ∧
    μ = ∑ j, ((w j : ℝ≥0∞) • multivariateGaussian (mean j) (cov j))

end AMPUniversality.StateEvol


