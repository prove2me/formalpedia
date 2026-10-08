-- Prove2me | Definitions.Def_WassKF_Reform_GaussianBall
-- name    : WassKF_Reform_GaussianBall
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:09:02.155238+00:00
-- url     : https://prove2.me/theorems/0d50b19a-b133-4f08-9c5d-3721b51462f8
-- title:
--   (3), p. 3 — the Wasserstein ball of normal distributions $\{\mathbb Q \in \mathcal N_d : W_2(\mathbb Q, \mathbb P) \le \rho\}$
-- statement:
--   Let $n, m \ge 0$, $d = n + m$, and identify $\mathbb R^d$ with pairs $z = [x; y]$ of a signal $x \in \mathbb R^n$ and an observation $y \in \mathbb R^m$. Fix a nominal mean $\mu \in \mathbb R^d$, a nominal covariance matrix $\Sigma \in \mathbb R^{d \times d}$ and a radius $\rho \in \mathbb R$, and write $\mathbb P = \mathcal N_d(\mu, \Sigma)$.
--
--   The **Wasserstein ambiguity set** of normal distributions is
--
--   $$
--   \mathcal P = \bigl\{\mathbb Q \in \mathcal N_d \;:\; W_2(\mathbb Q, \mathbb P) \le \rho\bigr\},
--   $$
--
--   that is, the set of all normal distributions $\mathbb Q = \mathcal N_d(c, S)$ with mean $c \in \mathbb R^d$ and positive semidefinite covariance $S \in \mathbb S^d_+$ (degenerate covariances are allowed) whose type-2 Wasserstein distance to $\mathbb P$ is at most $\rho$. The distance $W_2$ is the coupling definition (Definition 2.1): the infimum, over all probability distributions on $\mathbb R^d \times \mathbb R^d$ with marginals $\mathbb Q$ and $\mathbb P$, of the square root of the expected squared Euclidean distance.
--
--   This set is the adversary's feasible set in the minimax estimation problem (2). It is not convex, since mixtures of normal distributions are generically not normal.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin n ⊕ Fin m)`; the `Sum.inl` coordinates are $x$ and the `Sum.inr` coordinates are $y$. $\mathcal N_d(c, S)$ is Mathlib's `multivariateGaussian c S`, required here to have `S.PosSemidef`. $W_2$ is the published `WassersteinDRO.Shrinkage.wassersteinDistance 2`, valued in $[0,\infty]$, and the radius enters as `ENNReal.ofReal ρ`. The ball is not defined through the closed-form (Gelbrich) expression for $W_2$ between normals; that expression is Proposition 2.2.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 3, (3); Notation and Definition 2.1, p. 2

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_wassersteinDistance

open MeasureTheory ProbabilityTheory

namespace WassKF.Reform

/-- The Wasserstein ambiguity set (3) of Shafieezadeh-Abadeh et al. (arXiv:1809.08830v3, p. 3):
the normal distributions `Q = 𝒩_d(c, S)` (mean `c`, covariance `S ⪰ 0`, degenerate `S` allowed)
whose type-2 Wasserstein distance (Definition 2.1, coupling form) to the nominal
`ℙ = 𝒩_d(μ, Sig)` is at most `ρ`. Here `d = n + m` and `ℝ^d` is `EuclideanSpace ℝ (Fin n ⊕ Fin m)`,
the `Sum.inl` coordinates being the signal `x` and the `Sum.inr` coordinates the observation `y`. -/
noncomputable def GaussianBall {n m : ℕ} (μ : EuclideanSpace ℝ (Fin n ⊕ Fin m))
    (Sig : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (ρ : ℝ) :
    Set (Measure (EuclideanSpace ℝ (Fin n ⊕ Fin m))) :=
  {Q | ∃ (c : EuclideanSpace ℝ (Fin n ⊕ Fin m)) (S : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ),
    S.PosSemidef ∧ Q = multivariateGaussian c S ∧
    WassersteinDRO.Shrinkage.wassersteinDistance 2 Q (multivariateGaussian μ Sig) ≤ ENNReal.ofReal ρ}

end WassKF.Reform


