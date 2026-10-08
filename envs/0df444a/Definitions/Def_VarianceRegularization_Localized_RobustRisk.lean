-- Prove2me | Definitions.Def_VarianceRegularization_Localized_RobustRisk
-- name    : VarianceRegularization_Localized_RobustRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:13:12.940544+00:00
-- url     : https://prove2.me/theorems/75abd11d-67b5-472f-8202-55cfb3d4b4d9
-- title:
--   Eqs. (4), (8) — the χ² ball around the empirical distribution, the robust risk, and the empirical mean and variance
-- statement:
--   This module fixes the empirical objects of Duchi and Namkoong's variance-based regularization.
--
--   Let $x_1,\dots,x_n$ be a sample from a space $\mathcal X$, $n\ge 1$, and let $\widehat P_n$ be its empirical distribution. With $\phi(t)=\frac12(t-1)^2$, a distribution $p=(p_1,\dots,p_n)$ on the sample points has $\phi$-divergence $D_\phi(p\|\widehat P_n)=\frac1n\sum_{i=1}^n\phi(np_i)$ from $\widehat P_n$.
--
--   1. **The $\chi^2$ ball** of radius $\rho$ is the set of weight vectors
--   $$
--   \mathcal P_n=\Big\{p\in\mathbb R^n : p_i\ge 0,\ \sum_{i=1}^n p_i=1,\ \frac12\sum_{i=1}^n (np_i-1)^2\le\rho\Big\},
--   $$
--   which is exactly $\{p : D_\phi(p\|\widehat P_n)\le\rho/n\}$ (eq. (8)).
--   2. **The robust risk** of values $z_1,\dots,z_n$ is $\sup_{p\in\mathcal P_n}\sum_i p_iz_i$, and the robust risk of a function $f:\mathcal X\to\mathbb R$ at the sample is
--   $$
--   \sup_{P:\,D_\phi(P\|\widehat P_n)\le\rho/n}\mathbb E_P[f]=\sup_{p\in\mathcal P_n}\sum_{i=1}^n p_i f(x_i)\qquad\text{(eq. (4))}.
--   $$
--   3. **The empirical mean and variance** are $\mathbb E_{\widehat P_n}[f]=\frac1n\sum_i f(x_i)$ and $\mathrm{Var}_{\widehat P_n}(f)=\frac1n\sum_i f(x_i)^2-\big(\mathbb E_{\widehat P_n}[f]\big)^2$, normalized by $1/n$.
--
--   The robust risk is the objective whose minimizer the mission studies; Theorem 1 relates it to the empirical mean plus a standard-deviation penalty.
--
--   **Formalization Note** Distributions on the sample are weight vectors indexed by $\{1,\dots,n\}$ (`Fin n`); when sample values are tied, the supremum over weight vectors equals the supremum over distributions on the distinct points (split the mass of tied points equally; $\phi$ is convex). The supremum is the real `sSup` of the image of the ball; for $n\ge1$ and $\rho\ge0$ the ball contains the uniform weights and is compact, so the supremum is attained.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 2, eq. (4); p. 5, eq. (8); p. 7, Theorem 1 (s_n^2)

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_chiSqBall
import Definitions.Def_VarianceRegularization_Expansion_robustSup

namespace VarianceRegularization.Localized

open MeasureTheory

/-- The robust risk of `f` at the sample `s = (x₁, …, x_n)`:
`sup_{P : D_φ(P ‖ P̂_n) ≤ ρ/n} E_P[f]`. -/
noncomputable def robustRisk {X : Type*} {n : ℕ} (ρ : ℝ) (s : Fin n → X) (f : X → ℝ) : ℝ :=
  VarianceRegularization.Expansion.robustSup n ρ (fun i => f (s i))

/-- The empirical mean `E_{P̂_n}[f] = (1/n) ∑ᵢ f(xᵢ)`. -/
noncomputable def empMean {X : Type*} {n : ℕ} (s : Fin n → X) (f : X → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, f (s i)

/-- The empirical variance `Var_{P̂_n}(f) = E_{P̂_n}[f²] − (E_{P̂_n}[f])²` (normalized by `1/n`). -/
noncomputable def empVar {X : Type*} {n : ℕ} (s : Fin n → X) (f : X → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (f (s i)) ^ 2 - (empMean s f) ^ 2

end VarianceRegularization.Localized


