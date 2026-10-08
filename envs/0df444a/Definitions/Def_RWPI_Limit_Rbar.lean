-- Prove2me | Definitions.Def_RWPI_Limit_Rbar
-- name    : RWPI_Limit_Rbar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:10:52.091062+00:00
-- url     : https://prove2.me/theorems/f3e66de7-180d-4f45-989e-9f1dbb848545
-- title:
--   The limit functional $\bar R(\rho)$ and the covariance $\mathrm{Cov}[h(W, \theta_*)]$ of Theorem 3
-- statement:
--   Let $W$ be a random vector in $\mathbb R^m$ on a probability space, let $h : \mathbb R^m \times \mathbb R^l \to \mathbb R^r$, $\theta_* \in \mathbb R^l$, $p \in [1,\infty]$ and $\rho \ge 1$. Write $\|\zeta^T D_w h(W, \theta_*)\|_p$ for the $\ell_p$ norm of the row vector $\zeta^T D_w h(W, \theta_*)$. For $x \in \mathbb R^r$ (standing for the Gaussian vector $H$), this file defines
--
--   1. for $\rho > 1$,
--   $$
--   \bar R(\rho)(x) = \sup_{\zeta \in \mathbb R^r} \Big\{ \rho\, \zeta^T x - (\rho - 1)\, \mathbb E\big\|\zeta^T D_w h(W, \theta_*)\big\|_p^{\rho/(\rho - 1)} \Big\};
--   $$
--   2. for $\rho = 1$,
--   $$
--   \bar R(1)(x) = \sup\Big\{ \zeta^T x \;:\; \zeta \in \mathbb R^r,\ \mathbb P\big(\|\zeta^T D_w h(W, \theta_*)\|_p > 1\big) = 0 \Big\};
--   $$
--   3. the matrix $\mathrm{Cov}[h(W, \theta_*)] = \mathbb E\big[h(W, \theta_*)\, h(W, \theta_*)^T\big] \in \mathbb R^{r \times r}$.
--
--   The paper writes "max" in 1–2; Theorem 3 asserts that the supremum is attained. Evaluated at $x = H \sim \mathcal N(0, \mathrm{Cov}[h(W, \theta_*)])$, $\bar R(\rho)$ is the random variable that stochastically bounds the rescaled RWP function $n^{\rho/2} R_n(\theta_*)$.
--
--   **Formalization Note.** The expectation $\mathbb E\|\cdot\|_p^{\rho/(\rho-1)}$ is a lower Lebesgue integral in $[0,\infty]$, and the objective and the supremum are computed in the extended reals; an infinite moment makes the objective $-\infty$, never a junk value. The feasible set is all of $\mathbb R^r$ when $\rho \neq 1$. The matrix $\mathrm{Cov}$ is the matrix of second moments, which is the covariance matrix when $\mathbb E[h(W,\theta_*)] = 0$.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 15, Theorem 3 (definitions of R̄(ρ), R̄(1) and Cov[h(W, θ*)])

import Mathlib
import Definitions.Def_RWPI_Limit_rowNorm

open MeasureTheory

namespace RWPI.Limit

/-- `E ‖ζ^T D_w h(W, θ)‖_p^{ρ/(ρ−1)}` (Theorem 3, p. 15), for a random vector `W0 : Ω → ℝ^m` on
`(Ω, μ)`. It is the lower Lebesgue integral of a nonnegative quantity, so it is `⊤` (never a junk
`0`) when the moment is infinite. -/
noncomputable def rowMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m l r : ℕ}
    (W0 : Ω → (Fin m → ℝ)) (p : ENNReal) (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ))
    (θ : Fin l → ℝ) (ρ : ℝ) (ζ : Fin r → ℝ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (rowNorm p h θ ζ (W0 ω) ^ (ρ / (ρ - 1))) ∂μ

/-- The feasible set of the maximisation defining `R̄(ρ)` (Theorem 3, p. 15): all of `ℝ^r` when
`ρ > 1`, and `{ζ : P(‖ζ^T D_w h(W, θ)‖_p > 1) = 0}` when `ρ = 1`. -/
def RbarFeasible {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m l r : ℕ}
    (W0 : Ω → (Fin m → ℝ)) (p : ENNReal) (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ))
    (θ : Fin l → ℝ) (ρ : ℝ) : Set (Fin r → ℝ) :=
  if ρ = 1 then {ζ | μ {ω | 1 < rowNorm p h θ ζ (W0 ω)} = 0} else Set.univ

/-- The objective of the maximisation defining `R̄(ρ)` at `H = x` (Theorem 3, p. 15):
`ρ ζ^T x − (ρ − 1) E‖ζ^T D_w h(W, θ)‖_p^{ρ/(ρ−1)}` when `ρ > 1` (equal to `−∞` when the moment
is infinite), and `ζ^T x` when `ρ = 1`. -/
noncomputable def RbarObjective {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m l r : ℕ}
    (W0 : Ω → (Fin m → ℝ)) (p : ENNReal) (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ))
    (θ : Fin l → ℝ) (ρ : ℝ) (x : EuclideanSpace ℝ (Fin r)) (ζ : Fin r → ℝ) : EReal :=
  if ρ = 1 then ((∑ j, ζ j * x j : ℝ) : EReal)
  else ((ρ * ∑ j, ζ j * x j : ℝ) : EReal)
    - ((ENNReal.ofReal (ρ - 1) * rowMoment μ W0 p h θ ρ ζ : ENNReal) : EReal)

/-- `R̄(ρ)` evaluated at `H = x` (Theorem 3, p. 15): the supremum of `RbarObjective` over
`RbarFeasible`, taken in `EReal`. Theorem 3 asserts in addition that this supremum is a maximum. -/
noncomputable def Rbar {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m l r : ℕ}
    (W0 : Ω → (Fin m → ℝ)) (p : ENNReal) (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ))
    (θ : Fin l → ℝ) (ρ : ℝ) (x : EuclideanSpace ℝ (Fin r)) : EReal :=
  ⨆ ζ ∈ RbarFeasible μ W0 p h θ ρ, RbarObjective μ W0 p h θ ρ x ζ

/-- `Cov[h(W, θ)] = E[h(W, θ) h(W, θ)^T]` (Theorem 3, p. 15), the `r × r` matrix of second
moments of `h(W0, θ)`. -/
noncomputable def covMatrix {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m l r : ℕ}
    (W0 : Ω → (Fin m → ℝ)) (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ))
    (θ : Fin l → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun j k => ∫ ω, h (W0 ω) θ j * h (W0 ω) θ k ∂μ

end RWPI.Limit


