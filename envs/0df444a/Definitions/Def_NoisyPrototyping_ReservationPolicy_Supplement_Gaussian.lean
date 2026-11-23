-- Prove2me | Definitions.Def_NoisyPrototyping_ReservationPolicy_Supplement_Gaussian
-- name    : NoisyPrototyping_ReservationPolicy_Supplement_Gaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:47:04.365219+00:00
-- url     : https://prove2.me/theorems/bf9b19ee-e242-4b27-85ad-beeda555531f
-- title:
--   §4, p. 12 — Gaussian value–measurement laws, the standard-normal root R(w), and the Gaussian indices R_i and adjusted values p_i
-- statement:
--   This file specializes the published noisy-search model of §3 to the Gaussian setting of §4.
--
--   **Fidelity.** Each prototype $i$ has a prior mean $\mu_i\in\mathbb R$, a prior standard deviation $\sigma_i>0$ and a measurement fidelity $\tau_i\in(0,\infty]$. Write $1/\tau_i$ for its reciprocal, with $1/\tau_i=0$ at perfect fidelity $\tau_i=\infty$.
--
--   **Joint law.** The true value is $P_i\sim\mathcal N(\mu_i,\sigma_i^2)$ and the measurement is $m_i=P_i+\epsilon_i$, where $\epsilon_i\sim\mathcal N(0,1/\tau_i^2)$ is independent of $P_i$ (and $\epsilon_i=0$ when $\tau_i=\infty$). Equivalently, $(P_i,m_i)$ is jointly normal with mean $(\mu_i,\mu_i)$ and covariance matrix
--   $$\begin{pmatrix}\sigma_i^2&\sigma_i^2\\ \sigma_i^2&\sigma_i^2+1/\tau_i^2\end{pmatrix}.$$
--   The **Gaussian search problem** has these joint laws and evaluation costs $w_i$; prototypes are independent through the published product outcome law.
--
--   **Standard-normal root.** For $w>0$, a real number $x$ is a solution of the equation defining $R(w)$ when
--   $$x=\mathbb E[\max\{x,Z\}]-w,\qquad Z\sim\mathcal N(0,1).$$
--
--   **Indices and adjusted values.** Given a function $R$ on the positive reals, the **fidelity-adjusted reservation price** and the **fidelity-adjusted value** after measurement $m$ are
--   $$R_i=\mu_i+\frac{\sigma_i}{\sqrt{1+1/(\tau_i\sigma_i)^2}}\,R\!\left(\frac{w_i\sqrt{1+1/(\tau_i\sigma_i)^2}}{\sigma_i}\right),\qquad p_i(m)=\mu_i+(m-\mu_i)\,\frac{1}{1+1/(\tau_i\sigma_i)^2}.$$
--   At perfect fidelity these reduce to $R_i=\mu_i+\sigma_iR(w_i/\sigma_i)$ and $p_i(m)=m$.
--
--   These objects are the data of Theorem 2; the policy, net payoff, admissibility and value are the published ones.
--
--   **Formalization Note** The fidelity is an extended nonnegative real `τ : ℝ≥0∞`, and $1/\tau$ is `(τ⁻¹).toNNReal`, which is $0$ at $\tau=\infty$; the noise variance is $(1/\tau)^2$, a Dirac mass at $0$ when it vanishes. The joint law is the push-forward of $\mathcal N(\mu,\sigma^2)\otimes\mathcal N(0,1/\tau^2)$ under $(P,\epsilon)\mapsto(P,P+\epsilon)$; it has no density at $\tau=\infty$, which the law-based published model allows. The positivity of $\sigma_i$, $\tau_i$ and $w_i$ is stated in the theorem, not here. `IsNormalRoot w x` is the defining equation of $R(w)$; no root is chosen in this file.
-- source:
--   Bhaskaran and Erat, Optimal Prototyping with Noisy Measurements, author manuscript of 6 Nov 2024 (MSOM 2025, doi:10.1287/msom.2024.1133), §4 and §4.1, p. 12 (Gaussian model; R(w), R_i and p_i in Theorem 2)

import Mathlib
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Model

namespace NoisyPrototyping.ReservationPolicy.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- `1/τ` for a fidelity `τ ∈ (0, ∞]`, as a real number; perfect fidelity `τ = ∞` gives `0`. -/
noncomputable def invFidelity (τ : ℝ≥0∞) : ℝ := ((τ⁻¹).toNNReal : ℝ)

/-- The §4 joint law of `(P, m)`: `P ∼ N(μ, σ²)` and `m = P + ϵ` with `ϵ ∼ N(0, 1/τ²)`
independent of `P` (`ϵ = 0` when `τ = ∞`). -/
noncomputable def gaussianLaw (μ σ : ℝ) (τ : ℝ≥0∞) : Measure (ℝ × ℝ) :=
  ((gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩).prod (gaussianReal 0 ((τ⁻¹).toNNReal ^ 2))).map
    (fun z : ℝ × ℝ => (z.1, z.1 + z.2))

/-- The Gaussian search problem of §4: prototype `i` has the joint law `gaussianLaw (μ i) (σ i)
(τ i)` and evaluation cost `w i`. -/
noncomputable def gaussianProblem {N : ℕ} (μ σ : Fin N → ℝ) (τ : Fin N → ℝ≥0∞)
    (w : Fin N → ℝ) : SearchProblem N where
  law i := gaussianLaw (μ i) (σ i) (τ i)
  cost := w

/-- `x` solves `x = E[max {x, Z}] − w` with `Z` standard normal (the equation defining `R(w)`). -/
def IsNormalRoot (w x : ℝ) : Prop :=
  x = (∫ z, max x z ∂(gaussianReal 0 1)) - w

/-- `√(1 + 1/(τσ)²)`. -/
noncomputable def fidelityFactor (σ : ℝ) (τ : ℝ≥0∞) : ℝ :=
  Real.sqrt (1 + (invFidelity τ / σ) ^ 2)

/-- The fidelity-adjusted reservation price of Theorem 2:
`R_i = μ_i + σ_i / √(1 + 1/(τ_iσ_i)²) · R(w_i √(1 + 1/(τ_iσ_i)²) / σ_i)`. -/
noncomputable def gaussianIndex (Rstd : ℝ → ℝ) (μ σ : ℝ) (τ : ℝ≥0∞) (w : ℝ) : ℝ :=
  μ + σ / fidelityFactor σ τ * Rstd (w * fidelityFactor σ τ / σ)

/-- The fidelity-adjusted value of Theorem 2: `p_i = μ_i + (m_i − μ_i) · 1/(1 + 1/(τ_iσ_i)²)`. -/
noncomputable def adjustedValue (μ σ : ℝ) (τ : ℝ≥0∞) (m : ℝ) : ℝ :=
  μ + (m - μ) * (1 / (1 + (invFidelity τ / σ) ^ 2))

end NoisyPrototyping.ReservationPolicy.Supplement


