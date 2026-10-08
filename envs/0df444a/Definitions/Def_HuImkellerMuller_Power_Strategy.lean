-- Prove2me | Definitions.Def_HuImkellerMuller_Power_Strategy
-- name    : HuImkellerMuller_Power_Strategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:42.096769+00:00
-- url     : https://prove2.me/theorems/774babe8-4085-4a1d-a840-7fc279f07d00
-- title:
--   (11), Definition 13 and (12), p. 16 — wealth of a proportional strategy, the admissible class Ã and the power-utility value
-- statement:
--   This file fixes the power-utility problem of §3 of Hu, Imkeller and Müller (2005), in the variable $\rho_t=\tilde\rho_t\sigma_t$, where $\tilde\rho_t\in\mathbb R^{1\times d}$ is the proportion of wealth invested in each stock.
--
--   1. **Wealth.** For an initial capital $x$ and an $\mathbb R^m$-valued process $\rho$, the wealth process (11) is the stochastic exponential
--   $$
--   X^{(\rho)}_t = x\exp\Big(\int_0^t\rho_s\,dW_s+\int_0^t\rho_s\theta_s\,ds-\tfrac12\int_0^t|\rho_s|^2\,ds\Big),\qquad t\in[0,T].
--   $$
--   2. **Admissible strategies** (Definition 13). $\tilde{\mathcal A}$ consists of the predictable $\mathbb R^m$-valued processes $\rho$ with $\rho_t\in C_t(\omega)$ for $\lambda\otimes P$-a.e. $(t,\omega)$ and $\int_0^T|\rho_s|^2\,ds<\infty$ $P$-a.s.
--   3. **Value** (12). For $\gamma\in(0,1)$ and the power utility $U_\gamma(x)=\frac1\gamma x^\gamma$,
--   $$
--   \bar V(x)=\sup_{\rho\in\tilde{\mathcal A}} E\big[U_\gamma(X^{(\rho)}_T)\big].
--   $$
--
--   Theorem 14 computes $\bar V$ through a quadratic BSDE.
--
--   **Formalization Note** The stochastic integral $\int_0^t\rho\,dW$ is `I ρ t` for an Itô-integral operator `I` (the published `IsItoIntegralOperator` pins it down for locally square-integrable integrands). The first form of (11), an SDE in the stock prices, is not encoded; the wealth is the paper's second, explicit form. Definition 13 says "$d$-dimensional", but $\rho=\tilde\rho\sigma$ takes values in $\mathbb R^{1\times m}$; optimizing over $\tilde\rho_t\in\tilde C$ is the same as over $\rho_t\in C_t$ because $\sigma_t$ has full rank. The expectation of the nonnegative utility is a lower integral in $[0,\infty]$, so a non-integrable $U_\gamma(X_T)$ cannot be replaced by a junk value $0$; the supremum is taken in $[0,\infty]$.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, §3, (11), Definition 13 and (12), pp. 15–16

import Mathlib
import Definitions.Def_HuImkellerMuller_Power_Market

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Power

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The wealth process (11), p. 16, in its stochastic-exponential form, written in the variable
`ρ_t = ρ̃_t σ_t`:
`X^{(ρ)}_t = x · exp(∫₀ᵗ ρ_s dW_s + ∫₀ᵗ ρ_s θ_s ds − ½ ∫₀ᵗ |ρ_s|² ds)`.
The stochastic integral `∫₀ᵗ ρ dW` is `I ρ t`, for an Itô-integral operator `I`. -/
noncomputable def wealth {d m : ℕ}
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) → ℝ≥0 → Ω → ℝ)
    (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ) (x : ℝ)
    (ρ : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x * Real.exp (I ρ t ω
    + (∫ u in Set.Icc (0 : ℝ) t, inner ℝ (ρ u.toNNReal ω) (HuImkellerMuller.Exponential.theta b σ u.toNNReal ω))
    - (1 / 2) * ∫ u in Set.Icc (0 : ℝ) t, ‖ρ u.toNNReal ω‖ ^ 2)

/-- Definition 13, p. 16, in the variable `ρ = ρ̃σ`: the admissible strategies `Ã` are the
predictable `ℝᵐ`-valued processes `ρ` with `ρ_t ∈ C_t(ω)` for `λ ⊗ P`-a.e. `(t, ω)` and
`∫₀ᵀ |ρ_s|² ds < ∞` `P`-a.s. -/
def Admissible {d m : ℕ} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ) (Ct : Set (Fin d → ℝ))
    (ρ : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) : Prop :=
  HuImkellerMuller.Exponential.IsPredictable 𝓕 ρ ∧
  (∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T),
    ρ q.1.toNNReal q.2 ∈ HuImkellerMuller.Exponential.Cset Ct σ q.1.toNNReal q.2) ∧
  ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => ‖ρ s.toNNReal ω‖ ^ 2) (Set.Icc (0 : ℝ) T)

/-- The value (12), p. 16, of the power-utility problem with `U_γ(x) = x^γ / γ`:
`V̄(x) = sup_{ρ ∈ Ã} E[U_γ(X^{(ρ)}_T)]`, the expectation of the nonnegative utility taken as a
lower integral in `[0, ∞]`. -/
noncomputable def value {d m : ℕ} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) → ℝ≥0 → Ω → ℝ)
    (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (Ct : Set (Fin d → ℝ)) (γ x : ℝ) : ℝ≥0∞ :=
  ⨆ ρ ∈ {ρ | Admissible P 𝓕 T σ Ct ρ},
    ∫⁻ ω, ENNReal.ofReal ((wealth I b σ x ρ T ω) ^ γ / γ) ∂P

end HuImkellerMuller.Power


