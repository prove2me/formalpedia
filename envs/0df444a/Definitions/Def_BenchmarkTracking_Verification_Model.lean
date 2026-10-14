-- Prove2me | Definitions.Def_BenchmarkTracking_Verification_Model
-- name    : BenchmarkTracking_Verification_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:24.840279+00:00
-- url     : https://prove2.me/theorems/5c90baf8-be19-4805-83b4-a5fc84dff428
-- title:
--   §1–§3 — model parameters, standing assumptions and the coefficients $\alpha,\kappa_1,\kappa_2,\varrho_1,\varrho_2,C_1,C_2,\ell$
-- statement:
--   This file fixes the parameters of the relaxed benchmark-tracking model of Bo, Huang and Yu.
--
--   A market has $d$ risky assets with return vector $\mu\in\mathbb R^d$ and volatility matrix $\sigma\in\mathbb R^{d\times d}$; the riskless rate is $0$ (p. 2). The benchmark $M_t=m_t+Z_t$ is built from a geometric Brownian motion $Z$ with drift $\mu_Z\in\mathbb R$ and volatility $\sigma_Z\ge0$, driven by $W^\eta=\sum_j\eta_jW^j$, and the running maximum $m$ of a drifted Brownian motion $B_t=b+\mu_Bt+\sigma_BW^\gamma_t$ with $\mu_B\in\mathbb R$, $\sigma_B\ge0$ and $W^\gamma=\sum_j\gamma_jW^j$. The fund manager pays $\beta>0$ per unit of injected capital and has power utility $U(x)=x^p/p$.
--
--   1. **Standing assumptions** (pp. 2 and 4): $d\ge1$, $\sigma$ is invertible, $\mu\neq0$, $\sigma_Z,\sigma_B\ge0$, $|\gamma|=|\eta|=1$ (Euclidean norm), $\beta>0$, and $p\in(-\infty,0)\cup(0,1)$.
--   2. **Coefficients** (2.9) and (3.4):
--   $$
--   \alpha=\big(\mu^\top(\sigma\sigma^\top)^{-1}\mu\big)^{1/2},\quad \kappa_1=\sigma_B\,\mu^\top(\sigma\sigma^\top)^{-1}\sigma\gamma,\quad \kappa_2=\sigma_Z\,\mu^\top(\sigma\sigma^\top)^{-1}\sigma\eta,\quad \varrho_1=\frac{\mu^\top(\sigma\sigma^\top)^{-1}\sigma\gamma}{\alpha},\quad \varrho_2=\frac{\mu^\top(\sigma\sigma^\top)^{-1}\sigma\eta}{\alpha}.
--   $$
--   3. **Constants of Lemma 3.2**, for a discount rate $\rho$ ((3.10)–(3.12)):
--   $$
--   C_1=\frac{2(1-p)^3}{p(2\rho(1-p)-\alpha^2p)},\qquad C_2=\frac{2(1-p)^2}{2\rho(1-p)-\alpha^2p}\,\beta^{-\frac1{1-p}},\qquad \ell=\frac{-(\rho-\kappa_2-\frac12\alpha^2)+\sqrt{(\rho-\kappa_2-\frac12\alpha^2)^2+2\alpha^2(\rho-\mu_Z)}}{\alpha^2}.
--   $$
--
--   Every statement of the mission is phrased in terms of these parameters; the coefficients are computed from them and are never free.
--
--   **Formalization Note** Vectors are `Fin d → ℝ` and $|\gamma|=1$ is written $\gamma\cdot\gamma=1$. The paper requires $\gamma,\eta\in[-1,1]^d$ and says that $W^\gamma$ "itself is a Brownian motion"; that forces $|\gamma|=1$, and the same normalisation is assumed for $\eta$. Under these assumptions $|\varrho_1|,|\varrho_2|\le1$, so the square roots $\sqrt{1-\varrho_i^2}$ used later are genuine. The discount rate $\rho$ is not a field: the results hold for $\rho$ in a range, so it is an explicit argument.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, p. 2 (1.1)–(1.3), p. 4, p. 7 (2.9), p. 8 (3.4), pp. 9–10 (3.10)–(3.12)

import Mathlib

open Matrix
open scoped Matrix

namespace BenchmarkTracking.Verification

/-!
Bo, Huang & Yu, arXiv:2302.08302v4: the market (1.1)–(1.2) and benchmark (1.3), p. 2, the power
utility and cost parameter, p. 4, and the coefficients (2.9), p. 7, (3.4), p. 8, (3.10)–(3.12),
pp. 9–10. The riskless rate is `r = 0`. The discount rate `ρ` is not a field: the paper's results
hold for `ρ` in a range, so `ρ` is an explicit argument of everything that depends on it.
-/

/-- The model parameters of p. 2 and p. 4: `d` risky assets with return vector `µ` and volatility
matrix `σ`; the benchmark data `µ_Z, σ_Z` (the GBM `Z`), `µ_B, σ_B` (the drifted Brownian motion
`B`), and the correlation vectors `γ, η`; the cost `β` per unit of injected capital; the risk
aversion `p` of the power utility `U(x) = x^p/p`. -/
structure Params (d : ℕ) where
  /-- return vector `µ = (µ_1, …, µ_d)ᵀ` -/
  mu : Fin d → ℝ
  /-- volatility matrix `σ = (σ_ij)` -/
  sigma : Matrix (Fin d) (Fin d) ℝ
  /-- drift `µ_Z` of the GBM `Z` -/
  muZ : ℝ
  /-- volatility `σ_Z` of the GBM `Z` -/
  sigmaZ : ℝ
  /-- drift `µ_B` of `B` -/
  muB : ℝ
  /-- volatility `σ_B` of `B` -/
  sigmaB : ℝ
  /-- weights `γ` of `W^γ = Σ_j γ_j W^j` -/
  gamma : Fin d → ℝ
  /-- weights `η` of `W^η = Σ_j η_j W^j` -/
  eta : Fin d → ℝ
  /-- cost `β` per unit of injected capital -/
  beta : ℝ
  /-- risk aversion `p` of `U(x) = x^p / p` -/
  p : ℝ

namespace Params

variable {d : ℕ} (P : Params d)

/-- The standing assumptions of pp. 2 and 4: `d ≥ 1`; `σ` invertible; `µ ≠ 0`; `σ_Z, σ_B ≥ 0`;
`W^γ` and `W^η` are standard Brownian motions, i.e. `|γ| = |η| = 1` (Euclidean; the paper says
`W^γ` "itself is a Brownian motion", p. 2); `β > 0`; `p ∈ (−∞, 0) ∪ (0, 1)`. -/
def Standing : Prop :=
  1 ≤ d ∧ P.sigma.det ≠ 0 ∧ P.mu ≠ 0 ∧ 0 ≤ P.sigmaZ ∧ 0 ≤ P.sigmaB ∧
  P.gamma ⬝ᵥ P.gamma = 1 ∧ P.eta ⬝ᵥ P.eta = 1 ∧ 0 < P.beta ∧ P.p < 1 ∧ P.p ≠ 0

/-- `(σσᵀ)⁻¹`. -/
noncomputable def covInv : Matrix (Fin d) (Fin d) ℝ := (P.sigma * P.sigmaᵀ)⁻¹

/-- `α := (µᵀ(σσᵀ)⁻¹µ)^{1/2}`, (2.9). -/
noncomputable def alpha : ℝ := Real.sqrt (P.mu ⬝ᵥ (P.covInv *ᵥ P.mu))

/-- `κ₁ := σ_B µᵀ(σσᵀ)⁻¹σγ`, (2.9). -/
noncomputable def kappa1 : ℝ := P.sigmaB * (P.mu ⬝ᵥ (P.covInv *ᵥ (P.sigma *ᵥ P.gamma)))

/-- `κ₂ := σ_Z µᵀ(σσᵀ)⁻¹ση`, (2.9). -/
noncomputable def kappa2 : ℝ := P.sigmaZ * (P.mu ⬝ᵥ (P.covInv *ᵥ (P.sigma *ᵥ P.eta)))

/-- `ϱ₁ := µᵀ(σσᵀ)⁻¹σγ / α`, (3.4). -/
noncomputable def rho1 : ℝ := (P.mu ⬝ᵥ (P.covInv *ᵥ (P.sigma *ᵥ P.gamma))) / P.alpha

/-- `ϱ₂ := µᵀ(σσᵀ)⁻¹ση / α`, (3.4). -/
noncomputable def rho2 : ℝ := (P.mu ⬝ᵥ (P.covInv *ᵥ (P.sigma *ᵥ P.eta))) / P.alpha

/-- `C₁ := 2(1−p)³ / (p(2ρ(1−p) − α²p))`, (3.10). -/
noncomputable def C1 (ρ : ℝ) : ℝ :=
  2 * (1 - P.p) ^ 3 / (P.p * (2 * ρ * (1 - P.p) - P.alpha ^ 2 * P.p))

/-- `C₂ := (2(1−p)² / (2ρ(1−p) − α²p)) β^{−1/(1−p)}`, (3.10). -/
noncomputable def C2 (ρ : ℝ) : ℝ :=
  2 * (1 - P.p) ^ 2 / (2 * ρ * (1 - P.p) - P.alpha ^ 2 * P.p) * P.beta ^ (-1 / (1 - P.p))

/-- `ℓ`, the positive root (3.12) of `½α²ℓ² + (ρ − κ₂ − ½α²)ℓ + µ_Z − ρ = 0` (3.11). -/
noncomputable def ell (ρ : ℝ) : ℝ :=
  (-(ρ - P.kappa2 - P.alpha ^ 2 / 2) +
      Real.sqrt ((ρ - P.kappa2 - P.alpha ^ 2 / 2) ^ 2 + 2 * P.alpha ^ 2 * (ρ - P.muZ))) /
    P.alpha ^ 2

end Params

end BenchmarkTracking.Verification


