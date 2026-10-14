-- Prove2me | Definitions.Def_MFIrrev_Equilibrium_Analytic
-- name    : MFIrrev_Equilibrium_Analytic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:30.445801+00:00
-- url     : https://prove2.me/theorems/93c4d9c1-0e18-494a-a565-ba3f5c210896
-- title:
--   §2 and §4, pp. 6–7, 14–15, 21–22 — constants, η (2.7), generators (4.6), (4.15), ϕᵢ (4.27), α₁± (4.28), ϕ̄ (4.29), ϕ₁ᵢ (4.30), system (4.31), Π (4.32)
-- statement:
--   The constants and closed-form objects of Aïd, Basei and Ferrari's model.
--
--   **Constants.** A depreciation rate $\delta$, volatilities $\sigma_1,\sigma_2$, switching intensities $p_1,p_2$, a discount rate $\rho$, a running-cost coefficient $c$, a marginal investment cost $\kappa$, price levels $\varphi_1,\varphi_2$, demand coefficients $\zeta_1,\zeta_2$ and an exponent $\alpha$. The generator $P$ and the stationary law $\pi$ are those of (2.1).
--
--   **Inverse demand (2.7).** For aggregate productions $Q=(Q_1,Q_2)$ with $Q_i>0$,
--   $$\eta_i=\varphi_i+\zeta_i Q_i^{-\alpha}.$$
--
--   **Generators (4.6), (4.15).** For $w(\cdot,i)$ twice differentiable,
--   $$\mathcal L w(x,i)=\tfrac12\sigma_i^2x^2w''(x,i)-\delta x w'(x,i)+\sum_{j=1}^2P_{ij}w(x,j),$$
--   $$\bar{\mathcal L} w(x,i)=\tfrac12\sigma_i^2x^2w''(x,i)-(\delta-\sigma_i^2) x w'(x,i)+\sum_{j=1}^2P_{ij}w(x,j).$$
--
--   **Characteristic polynomials (4.27)–(4.30).**
--   $$\phi_i(\theta)=\tfrac12\sigma_i^2\theta^2+\big(\delta+\tfrac12\sigma_i^2\big)\theta-p_i,\qquad \bar\phi(\theta)=\phi_1(\theta)\phi_2(\theta)-p_1p_2,$$
--   $$\alpha_1^\pm=\frac{-(\delta+\frac12\sigma_1^2)\pm\sqrt{(\delta+\frac12\sigma_1^2)^2+2\sigma_1^2p_1}}{\sigma_1^2},\qquad \phi_{1i}=\frac{\phi_1(\theta_i)}{p_2}.$$
--
--   **The linear system (4.31)** in $(A_1,A_2,B_1,B_2)$, for log-barriers $b_1,b_2$ and roots $\theta_1,\theta_2$:
--   $$\begin{pmatrix}1&1&0&0\\ e^{\alpha_1^+(b_2-b_1)}&e^{\alpha_1^-(b_2-b_1)}&-1&-1\\ \alpha_1^+e^{\alpha_1^+(b_2-b_1)}&\alpha_1^-e^{\alpha_1^-(b_2-b_1)}&-\theta_1&-\theta_2\\ 0&0&\phi_{11}&\phi_{12}\end{pmatrix}\begin{pmatrix}A_1\\A_2\\B_1\\B_2\end{pmatrix}=\begin{pmatrix}0\\ \pi_1\\0\\ \pi_2\end{pmatrix}.$$
--
--   **The function $\Pi$ of (4.32).**
--   $$\Pi(z,1)=\begin{cases}0,&z\le b_1,\\ A_1e^{\alpha_1^+(z-b_1)}+A_2e^{\alpha_1^-(z-b_1)},&b_1<z<b_2,\\ B_1e^{\theta_1(z-b_2)}+B_2e^{\theta_2(z-b_2)}+\pi_1,&z\ge b_2,\end{cases}$$
--   $$\Pi(z,2)=\begin{cases}0,&z\le b_2,\\ -B_1\phi_{11}e^{\theta_1(z-b_2)}-B_2\phi_{12}e^{\theta_2(z-b_2)}+\pi_2,&z>b_2.\end{cases}$$
--
--   These are the explicit formulas the paper uses to describe the stationary law of the equilibrium capacity; every theorem that uses them states its hypotheses separately.
--
--   **Formalization Note.** Regimes are `Fin 2`: index `0` is the paper's regime 1, index `1` its regime 2. The constants form a data-only structure; no positivity is built in. $\eta$ uses Lean's real power, which at $Q_i=0$ returns a junk value, so every theorem using it assumes $Q_i>0$. The generators are written with `deriv`, and are only evaluated at points where the theorems assume (or assert) the needed differentiability.
-- source:
--   Aïd, Basei & Ferrari, A Stationary Mean-Field Equilibrium Model of Irreversible Investment in a Two-Regime Economy, arXiv:2305.00541v1, pp. 5–7 (constants, (2.1), (2.7)), p. 14 (4.6), p. 15 (4.15), p. 21 (4.27)–(4.30), p. 22 (4.31)–(4.32)

import Mathlib
import Definitions.Def_MFIrrev_Equilibrium_TwoStateChain

namespace MFIrrev.Equilibrium

/-- Constants of §2 of Aïd–Basei–Ferrari (data only; every hypothesis on them is a binder of the
theorems). Regime index `0` is the paper's regime 1, index `1` is regime 2. -/
structure Params where
  /-- depreciation rate δ, (2.2) -/
  δ : ℝ
  /-- volatilities σ₁, σ₂, (2.2) -/
  σ : Fin 2 → ℝ
  /-- switching intensities p₁, p₂ of the regime chain, (2.1) -/
  p : Fin 2 → ℝ
  /-- discount rate ρ, (2.6) -/
  ρ : ℝ
  /-- running-cost coefficient c, (2.6) -/
  c : ℝ
  /-- marginal investment cost κ, (2.6) -/
  κ : ℝ
  /-- price levels φ₁, φ₂ (the paper's ϕᵢ), (2.7) -/
  φ : Fin 2 → ℝ
  /-- demand coefficients ζ₁, ζ₂, (2.7) -/
  ζ : Fin 2 → ℝ
  /-- demand elasticity exponent α, (2.7) -/
  α : ℝ

/-- Generator matrix `P` of (2.1): `[[-p₁, p₁], [p₂, -p₂]]`. -/
def genMat (m : Params) : Fin 2 → Fin 2 → ℝ :=
  ![![-m.p 0, m.p 0], ![m.p 1, -m.p 1]]

/-- Stationary distribution `π = (p₂/(p₁+p₂), p₁/(p₁+p₂))` of (2.1). -/
noncomputable def piStat (m : Params) : Fin 2 → ℝ := twoStatePi m.p

/-- Inverse demand (2.7): `η_j = φ_j + ζ_j Q_j^{−α}`; used only with `0 < Q j`. -/
noncomputable def eta (m : Params) (Q : Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  m.φ j + m.ζ j * Q j ^ (-m.α)

/-- The generator `𝓛` of (4.6), applied to `w : ℝ → Fin 2 → ℝ` at `(y, j)`:
`½σ_j² y² w''(y, j) − δ y w'(y, j) + Σ_k P_{jk} w(y, k)`. -/
noncomputable def genL (m : Params) (w : ℝ → Fin 2 → ℝ) (y : ℝ) (j : Fin 2) : ℝ :=
  m.σ j ^ 2 / 2 * y ^ 2 * deriv (deriv fun z => w z j) y - m.δ * y * deriv (fun z => w z j) y
    + ∑ k, genMat m j k * w y k

/-- The generator `𝓛̄` of (4.15), applied to `w : ℝ → Fin 2 → ℝ` at `(y, j)`:
`½σ_j² y² w''(y, j) − (δ − σ_j²) y w'(y, j) + Σ_k P_{jk} w(y, k)`. -/
noncomputable def genLbar (m : Params) (w : ℝ → Fin 2 → ℝ) (y : ℝ) (j : Fin 2) : ℝ :=
  m.σ j ^ 2 / 2 * y ^ 2 * deriv (deriv fun z => w z j) y
    - (m.δ - m.σ j ^ 2) * y * deriv (fun z => w z j) y + ∑ k, genMat m j k * w y k

/-- `ϕ_j(θ) = ½σ_j²θ² + (δ + ½σ_j²)θ − p_j` of (4.27) (Theorem 2.4's `ϕ_i`). -/
noncomputable def phiPoly (m : Params) (j : Fin 2) (θ : ℝ) : ℝ :=
  m.σ j ^ 2 / 2 * θ ^ 2 + (m.δ + m.σ j ^ 2 / 2) * θ - m.p j

/-- `ϕ̄(θ) = ϕ₁(θ)ϕ₂(θ) − p₁p₂` of (4.29). -/
noncomputable def phiBar (m : Params) (θ : ℝ) : ℝ :=
  phiPoly m 0 θ * phiPoly m 1 θ - m.p 0 * m.p 1

/-- `α₁⁺` of (4.28): the positive root of `ϕ₁`. -/
noncomputable def alphaPlus (m : Params) : ℝ :=
  (-(m.δ + m.σ 0 ^ 2 / 2) + Real.sqrt ((m.δ + m.σ 0 ^ 2 / 2) ^ 2 + 2 * m.σ 0 ^ 2 * m.p 0))
    / m.σ 0 ^ 2

/-- `α₁⁻` of (4.28): the negative root of `ϕ₁`. -/
noncomputable def alphaMinus (m : Params) : ℝ :=
  (-(m.δ + m.σ 0 ^ 2 / 2) - Real.sqrt ((m.δ + m.σ 0 ^ 2 / 2) ^ 2 + 2 * m.σ 0 ^ 2 * m.p 0))
    / m.σ 0 ^ 2

/-- `ϕ_{1i} = ϕ₁(θ_i)/p₂` of (4.30), as a function of `θ = θ_i`. -/
noncomputable def phi1i (m : Params) (θ : ℝ) : ℝ := phiPoly m 0 θ / m.p 1

/-- The linear system (4.31) in the unknowns `(A₁, A₂, B₁, B₂)`, for log-barriers `b₁, b₂` and
roots `θ₁, θ₂`, row by row:
`A₁ + A₂ = 0`,
`e^{α₁⁺(b₂−b₁)}A₁ + e^{α₁⁻(b₂−b₁)}A₂ − B₁ − B₂ = π₁`,
`α₁⁺e^{α₁⁺(b₂−b₁)}A₁ + α₁⁻e^{α₁⁻(b₂−b₁)}A₂ − θ₁B₁ − θ₂B₂ = 0`,
`ϕ₁₁B₁ + ϕ₁₂B₂ = π₂`. -/
def Sys431 (m : Params) (b1 b2 θ1 θ2 A1 A2 B1 B2 : ℝ) : Prop :=
  A1 + A2 = 0 ∧
  Real.exp (alphaPlus m * (b2 - b1)) * A1 + Real.exp (alphaMinus m * (b2 - b1)) * A2 - B1 - B2
    = piStat m 0 ∧
  alphaPlus m * Real.exp (alphaPlus m * (b2 - b1)) * A1
      + alphaMinus m * Real.exp (alphaMinus m * (b2 - b1)) * A2 - θ1 * B1 - θ2 * B2 = 0 ∧
  phi1i m θ1 * B1 + phi1i m θ2 * B2 = piStat m 1

/-- The function `Π(z, j)` of (4.32) (log-capacity `z`, regime `j`; index `0` is regime 1):
`Π(z,1) = 0` for `z ≤ b₁`, `A₁e^{α₁⁺(z−b₁)} + A₂e^{α₁⁻(z−b₁)}` for `b₁ < z < b₂`,
`B₁e^{θ₁(z−b₂)} + B₂e^{θ₂(z−b₂)} + π₁` for `z ≥ b₂`;
`Π(z,2) = 0` for `z ≤ b₂`, `−B₁ϕ₁₁e^{θ₁(z−b₂)} − B₂ϕ₁₂e^{θ₂(z−b₂)} + π₂` for `z > b₂`. -/
noncomputable def PiCDF (m : Params) (b1 b2 θ1 θ2 A1 A2 B1 B2 : ℝ) (z : ℝ) : Fin 2 → ℝ :=
  ![if z ≤ b1 then 0
    else if z < b2 then
      A1 * Real.exp (alphaPlus m * (z - b1)) + A2 * Real.exp (alphaMinus m * (z - b1))
    else B1 * Real.exp (θ1 * (z - b2)) + B2 * Real.exp (θ2 * (z - b2)) + piStat m 0,
    if z ≤ b2 then 0
    else -B1 * phi1i m θ1 * Real.exp (θ1 * (z - b2)) - B2 * phi1i m θ2 * Real.exp (θ2 * (z - b2))
      + piStat m 1]

end MFIrrev.Equilibrium


