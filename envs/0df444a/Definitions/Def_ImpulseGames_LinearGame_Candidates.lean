-- Prove2me | Definitions.Def_ImpulseGames_LinearGame_Candidates
-- name    : ImpulseGames_LinearGame_Candidates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:08:54.361983+00:00
-- url     : https://prove2.me/theorems/b73f09a5-cb00-404e-b602-7e27b4b37852
-- title:
--   The explicit candidates: $\theta,\eta$, $F$ (4.17), $\Gamma$ (4.21), the 8-uple (4.20), and for $i=1,2$: $\varphi_i$ (4.5), $\tilde V_i$ (4.6), $\delta_i$ (4.23), $\mathcal M_i$ (3.2)
-- statement:
--   Write
--   $$\theta=\sqrt{\frac{2\rho}{\sigma^2}},\qquad \eta=\frac{1-\lambda\rho}{\rho},\qquad F(y)=2y+\theta c-\eta\log\Big(\frac{\eta+y}{\eta-y}\Big)\quad(0<y<\eta),$$
--   and, for $\xi\in(0,\eta)$ (the zero of $F$),
--   $$\Gamma=\frac{\theta(c-\tilde c)}{4\xi}+\frac{\theta c(\lambda-\tilde\lambda)}{4\eta\xi}+\frac{\lambda-\tilde\lambda}{2\eta}.$$
--   For every $\tilde s\in\mathbb R$ and $i,j\in\{1,2\}$, the 8-uple of Remark 4.4 is
--   $$\bar x_i=\tilde s+\frac{(-1)^i}{\theta}\log\Big[\sqrt{\tfrac{\eta+\xi}{\eta-\xi}}\big(\sqrt{\Gamma+1}+\sqrt\Gamma\big)\Big],\qquad x_i^*=\tilde s+\frac{(-1)^i}{\theta}\log\Big[\sqrt{\tfrac{\eta-\xi}{\eta+\xi}}\big(\sqrt{\Gamma+1}+\sqrt\Gamma\big)\Big],$$
--   $$A_{ij}=e^{(-1)^j\theta\tilde s}\,\frac{\sqrt{\eta^2-\xi^2}}{2\theta}\Big((-1)^{i+j+1}\sqrt{\Gamma+1}-\sqrt\Gamma\Big).$$
--   The functions $\varphi_1(y)=A_{11}e^{\theta y}+A_{12}e^{-\theta y}+(y-s_1)/\rho$ and $\varphi_2(y)=A_{21}e^{\theta y}+A_{22}e^{-\theta y}+(s_2-y)/\rho$ (4.5) define the candidates of Definition 4.1:
--   $$\tilde V_1(x)=\begin{cases}\varphi_1(x_1^*)-c-\lambda(x_1^*-x),&x\in]-\infty,\bar x_1],\\ \varphi_1(x),&x\in]\bar x_1,\bar x_2[,\\ \varphi_1(x_2^*)+\tilde c+\tilde\lambda(x-x_2^*),&x\in[\bar x_2,+\infty[,\end{cases}\qquad \tilde V_2(x)=\begin{cases}\varphi_2(x_1^*)+\tilde c+\tilde\lambda(x_1^*-x),&x\in]-\infty,\bar x_1],\\ \varphi_2(x),&x\in]\bar x_1,\bar x_2[,\\ \varphi_2(x_2^*)-c-\lambda(x-x_2^*),&x\in[\bar x_2,+\infty[.\end{cases}$$
--   The impulse functions of (4.23) are $\delta_1(y)=\max(x_1^*-y,0)$ and $\delta_2(y)=\min(x_2^*-y,0)$, and the intervention operators (3.2) of the model are
--   $$\mathcal M_1V(y)=\sup_{\delta\ge0}\{V(y+\delta)-c-\lambda|\delta|\},\qquad \mathcal M_2V(y)=\sup_{\delta\le0}\{V(y+\delta)-c-\lambda|\delta|\}.$$
--
--   These are the explicit objects of Sections 4.2-4.3: Proposition 4.7 identifies $\tilde V_1,\tilde V_2$ with the payoffs of a Nash equilibrium.
--
--   **Formalization Note.** The zero $\xi$ is a parameter of every definition; the theorems assume $\xi\in(0,\eta)$ and $F(\xi)=0$, and existence and uniqueness of such $\xi$ is the separate statement (4.17). On that domain every `Real.log`, `Real.sqrt` and division above has a positive argument. The suprema $\mathcal M_i$ are real `sSup`s; the theorems that use them also assert that the supremum is attained. Indices $i,j$ are natural numbers and only $1,2$ are used.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, (3.2) (p. 7), (4.5) and Definition 4.1 (pp. 14-15), (4.17) (p. 16), (4.20)-(4.21) and (4.23) (p. 17)

import Mathlib
import Definitions.Def_ImpulseGames_LinearGame_Model

namespace ImpulseGames.LinearGame

/-- `θ = √(2ρ/σ²)` (p. 14, and (4.21)). -/
noncomputable def theta (M : Model) : ℝ := Real.sqrt (2 * M.ρ / M.σ ^ 2)

/-- `η = (1 − λρ)/ρ` (4.21). -/
noncomputable def eta (M : Model) : ℝ := (1 - M.lam * M.ρ) / M.ρ

/-- The function `F(y) = 2y + θc − η log((η + y)/(η − y))` of (4.17), meaningful for `y ∈ (0, η)`. -/
noncomputable def F (M : Model) (y : ℝ) : ℝ :=
  2 * y + theta M * M.c - eta M * Real.log ((eta M + y) / (eta M - y))

/-- The coefficient `Γ = θ(c − c̃)/(4ξ) + θc(λ − λ̃)/(4ηξ) + (λ − λ̃)/(2η)` of (4.21). -/
noncomputable def Gam (M : Model) (ξ : ℝ) : ℝ :=
  theta M * (M.c - M.ct) / (4 * ξ) + theta M * M.c * (M.lam - M.lamt) / (4 * eta M * ξ)
    + (M.lam - M.lamt) / (2 * eta M)

/-- The thresholds `x̄ᵢ` of (4.20), `i ∈ {1, 2}`, for the parameter `s̃ = s`:
`x̄ᵢ = s̃ + ((−1)^i/θ) log[√((η+ξ)/(η−ξ)) (√(Γ+1) + √Γ)]`. -/
noncomputable def xbar (M : Model) (ξ s : ℝ) (i : ℕ) : ℝ :=
  s + (-1 : ℝ) ^ i / theta M *
    Real.log (Real.sqrt ((eta M + ξ) / (eta M - ξ)) * (Real.sqrt (Gam M ξ + 1) + Real.sqrt (Gam M ξ)))

/-- The targets `xᵢ*` of (4.20), `i ∈ {1, 2}`:
`xᵢ* = s̃ + ((−1)^i/θ) log[√((η−ξ)/(η+ξ)) (√(Γ+1) + √Γ)]`. -/
noncomputable def xstar (M : Model) (ξ s : ℝ) (i : ℕ) : ℝ :=
  s + (-1 : ℝ) ^ i / theta M *
    Real.log (Real.sqrt ((eta M - ξ) / (eta M + ξ)) * (Real.sqrt (Gam M ξ + 1) + Real.sqrt (Gam M ξ)))

/-- The coefficients `Aᵢⱼ` of (4.20), `i, j ∈ {1, 2}`:
`Aᵢⱼ = e^{(−1)^j θ s̃} (√(η² − ξ²)/(2θ)) ((−1)^{i+j+1} √(Γ+1) − √Γ)`. -/
noncomputable def A (M : Model) (ξ s : ℝ) (i j : ℕ) : ℝ :=
  Real.exp ((-1 : ℝ) ^ j * theta M * s) * Real.sqrt (eta M ^ 2 - ξ ^ 2) / (2 * theta M) *
    ((-1 : ℝ) ^ (i + j + 1) * Real.sqrt (Gam M ξ + 1) - Real.sqrt (Gam M ξ))

/-- `φ₁^{A₁₁,A₁₂}(y) = A₁₁ e^{θy} + A₁₂ e^{−θy} + (y − s₁)/ρ` (4.5). -/
noncomputable def phi1 (M : Model) (A₁₁ A₁₂ : ℝ) (y : ℝ) : ℝ :=
  A₁₁ * Real.exp (theta M * y) + A₁₂ * Real.exp (-(theta M * y)) + (y - M.s₁) / M.ρ

/-- `φ₂^{A₂₁,A₂₂}(y) = A₂₁ e^{θy} + A₂₂ e^{−θy} + (s₂ − y)/ρ` (4.5). -/
noncomputable def phi2 (M : Model) (A₂₁ A₂₂ : ℝ) (y : ℝ) : ℝ :=
  A₂₁ * Real.exp (theta M * y) + A₂₂ * Real.exp (-(theta M * y)) + (M.s₂ - y) / M.ρ

/-- `φ₁ = φ₁^{A₁₁,A₁₂}` with the coefficients `A₁₁, A₁₂` of (4.20). -/
noncomputable def phiOne (M : Model) (ξ s : ℝ) : ℝ → ℝ := phi1 M (A M ξ s 1 1) (A M ξ s 1 2)

/-- `φ₂ = φ₂^{A₂₁,A₂₂}` with the coefficients `A₂₁, A₂₂` of (4.20). -/
noncomputable def phiTwo (M : Model) (ξ s : ℝ) : ℝ → ℝ := phi2 M (A M ξ s 2 1) (A M ξ s 2 2)

/-- The candidate payoff `Ṽ₁` of Definition 4.1, (4.6), built on the 8-uple (4.20). -/
noncomputable def Vt1 (M : Model) (ξ s : ℝ) (y : ℝ) : ℝ :=
  if y ≤ xbar M ξ s 1 then
    phiOne M ξ s (xstar M ξ s 1) - M.c - M.lam * (xstar M ξ s 1 - y)
  else if y < xbar M ξ s 2 then phiOne M ξ s y
  else phiOne M ξ s (xstar M ξ s 2) + M.ct + M.lamt * (y - xstar M ξ s 2)

/-- The candidate payoff `Ṽ₂` of Definition 4.1, (4.6), built on the 8-uple (4.20). -/
noncomputable def Vt2 (M : Model) (ξ s : ℝ) (y : ℝ) : ℝ :=
  if y ≤ xbar M ξ s 1 then
    phiTwo M ξ s (xstar M ξ s 1) + M.ct + M.lamt * (xstar M ξ s 1 - y)
  else if y < xbar M ξ s 2 then phiTwo M ξ s y
  else phiTwo M ξ s (xstar M ξ s 2) - M.c - M.lam * (y - xstar M ξ s 2)

/-- `δ₁(y) = max(x₁* − y, 0)`, i.e. `x₁* − y` on `]−∞, x₁*]` and `0` on `]x₁*, +∞[` (4.23). -/
noncomputable def delta1 (M : Model) (ξ s : ℝ) (y : ℝ) : ℝ := max (xstar M ξ s 1 - y) 0

/-- `δ₂(y) = min(x₂* − y, 0)`, i.e. `0` on `]−∞, x₂*[` and `x₂* − y` on `[x₂*, +∞[` (4.23). -/
noncomputable def delta2 (M : Model) (ξ s : ℝ) (y : ℝ) : ℝ := min (xstar M ξ s 2 - y) 0

/-- The intervention operator of player 1 (3.2), `𝓜₁V(y) = sup_{δ ≥ 0} {V(y + δ) − c − λ|δ|}`
(supremum over `Z₁ = [0, ∞[`; p. 7: `𝓜ᵢVᵢ = max_δ {Vᵢ(Γⁱ(·, δ)) + φᵢ(·, δ)}`). -/
noncomputable def M1op (M : Model) (V : ℝ → ℝ) (y : ℝ) : ℝ :=
  sSup ((fun δ => V (y + δ) - M.c - M.lam * |δ|) '' Set.Ici 0)

/-- The intervention operator of player 2 (3.2), `𝓜₂V(y) = sup_{δ ≤ 0} {V(y + δ) − c − λ|δ|}`
(supremum over `Z₂ = ]−∞, 0]`). -/
noncomputable def M2op (M : Model) (V : ℝ → ℝ) (y : ℝ) : ℝ :=
  sSup ((fun δ => V (y + δ) - M.c - M.lam * |δ|) '' Set.Iic 0)

end ImpulseGames.LinearGame


