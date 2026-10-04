-- Prove2me | Definitions.Def_ImpulseGames_CostMonotonicity_Thresholds
-- name    : ImpulseGames_CostMonotonicity_Thresholds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:22:50.29556+00:00
-- url     : https://prove2.me/theorems/39b929fd-b556-4af5-8d1a-19a2d480f33f
-- title:
--   Equilibrium thresholds of the linear impulse game as functions of the fixed cost $c$: $F$ (4.17), $\xi(c)$, $\theta,\eta,\Gamma$ (4.21), $\bar x_i, x_i^*, A_{2j}$ (4.20), $V_i^c$ (4.27)
-- statement:
--   This file fixes the explicit formulas of Section 4 of Aïd, Basei, Callegaro, Campi and Vargiolu for the linear two-player impulse game, viewed as functions of the **fixed intervention cost** $c$.
--
--   **Parameters.** The data are a discount rate $\rho$, a volatility $\sigma$, a proportional intervention cost $\lambda$ and proportional gain $\tilde\lambda$, a fixed gain $\tilde c$, the targets $s_1, s_2$ of the running payoffs $f_1(x) = x - s_1$, $f_2(x) = s_2 - x$ (4.1), and a real number $\tilde s$ indexing the family of equilibria (Remark 4.4). The **standing assumptions** of Section 4.1 are
--   $$\rho > 0,\quad \sigma > 0,\quad s_1 < s_2,\quad \tilde c \ge 0,\quad \lambda \ge \tilde\lambda \ge 0,\quad 1 - \lambda\rho > 0 .$$
--   The remaining assumptions of the paper, $c \ge \tilde c$ and $(c,\lambda) \ne (\tilde c, \tilde\lambda)$, concern the variable $c$ and are carried by each statement through its domain: the statements about the thresholds use $c > \tilde c$ (or $c > 0$ when $\tilde c = 0$, or $c \to +\infty$), and the statements about $\xi$ alone, which does not involve $\tilde c$ or $\tilde\lambda$, use $c > 0$ as the paper does in (4.28).
--
--   **Coefficients (4.21).** $\theta = \sqrt{2\rho/\sigma^2}$ and $\eta = (1-\lambda\rho)/\rho$; both are positive under the standing assumptions.
--
--   **The function $F$ (4.17).** For $y \in (0,\eta)$,
--   $$F_c(y) = 2y + \theta c - \eta \log\left(\frac{\eta + y}{\eta - y}\right).$$
--
--   **The zero $\xi(c)$.** $\xi(c)$ is defined as $\sup\{y \in (0,\eta) : F_c(y) \ge 0\}$. For $c > 0$ this is the unique zero of $F_c$ in $(0,\eta)$, which is how the paper defines $\xi$; for $c \le 0$ the set is empty and the value is a placeholder.
--
--   **The coefficient $\Gamma$ (4.21).**
--   $$\Gamma(c) = \frac{\theta(c-\tilde c)}{4\xi} + \frac{\theta c(\lambda-\tilde\lambda)}{4\eta\xi} + \frac{\lambda-\tilde\lambda}{2\eta}, \qquad \xi = \xi(c).$$
--
--   **Thresholds and targets (4.20).** For $i \in \{1,2\}$,
--   $$\bar x_i(c) = \tilde s + \frac{(-1)^i}{\theta}\log\left[\sqrt{\frac{\eta+\xi}{\eta-\xi}}\left(\sqrt{\Gamma+1}+\sqrt{\Gamma}\right)\right], \qquad x_i^*(c) = \tilde s + \frac{(-1)^i}{\theta}\log\left[\sqrt{\frac{\eta-\xi}{\eta+\xi}}\left(\sqrt{\Gamma+1}+\sqrt{\Gamma}\right)\right].$$
--   In the equilibrium of Proposition 4.7, player 1 intervenes when the state is below $\bar x_1$ and moves it to $x_1^*$; player 2 intervenes above $\bar x_2$ and moves it to $x_2^*$.
--
--   **Payoffs (4.5), (4.20), (4.27).** With $A_{21} = e^{-\theta\tilde s}\frac{\sqrt{\eta^2-\xi^2}}{2\theta}\left(\sqrt{\Gamma+1}-\sqrt\Gamma\right)$, $A_{22} = e^{\theta\tilde s}\frac{\sqrt{\eta^2-\xi^2}}{2\theta}\left(-\sqrt{\Gamma+1}-\sqrt\Gamma\right)$ and $\varphi_2^{A,B}(x) = A e^{\theta x} + B e^{-\theta x} + (s_2 - x)/\rho$,
--   $$V_2^c(x) = \begin{cases} \varphi_2^{A_{21},A_{22}}(x_1^*) + \tilde c + \tilde\lambda(x_1^* - x), & x \le \bar x_1,\\ \varphi_2^{A_{21},A_{22}}(x), & \bar x_1 < x < \bar x_2,\\ \varphi_2^{A_{21},A_{22}}(x_2^*) - c - \lambda(x - x_2^*), & x \ge \bar x_2,\end{cases} \qquad V_1^c(x) = V_2^c(2\tilde s - x) + \frac{2\tilde s - (s_1+s_2)}{\rho}.$$
--
--   These are the objects whose dependence on $c$ is studied in Section 4.4 of the paper: the continuation region $]\bar x_1(c), \bar x_2(c)[$, the target states $x_i^*(c)$ and the equilibrium payoffs $V_i^c$.
--
--   **Formalization Note.** The data are bundled in a structure `Params` and the standing assumptions in a predicate `Params.Standing`. The cost $c$ is an explicit real argument of every function. Every function is total: for $c \le 0$ the value of $\xi$ is the junk value $0$, and $\Gamma$, $\bar x_i$, $x_i^*$ are junk wherever $\xi(c) \notin (0,\eta)$ or $\Gamma(c) < 0$; every statement of the mission restricts $c$ to $c > 0$ or $c > \tilde c$, where they are the paper's values. $\theta$ and $\eta$ are computed from $\rho, \sigma, \lambda$ as in (4.21), not taken as free parameters.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Section 4.1 (pp. 12-13), (4.5) (p. 14), (4.17) (p. 16), (4.20)-(4.21) (p. 17), (4.27) (p. 20)

import Mathlib

namespace ImpulseGames.CostMonotonicity

/-- The fixed data of the linear impulse game of Section 4.1 (Aïd et al. 2020, pp. 12–13), all
except the fixed intervention cost `c`, which is the variable of Section 4.4:
the discount rate `rho` (ρ), the volatility `sigma` (σ), the proportional cost `lam` (λ) and gain
`lamTilde` (λ̃), the fixed gain `cTilde` (c̃), the targets `s1`, `s2` of the running payoffs (4.1),
and the parameter `sTilde` (s̃ ∈ ℝ) indexing the family of equilibria (Remark 4.4). -/
structure Params where
  rho : ℝ
  sigma : ℝ
  lam : ℝ
  lamTilde : ℝ
  cTilde : ℝ
  sTilde : ℝ
  s1 : ℝ
  s2 : ℝ

/-- The standing assumptions of Section 4.1 that do not involve `c`: ρ > 0 and σ > 0 (Section 2
and (4.1)), s₁ < s₂ (4.1), c̃ ≥ 0 and λ ≥ λ̃ ≥ 0 (p. 13), and 1 − λρ > 0 (4.2). The assumptions
`c ≥ c̃` and `(c, λ) ≠ (c̃, λ̃)` are about the variable `c` and are carried by each statement. -/
structure Params.Standing (P : Params) : Prop where
  rho_pos : 0 < P.rho
  sigma_pos : 0 < P.sigma
  s1_lt_s2 : P.s1 < P.s2
  cTilde_nonneg : 0 ≤ P.cTilde
  lamTilde_nonneg : 0 ≤ P.lamTilde
  lamTilde_le_lam : P.lamTilde ≤ P.lam
  one_sub_lam_mul_rho_pos : 0 < 1 - P.lam * P.rho

/-- θ = √(2ρ/σ²), (4.21). -/
noncomputable def Params.theta (P : Params) : ℝ := Real.sqrt (2 * P.rho / P.sigma ^ 2)

/-- η = (1 − λρ)/ρ, (4.21). -/
noncomputable def Params.eta (P : Params) : ℝ := (1 - P.lam * P.rho) / P.rho

/-- F(y) = 2y + θc − η log((η + y)/(η − y)), the function (4.17), meaningful for y ∈ (0, η). -/
noncomputable def Params.F (P : Params) (c y : ℝ) : ℝ :=
  2 * y + P.theta * c - P.eta * Real.log ((P.eta + y) / (P.eta - y))

/-- ξ(c): the supremum of the points y ∈ (0, η) with F(y) ≥ 0. For c > 0 this is the unique zero of
F in (0, η) (milestone (4.17)); for c ≤ 0 the set is empty and the value `0` is a junk value that
no statement of the mission uses. -/
noncomputable def Params.xi (P : Params) (c : ℝ) : ℝ :=
  sSup {y : ℝ | y ∈ Set.Ioo 0 P.eta ∧ 0 ≤ P.F c y}

/-- Γ(c) = θ(c − c̃)/(4ξ) + θc(λ − λ̃)/(4ηξ) + (λ − λ̃)/(2η), (4.21). -/
noncomputable def Params.Gamma (P : Params) (c : ℝ) : ℝ :=
  P.theta * (c - P.cTilde) / (4 * P.xi c)
    + P.theta * c * (P.lam - P.lamTilde) / (4 * P.eta * P.xi c)
    + (P.lam - P.lamTilde) / (2 * P.eta)

/-- The common factor √(Γ + 1) + √Γ of (4.20). -/
noncomputable def Params.gammaFactor (P : Params) (c : ℝ) : ℝ :=
  Real.sqrt (P.Gamma c + 1) + Real.sqrt (P.Gamma c)

/-- x̄₁(c) = s̃ − (1/θ) log[√((η + ξ)/(η − ξ)) (√(Γ + 1) + √Γ)], (4.20) with i = 1. -/
noncomputable def Params.xbar1 (P : Params) (c : ℝ) : ℝ :=
  P.sTilde - 1 / P.theta *
    Real.log (Real.sqrt ((P.eta + P.xi c) / (P.eta - P.xi c)) * P.gammaFactor c)

/-- x̄₂(c) = s̃ + (1/θ) log[√((η + ξ)/(η − ξ)) (√(Γ + 1) + √Γ)], (4.20) with i = 2. -/
noncomputable def Params.xbar2 (P : Params) (c : ℝ) : ℝ :=
  P.sTilde + 1 / P.theta *
    Real.log (Real.sqrt ((P.eta + P.xi c) / (P.eta - P.xi c)) * P.gammaFactor c)

/-- x₁*(c) = s̃ − (1/θ) log[√((η − ξ)/(η + ξ)) (√(Γ + 1) + √Γ)], (4.20) with i = 1. -/
noncomputable def Params.xstar1 (P : Params) (c : ℝ) : ℝ :=
  P.sTilde - 1 / P.theta *
    Real.log (Real.sqrt ((P.eta - P.xi c) / (P.eta + P.xi c)) * P.gammaFactor c)

/-- x₂*(c) = s̃ + (1/θ) log[√((η − ξ)/(η + ξ)) (√(Γ + 1) + √Γ)], (4.20) with i = 2. -/
noncomputable def Params.xstar2 (P : Params) (c : ℝ) : ℝ :=
  P.sTilde + 1 / P.theta *
    Real.log (Real.sqrt ((P.eta - P.xi c) / (P.eta + P.xi c)) * P.gammaFactor c)

/-- A₂₁(c) = e^{−θs̃} (√(η² − ξ²)/(2θ)) (√(Γ + 1) − √Γ), (4.20) with i = 2, j = 1. -/
noncomputable def Params.A21 (P : Params) (c : ℝ) : ℝ :=
  Real.exp (-(P.theta * P.sTilde)) * (Real.sqrt (P.eta ^ 2 - P.xi c ^ 2) / (2 * P.theta)) *
    (Real.sqrt (P.Gamma c + 1) - Real.sqrt (P.Gamma c))

/-- A₂₂(c) = e^{θs̃} (√(η² − ξ²)/(2θ)) (−√(Γ + 1) − √Γ), (4.20) with i = 2, j = 2. -/
noncomputable def Params.A22 (P : Params) (c : ℝ) : ℝ :=
  Real.exp (P.theta * P.sTilde) * (Real.sqrt (P.eta ^ 2 - P.xi c ^ 2) / (2 * P.theta)) *
    (-Real.sqrt (P.Gamma c + 1) - Real.sqrt (P.Gamma c))

/-- φ₂^{A,B}(x) = A e^{θx} + B e^{−θx} + (s₂ − x)/ρ, (4.5). -/
noncomputable def Params.phi2 (P : Params) (A B x : ℝ) : ℝ :=
  A * Real.exp (P.theta * x) + B * Real.exp (-(P.theta * x)) + (P.s2 - x) / P.rho

/-- The equilibrium payoff of player 2, (4.27):
V₂ᶜ(x) = φ₂(x₁*) + c̃ + λ̃(x₁* − x) on ]−∞, x̄₁], φ₂(x) on ]x̄₁, x̄₂[,
and φ₂(x₂*) − c − λ(x − x₂*) on [x̄₂, +∞[, with φ₂ = φ₂^{A₂₁(c), A₂₂(c)}. -/
noncomputable def Params.V2 (P : Params) (c x : ℝ) : ℝ :=
  if x ≤ P.xbar1 c then
    P.phi2 (P.A21 c) (P.A22 c) (P.xstar1 c) + P.cTilde + P.lamTilde * (P.xstar1 c - x)
  else if x < P.xbar2 c then
    P.phi2 (P.A21 c) (P.A22 c) x
  else
    P.phi2 (P.A21 c) (P.A22 c) (P.xstar2 c) - c - P.lam * (x - P.xstar2 c)

/-- The equilibrium payoff of player 1, (4.27): V₁ᶜ(x) = V₂ᶜ(2s̃ − x) + (2s̃ − (s₁ + s₂))/ρ. -/
noncomputable def Params.V1 (P : Params) (c x : ℝ) : ℝ :=
  P.V2 c (2 * P.sTilde - x) + (2 * P.sTilde - (P.s1 + P.s2)) / P.rho

end ImpulseGames.CostMonotonicity


