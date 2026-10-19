-- Prove2me | Definitions.Def_CostlyPriceInterp_MarketEq_Model
-- name    : CostlyPriceInterp_MarketEq_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:48.526014+00:00
-- url     : https://prove2.me/theorems/b126addc-3aff-47d0-b6e5-2638bcc9ce28
-- title:
--   §3.1, §4–§4.1, pp. 9–18 — noisy-REE market with costly price interpretation: signals (1)–(4), Bayesian demands (8), market clearing (9), linear equilibrium (11)
-- statement:
--   The financial-market stage of Vives and Yang's model of costly interpretation of asset prices (§3.1 and §4).
--
--   **Asset and signals.** A risky asset pays $\tilde V = \tilde v + \tilde\xi$, where the learnable part $\tilde v \sim N(0,\tau_v^{-1})$ and the unlearnable part $\tilde\xi \sim N(0,\tau_\xi^{-1})$ are independent. A continuum $[0,1]$ of investors have CARA utility with risk aversion $\gamma$. Investor $i$ observes a private signal $\tilde s_i = \tilde v + \tilde\varepsilon_i$ with $\tilde\varepsilon_i \sim N(0,\tau_\varepsilon^{-1})$ (1). If the price conveys the signal $\tilde s_p = \tilde v + \alpha\tilde u$, investor $i$ reads it with interpretation noise, $\tilde s_{p,i} = \tilde s_p + \tilde x_i$ with $\tilde x_i = \tilde u + \tilde e_i$, $\tilde u \sim N(0,\tau_u^{-1})$ common and $\tilde e_i \sim N(0,\tau_e^{-1})$ idiosyncratic ((2), (3)); and, having acquired sophistication $\tau_\eta$, she also observes $\tilde z_i = \tilde x_i + \tilde\eta_i$ with $\tilde\eta_i \sim N(0,\tau_\eta^{-1})$ (4). All shocks are independent and centred, and all investors share the sophistication level $\tau_\eta$. The **standing assumptions** are
--   $$\tau_v,\ \tau_\xi,\ \tau_\varepsilon,\ \tau_e,\ \tau_u,\ \tau_\eta,\ \gamma > 0.$$
--
--   **Bayesian updating.** The signal vector $S = (\tilde s_i, \tilde s_{p,i}, \tilde z_i) = (\tilde v + \tilde\varepsilon_i,\ \tilde v + (\alpha+1)\tilde u + \tilde e_i,\ \tilde u + \tilde e_i + \tilde\eta_i)$ has covariance matrix
--   $$\Sigma(\alpha) = \begin{pmatrix} \tau_v^{-1} + \tau_\varepsilon^{-1} & \tau_v^{-1} & 0 \\ \tau_v^{-1} & \tau_v^{-1} + (\alpha+1)^2\tau_u^{-1} + \tau_e^{-1} & (\alpha+1)\tau_u^{-1} + \tau_e^{-1} \\ 0 & (\alpha+1)\tau_u^{-1} + \tau_e^{-1} & \tau_u^{-1} + \tau_e^{-1} + \tau_\eta^{-1} \end{pmatrix}$$
--   and covariance $c = (\tau_v^{-1}, \tau_v^{-1}, 0)$ with $\tilde v$. The coefficients of the conditional mean (16) are $(\beta_s,\beta_p,\beta_z) = \Sigma(\alpha)^{-1}c$, so $E(\tilde V \mid S) = \beta_s\tilde s_i + \beta_p\tilde s_{p,i} + \beta_z\tilde z_i$, and the conditional variance is $\mathrm{Var}(\tilde V\mid S) = \tau_v^{-1} - c^\top\Sigma(\alpha)^{-1}c + \tau_\xi^{-1}$.
--
--   **Equilibrium.** Investor $i$'s demand is $D = (E(\tilde V\mid S) - \tilde p)/(\gamma\,\mathrm{Var}(\tilde V\mid S))$ (8). A **linear equilibrium** is a pair $(a_v, a_u)$ with $a_v \neq 0$ such that, for the conjectured price $\tilde p = a_v\tilde v + a_u\tilde u$ (11) and the induced price signal with $\alpha = a_u/a_v$ (12), aggregate demand vanishes (9) for every realization $(\tilde v,\tilde u)\in\mathbb R^2$. Aggregate demand is the demand evaluated at the cross-sectional mean $(\tilde v,\ \tilde v + (\alpha+1)\tilde u,\ \tilde u)$ of the signals, since the idiosyncratic noises $\tilde\varepsilon_i, \tilde e_i, \tilde\eta_i$ average out over the continuum.
--
--   **Closed forms used in statements.** The file also names the page's closed forms, which appear only in theorem statements, never in the equilibrium predicate:
--   $$\tau_p(\alpha) = \frac{\tau_e\tau_u + (\tau_e+\tau_u)\tau_\eta}{\tau_u + \tau_e(\alpha+1)^2 + \alpha^2\tau_\eta}\ \ (15),\qquad a_v(\alpha) = \frac{\tau_\varepsilon + \tau_p}{\tau_v + \tau_\varepsilon + \tau_p},\qquad a_u(\alpha) = \frac{\tau_p}{\tau_v+\tau_\varepsilon+\tau_p}\cdot\frac{\tau_u(\tau_e + \alpha\tau_e + \alpha\tau_\eta)}{\tau_e\tau_u + \tau_e\tau_\eta + \tau_u\tau_\eta},$$
--   the cubic $f(\alpha) = (\tau_e\tau_\varepsilon + \tau_\varepsilon\tau_\eta)\alpha^3 + 2\tau_e\tau_\varepsilon\alpha^2 + (\tau_e\tau_\varepsilon + \tau_e\tau_\eta + \tau_u\tau_\varepsilon)\alpha - \tau_e\tau_u$ of (18) (also as a Mathlib `Cubic`), and $\bar\alpha = \tau_e\tau_u/(\tau_e\tau_\varepsilon + \tau_e\tau_\eta + \tau_u\tau_\varepsilon)$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** All quantities are real. Gaussian conditioning is encoded in reduced form, as the linear projection $\Sigma^{-1}c$ of the jointly normal vector; the coefficients are not defined by the printed fractions. Market clearing "almost surely" is stated for every $(\tilde v,\tilde u)\in\mathbb R^2$, which is equivalent for linear functions of a nondegenerate Gaussian pair; the integral over investors is the demand at the averaged signals (the usual continuum convention). The condition $a_v \neq 0$ is part of the equilibrium predicate, as on p. 17 ("provided that $a_v \neq 0$ (which is true in equilibrium)"); without it $a_u/a_v$ would be Lean's junk value $0$. Equation (4) as printed attaches the law $N(0,\tau_{\eta_i}^{-1})$ to $\tilde z_i$; equations (5) and (15) show it is the law of $\tilde\eta_i$, which is the reading used here. `Matrix.inv` returns $0$ on a singular matrix; $\Sigma(\alpha)$ is nonsingular for every real $\alpha$ under the standing assumptions, which the milestone on the Bayes coefficients states.
-- source:
--   Vives & Yang, Costly Interpretation of Asset Prices, SSRN working paper 2763813 (September 2018 version), pp. 9–19 (PDF 11–21): §3.1 eqs. (1)–(5), §4 eqs. (8)–(9) and the equilibrium definition p. 17, §4.1 eqs. (11)–(18), Proposition 1; proof of Proposition 1, pp. 55–56 (PDF 54–55)

import Mathlib

namespace CostlyPriceInterp.MarketEq

/-- The primitive data of the Vives–Yang asset market (§3.1, pp. 9–12): the precisions
`tv` (τ_v) of the learnable fundamental ṽ, `txi` (τ_ξ) of the unlearnable part ξ̃, `teps` (τ_ε) of
the private-signal noise ε̃_i, `te` (τ_e) of the idiosyncratic interpretation noise ẽ_i, `tu` (τ_u)
of the common interpretation noise ũ, `teta` (τ_η) the common sophistication level (precision of
η̃_i), and the CARA risk aversion `gam` (γ). -/
structure Params where
  tv : ℝ
  txi : ℝ
  teps : ℝ
  te : ℝ
  tu : ℝ
  teta : ℝ
  gam : ℝ

/-- Standing assumptions (§3.1; Proposition 1; Corollary 1): every precision and γ is positive. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.tv ∧ 0 < P.txi ∧ 0 < P.teps ∧ 0 < P.te ∧ 0 < P.tu ∧ 0 < P.teta ∧ 0 < P.gam

/-- Σ(α): covariance matrix of investor i's signals (s̃_i, s̃_{p,i}, z̃_i)
= (ṽ + ε̃_i, ṽ + (α+1)ũ + ẽ_i, ũ + ẽ_i + η̃_i), when the price signal is s̃_p = ṽ + αũ. -/
noncomputable def sigCov (P : Params) (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 / P.tv + 1 / P.teps, 1 / P.tv, 0;
     1 / P.tv, 1 / P.tv + (α + 1) ^ 2 / P.tu + 1 / P.te, (α + 1) / P.tu + 1 / P.te;
     0, (α + 1) / P.tu + 1 / P.te, 1 / P.tu + 1 / P.te + 1 / P.teta]

/-- c: covariance of (s̃_i, s̃_{p,i}, z̃_i) with ṽ. -/
noncomputable def sigCovV (P : Params) : Fin 3 → ℝ :=
  ![1 / P.tv, 1 / P.tv, 0]

/-- (β_s, β_p, β_z) := Σ(α)⁻¹ c, the jointly-Gaussian conditional-mean coefficients of (16):
E(ṽ | s̃_i, s̃_{p,i}, z̃_i) = β_s s̃_i + β_p s̃_{p,i} + β_z z̃_i. -/
noncomputable def bayesCoef (P : Params) (α : ℝ) : Fin 3 → ℝ :=
  Matrix.mulVec (sigCov P α)⁻¹ (sigCovV P)

/-- Var(Ṽ | s̃_i, s̃_{p,i}, z̃_i) = (1/τ_v − c·Σ(α)⁻¹c) + 1/τ_ξ (Gaussian conditioning, Ṽ = ṽ + ξ̃). -/
noncomputable def condVarV (P : Params) (α : ℝ) : ℝ :=
  1 / P.tv - dotProduct (sigCovV P) (bayesCoef P α) + 1 / P.txi

/-- Cross-sectional mean of the signals given (ṽ, ũ): the idiosyncratic noises ε̃_i, ẽ_i, η̃_i
average out over the continuum, leaving (ṽ, ṽ + (α+1)ũ, ũ). -/
def avgSignals (α v u : ℝ) : Fin 3 → ℝ :=
  ![v, v + (α + 1) * u, u]

/-- Aggregate demand ∫₀¹ D_i di of (8)–(9) at the price p̃ = a_v ṽ + a_u ũ, with α = a_u / a_v:
the common CARA demand (E(Ṽ|·) − p̃)/(γ Var(Ṽ|·)) evaluated at the averaged signals. -/
noncomputable def aggDemand (P : Params) (av au v u : ℝ) : ℝ :=
  (dotProduct (bayesCoef P (au / av)) (avgSignals (au / av) v u) - (av * v + au * u)) /
    (P.gam * condVarV P (au / av))

/-- A linear financial market equilibrium (§4, p. 17; (11)): price coefficients (a_v, a_u) with
a_v ≠ 0 such that the market clears (9) for every realization (ṽ, ũ). -/
def IsLinearEq (P : Params) (av au : ℝ) : Prop :=
  av ≠ 0 ∧ ∀ v u : ℝ, aggDemand P av au v u = 0

/-- τ_p of (15) (common sophistication τ_η). -/
noncomputable def tauP (P : Params) (α : ℝ) : ℝ :=
  (P.te * P.tu + (P.te + P.tu) * P.teta) / (P.tu + P.te * (α + 1) ^ 2 + α ^ 2 * P.teta)

/-- The closed form of a_v in Proposition 1, as a function of α. -/
noncomputable def avOf (P : Params) (α : ℝ) : ℝ :=
  (P.teps + tauP P α) / (P.tv + P.teps + tauP P α)

/-- The closed form of a_u in Proposition 1, as a function of α. -/
noncomputable def auOf (P : Params) (α : ℝ) : ℝ :=
  tauP P α / (P.tv + P.teps + tauP P α) *
    (P.tu * (P.te + α * P.te + α * P.teta) / (P.te * P.tu + P.te * P.teta + P.tu * P.teta))

/-- f(α), the left-hand side of the cubic (18). -/
noncomputable def cubicF (P : Params) (α : ℝ) : ℝ :=
  (P.te * P.teps + P.teps * P.teta) * α ^ 3 + 2 * P.te * P.teps * α ^ 2
    + (P.te * P.teps + P.te * P.teta + P.tu * P.teps) * α - P.te * P.tu

/-- The cubic (18) as a Mathlib `Cubic`, with coefficients (a, b, c, d). -/
noncomputable def cubic18 (P : Params) : Cubic ℝ :=
  ⟨P.te * P.teps + P.teps * P.teta, 2 * P.te * P.teps,
    P.te * P.teps + P.te * P.teta + P.tu * P.teps, -(P.te * P.tu)⟩

/-- ᾱ = τ_eτ_u/(τ_eτ_ε + τ_eτ_η + τ_uτ_ε), the upper end of the interval containing α. -/
noncomputable def alphaBar (P : Params) : ℝ :=
  P.te * P.tu / (P.te * P.teps + P.te * P.teta + P.tu * P.teps)

end CostlyPriceInterp.MarketEq


