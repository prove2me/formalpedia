-- Prove2me | Definitions.Def_IdentityMgmt_FIA_Model
-- name    : IdentityMgmt_FIA_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:15.808666+00:00
-- url     : https://prove2.me/theorems/320bc497-1dae-47fc-8232-f1cd621cafe3
-- title:
--   §3–§4, pp. 14–25, OA pp. 1–3 — dynamic monopoly with identity management (FIA): quasi-linear cut-off and expectations rules, period profit, arbitrage, Euler and pivot conditions, MPE
-- statement:
--   **The model.** A monopolist sells a non-durable good at zero marginal cost in contracting periods $n = 0, 1, 2, \dots$, with per-period discount factor $\beta = e^{-\Delta} \in (0,1)$. A continuum of consumers has types $\theta$ uniform on $[0,1]$; type $\theta$ values one unit of the good per period at $\theta$. Under **full information acquisition (FIA)** a *passive* consumer who has bought once is recognised and charged her exact willingness to pay ever after. A consumer may instead pay a once-for-all **privacy cost** $c \ge 0$ and become *active*: she stays anonymous and buys every period at the introductory price $p^I(n)$ offered to newcomers. Types in $[\tilde\theta, 1]$ are active, types below the **pivot** $\tilde\theta$ are passive.
--
--   **Strategy profile.** A quasi-linear profile consists of numbers $(\beta, c, K, \gamma, C, \lambda, \tilde\theta)$ defining
--   - the firm's cut-off rule $\Phi(\theta) = K + \gamma\theta$ (new passive customers in period $n$ are the types in $[\theta_{n+1}, \theta_n)$, $\theta_{n+1} = \Phi(\theta_n)$);
--   - the consumers' expectations rule $\Psi(\theta) = C + \lambda\theta$, eq. (13): the lifetime net utility $U_n(\theta_{n+1})$ of the period-$n$ marginal passive customer when the state is $\theta_n = \theta$;
--   - the path $\theta_n = \Phi^{n}(\tilde\theta)$ with $\theta_0 = \tilde\theta$, its limit $\theta_{\inf} = K/(1-\gamma)$, and the introductory price (4)
--   $$p^I(n) = \theta_{n+1} - \frac{\Psi(\theta_n)}{1-\beta}.$$
--
--   **Period profit** (Online Appendix p. 3, the sum of (1), (6) and (7)): at state $x = \theta_n$ and choice $y = \theta_{n+1}$,
--   $$\pi(x, y) = (1-\beta)\Big[\frac{\tilde\theta^2 - x^2}{2} + (1 - \tilde\theta + x - y)\Big(y - \frac{\Psi(x)}{1-\beta}\Big)\Big].$$
--
--   **Equilibrium conditions**, each required at every state $\theta \in [0,1]$ where it is an identity in $\theta$:
--   1. *Arbitrage* (8): $\Psi(\theta) = \beta\big[\Psi(\Phi\theta) + (1-\beta)(\Phi\theta - \Phi(\Phi\theta))\big]$.
--   2. *Euler*: the first-order condition (16) of the Bellman equation (15) with the envelope condition (17), $\partial_y \pi(\theta, \Phi\theta) + \beta\, \partial_x \pi(\Phi\theta, \Phi(\Phi\theta)) = 0$.
--   3. *Pivot* (20): with the active gain $G = \beta\tilde\theta - c - \sum_{n\ge1}(1-\beta)p^I(n)\beta^n$, $G = 0$ if $\tilde\theta < 1$, and $G \le 0$ if $\tilde\theta = 1$.
--
--   A **Markov equilibrium** (for the pivot $\tilde\theta$) requires $0<\beta<1$, $0 \le \gamma < 1$, $0 \le \theta_{\inf} \le \tilde\theta \le 1$, arbitrage and Euler. An **MPE** additionally requires $c \ge 0$ and the pivot condition. Finally the threshold is
--   $$\bar c^{FIA} = \frac{\beta(1-\gamma)(1+(1-2\beta)\gamma)}{(1-\beta\gamma)^2}.$$
--
--   This is the common model of every statement of the mission: the equilibrium is a predicate, and none of the equilibrium quantities $K, \gamma, C, \lambda, \tilde\theta$ is given by a formula.
--
--   **Formalization Note.** The firm's best reply is encoded by its first-order system (16)–(17), as in the paper; the derivatives are Lean's `deriv` of the period profit, so no hand expansion is trusted (the printed envelope expression (23) has a sign slip). The boundary condition (14), $\lim \Psi(\theta_n) = 0$, is deliberately *not* part of the definition; it is derived (Proposition 1 (iii)). Feasibility is the weak $\theta_{\inf} \le \tilde\theta$ rather than strict expansion, because at $c = 0$ the equilibrium path is constant. The pivot condition at $\tilde\theta = 1$ is the inequality "type 1 does not gain from going active". The series in $G$ is a `tsum`; it is summable under $0<\beta<1$, $0\le\gamma<1$ (checked in a sorry-free sanity file), so it is a genuine sum.
-- source:
--   Laussel, Long & Resende, Profit Effects of Consumers' Identity Management: A Dynamic Model, CIRANO working paper 2021s-29 (24 Aug. 2021), pp. 14–25 (PDF 18–29), §3–§4, eqs. (1), (4), (6)–(8), (12)–(17); Online Appendix, OA pp. 1, 3 (PDF 55, 57), eq. (20) and π_n

import Mathlib

namespace IdentityMgmt.FIA

/-- A quasi-linear strategy profile of the FIA identity-management game (p. 24, (13)):
the discount factor `β = e^{-Δ}`, the privacy cost `c`, the cut-off rule
`θ_{n+1} = K + γ θ_n`, the expectations rule `Ψ(θ) = C + λ θ`, and the pivot type `θ̃`. -/
structure Profile where
  /-- discount factor per contracting period, `β = e^{-Δ}` (r = 1) -/
  β : ℝ
  /-- once-for-all privacy cost of becoming active -/
  c : ℝ
  /-- intercept of the cut-off rule `θ_{n+1} = K + γ θ_n` -/
  K : ℝ
  /-- slope of the cut-off rule -/
  γ : ℝ
  /-- intercept of the expectations rule `Ψ(θ) = C + λ θ` -/
  C : ℝ
  /-- slope `λ` of the expectations rule -/
  lam : ℝ
  /-- the pivot type `θ̃`: types in `[θ̃, 1]` are active, types below are passive -/
  θt : ℝ

/-- The firm's Markovian cut-off rule `Φ(θ) = K + γ θ` (p. 24). -/
def Profile.Φ (P : Profile) (θ : ℝ) : ℝ := P.K + P.γ * θ

/-- The consumers' Markovian expectations rule `Ψ(θ) = C + λ θ`, eq. (13): the lifetime net
utility `U_n(θ_{n+1})` of the period-`n` marginal passive customer when the state is `θ_n = θ`. -/
def Profile.Ψ (P : Profile) (θ : ℝ) : ℝ := P.C + P.lam * θ

/-- The market-expansion path `θ_n = Φ^[n](θ̃)`, with `θ_0 = θ̃` (p. 23). -/
def Profile.path (P : Profile) (n : ℕ) : ℝ := P.Φ^[n] P.θt

/-- The limiting cut-off `θ_inf = K / (1 - γ)` (p. 24). -/
noncomputable def Profile.θinf (P : Profile) : ℝ := P.K / (1 - P.γ)

/-- The introductory price of period `n`, eq. (4), with `U_n(θ_{n+1}) = Ψ(θ_n)`:
`p^I(n) = θ_{n+1} - Ψ(θ_n) / (1 - β)`. -/
noncomputable def Profile.pI (P : Profile) (n : ℕ) : ℝ :=
  P.path (n + 1) - P.Ψ (P.path n) / (1 - P.β)

/-- The FIA period profit `π_n(x, y)` at state `x = θ_n` and choice `y = θ_{n+1}`
(Online Appendix p. 3; the sum of (1), (6) and (7) with `U_n(θ_{n+1})` replaced by `Ψ(θ_n)`):
`(1 - β) [ (θ̃² - x²)/2 + (1 - θ̃ + x - y) (y - Ψ(x)/(1 - β)) ]`. -/
noncomputable def periodProfit (β θt : ℝ) (Ψ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (1 - β) * ((θt ^ 2 - x ^ 2) / 2 + (1 - θt + x - y) * (y - Ψ x / (1 - β)))

/-- Rational expectations: the FIA arbitrage (participation) equation (8),
`Ψ(θ) = β [Ψ(Φ θ) + (1 - β)(Φ θ - Φ(Φ θ))]`, at every state `θ ∈ [0, 1]`. -/
def Profile.Arbitrage (P : Profile) : Prop :=
  ∀ θ ∈ Set.Icc (0 : ℝ) 1,
    P.Ψ θ = P.β * (P.Ψ (P.Φ θ) + (1 - P.β) * (P.Φ θ - P.Φ (P.Φ θ)))

/-- The firm's best reply in first-order form: the FOC (16) of the Bellman equation (15),
with `V'(θ_{n+1})` given by the envelope condition (17), i.e. the partial derivative of the
period profit in the state, at every state `θ ∈ [0, 1]`. -/
def Profile.Euler (P : Profile) : Prop :=
  ∀ θ ∈ Set.Icc (0 : ℝ) 1,
    deriv (fun y => periodProfit P.β P.θt P.Ψ θ y) (P.Φ θ)
      + P.β * deriv (fun x => periodProfit P.β P.θt P.Ψ x (P.Φ (P.Φ θ))) (P.Φ θ) = 0

/-- The pivot type's gain from becoming active, the left side of (20):
`β θ̃ - c - Σ_{n ≥ 1} (1 - β) p^I(n) β^n`. -/
noncomputable def Profile.activeGain (P : Profile) : ℝ :=
  P.β * P.θt - P.c - ∑' n : ℕ, (1 - P.β) * P.pI (n + 1) * P.β ^ (n + 1)

/-- The pivot condition (20) with its corner: an interior pivot `θ̃ < 1` is indifferent between
being active and passive; at `θ̃ = 1` (everyone passive) type 1 does not gain from being active. -/
def Profile.Pivot (P : Profile) : Prop :=
  (P.θt < 1 → P.activeGain = 0) ∧ (P.θt = 1 → P.activeGain ≤ 0)

/-- A quasi-linear Markov equilibrium between the firm and the consumers for the pivot `θ̃`
(the object of Lemma 2): standing assumptions `0 < β < 1`, `0 ≤ γ < 1`, the range
`0 ≤ θ_inf ≤ θ̃ ≤ 1`, the arbitrage equation (8) and the Euler condition (16)–(17). -/
def Profile.IsMarkovEq (P : Profile) : Prop :=
  0 < P.β ∧ P.β < 1 ∧ 0 ≤ P.γ ∧ P.γ < 1 ∧
    0 ≤ P.θinf ∧ P.θinf ≤ P.θt ∧ P.θt ≤ 1 ∧ P.Arbitrage ∧ P.Euler

/-- A quasi-linear FIA Markov perfect equilibrium with endogenous privacy decisions (p. 24):
a Markov equilibrium for `θ̃`, a nonnegative privacy cost, and the pivot condition (20). -/
def Profile.IsMPE (P : Profile) : Prop :=
  P.IsMarkovEq ∧ 0 ≤ P.c ∧ P.Pivot

/-- The FIA privacy-cost threshold `c̄^FIA = β(1-γ)(1+(1-2β)γ)/(1-βγ)²` (p. 27). -/
noncomputable def cbarFIA (β γ : ℝ) : ℝ :=
  β * (1 - γ) * (1 + (1 - 2 * β) * γ) / (1 - β * γ) ^ 2

end IdentityMgmt.FIA


