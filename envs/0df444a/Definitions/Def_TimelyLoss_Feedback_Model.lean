-- Prove2me | Definitions.Def_TimelyLoss_Feedback_Model
-- name    : TimelyLoss_Feedback_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:10.431048+00:00
-- url     : https://prove2.me/theorems/b1522169-7589-4e13-aa80-4354227c2fc8
-- title:
--   §2–§3, pp. 7–17 (PDF 8–18) — feedback-effect trading game with asymmetric reporting timeliness
-- statement:
--   This definition sets up the trading game of Chen, Huang, Jiang, Zhang and Zhang with a feedback effect from prices to investment.
--
--   **Firm.** The state $\theta\in\{H,L\}$ has prior $\Pr(\theta=H)=\Pr(\theta=L)=1/2$. The firm chooses $d\in\{-1,0,1\}$ (decrease, keep, increase investment), and terminal value is
--
--   $$v(\theta,0)=R_\theta,\quad v(H,1)=R_H+x-c,\quad v(H,-1)=R_H-x-c,\quad v(L,-1)=R_L+x-c,\quad v(L,1)=R_L-x-c.$$
--
--   With posterior $\mu$ of state $H$, an uninformed firm invests iff $\mu>\bar\mu=\tfrac12+\tfrac{c}{2x}$, divests iff $\mu<\underline\mu=\tfrac12-\tfrac{c}{2x}$, and otherwise keeps the status quo.
--
--   **Reporting.** The firm privately learns $\theta$ with probability $f$ (signal $\delta=\theta$), and otherwise receives a null signal $\delta=\phi$. An informed firm reports $\theta$ with probability $\beta_\theta$, where $\beta_H=\beta-\xi$ and $\beta_L=\beta+\xi$; otherwise the report is null, $r=\phi$. Hence $\Pr(r=\phi\mid\theta)=(1-f)+f(1-\beta_\theta)$. The parameter $\xi$ is *feasible* when $0\le\beta\pm\xi\le1$. After a null report,
--   $$t=\Pr(\theta=H\mid r=\phi),\qquad \tau_\theta=\Pr(\delta=\theta\mid\theta,r=\phi),\qquad R'_\theta=R_\theta+\tau_\theta(x-c),$$
--   with $t$ and $\tau_\theta$ computed by Bayes' rule.
--
--   **Trading.** A speculator learns $\theta$ with probability $\lambda$; a noise trader submits $z\in\{-1,0,1\}$, each with probability $1/3$, independently. Two speculator profiles after a null report are considered: no trading (NT), and trading (T), in which an informed speculator buys on $H$ and sells on $L$. Given a profile, the order flow $X=s+z$ has a state-conditional likelihood; the uninformed firm's posterior $\mu_F^{\phi,X}$ uses prior $1/2$ and the market maker's posterior $\mu_M^{\phi,X}$ uses prior $t$. The price is $P(X,\phi)=E[v\mid X,r=\phi]$, where an informed firm (probability $\tau_\theta$ given $\theta$) adjusts correctly and an uninformed one follows the threshold rule at $\mu_F^{\phi,X}$.
--
--   **Profits.** $\pi^\sigma_{buy}$ is the expected gross profit $E[v-P(X,\phi)]$ of an informed speculator who buys one share on $\eta=H$, and $\pi^\sigma_{sell}$ that of selling on $\eta=L$, against the prices and firm response of profile $\sigma\in\{NT,T\}$, averaged over the noise order. The thresholds are
--
--   $$\kappa^{NT}=\max\{\pi^{NT}_{buy},\pi^{NT}_{sell}\},\qquad \kappa^T=\min\{\pi^T_{buy},\pi^T_{sell}\}.$$
--
--   The standing assumptions are $0<c<x$, $R_L+x<R_H-x$, $0<\beta<1$ and $\lambda>2c/(x+c)$.
--
--   **Formalization Note** All quantities are real numbers and order flows are integers. The firm's and the market maker's equilibrium behaviour (threshold investment rule, Bayesian price) is built into the definitions; the speculator's profits are computed against it. Posteriors $t$, $\tau_\theta$, $\mu_F$, $\mu_M$ are explicit Bayes ratios, not the paper's closed forms (1), (3), (6), (7). On an order flow of probability zero (only $X=\pm2$ under NT) the belief is $H$ for $X>0$ and $L$ otherwise, the paper's off-path convention (pp. 15, 33). Investment ties keep the status quo (p. 12). The standing predicate adds $\lambda<1$ and $0<f<1$ to the paper's list: both are probabilities, and at the endpoints the strict conclusions of Corollary 2(i) and Proposition 4 fail.
-- source:
--   Chen, Huang, Jiang, Zhang & Zhang, The Role of Asymmetric Disclosure When Price Efficiency Affects Real Efficiency, working paper (PDF of 2018-08; published as "Asymmetric Reporting Timeliness and Informational Feedback", Management Science 2021), pp. 7–17 (PDF 8–18), §§2.1–3.2

import Mathlib

namespace TimelyLoss.Feedback

/-- The state of the world: good (`H`) or bad (`L`), each with prior probability 1/2. -/
inductive State | H | L
  deriving DecidableEq

/-- The firm's investment decision `d`: `down` is d = −1, `keep` is d = 0, `up` is d = 1. -/
inductive Dec | down | keep | up
  deriving DecidableEq

/-- Primitive parameters: values `RH`, `RL` without adjustment, adjustment gain `x`, adjustment
cost `c`, probability `f` that the firm learns the state, overall timeliness `β`, and probability
`lam` (λ) that the speculator learns the state. -/
structure Params where
  RH : ℝ
  RL : ℝ
  x : ℝ
  c : ℝ
  f : ℝ
  β : ℝ
  lam : ℝ

noncomputable section

/-- Standing assumptions of §2.1: `0 < c < x`, `R_L + x < R_H − x`, `0 < β < 1`,
`2c/(x+c) < λ`; plus `λ < 1` and `0 < f < 1` (probabilities, made explicit). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.c ∧ P.c < P.x ∧ P.RL + P.x < P.RH - P.x ∧
  0 < P.β ∧ P.β < 1 ∧ 2 * P.c / (P.x + P.c) < P.lam ∧
  P.lam < 1 ∧ 0 < P.f ∧ P.f < 1

/-- A disclosure asymmetry `ξ` is feasible when `β_H = β − ξ` and `β_L = β + ξ` lie in `[0,1]`. -/
def Params.Feasible (P : Params) (ξ : ℝ) : Prop :=
  0 ≤ P.β - ξ ∧ P.β - ξ ≤ 1 ∧ 0 ≤ P.β + ξ ∧ P.β + ξ ≤ 1

/-- Disclosure probability of an informed firm in state θ: `β_H = β − ξ`, `β_L = β + ξ`. -/
def betaOf (P : Params) (ξ : ℝ) : State → ℝ
  | .H => P.β - ξ
  | .L => P.β + ξ

/-- Firm value `R_θ` under the status quo. -/
def asset (P : Params) : State → ℝ
  | .H => P.RH
  | .L => P.RL

/-- The correct adjustment in each state. -/
def correct : State → Dec
  | .H => .up
  | .L => .down

/-- Terminal firm value `v(θ, d)`. -/
def v (P : Params) (θ : State) : Dec → ℝ
  | .keep => asset P θ
  | d => if d = correct θ then asset P θ + P.x - P.c else asset P θ - P.x - P.c

/-- Upper investment threshold `µ̄ = 1/2 + c/(2x)` and lower threshold `µ̲ = 1/2 − c/(2x)`. -/
def muBar (P : Params) : ℝ := 1 / 2 + P.c / (2 * P.x)
def muLow (P : Params) : ℝ := 1 / 2 - P.c / (2 * P.x)

/-- Expected terminal value of decision `d` under posterior probability `μ` of state `H`. -/
def expectedValue (P : Params) (μ : ℝ) (d : Dec) : ℝ :=
  μ * v P .H d + (1 - μ) * v P .L d

/-- The firm's rule: invest iff `µ̄ < μ`, divest iff `μ < µ̲`, otherwise keep (ties keep). -/
noncomputable def firmRule (P : Params) (μ : ℝ) : Dec :=
  if muBar P < μ then .up else if μ < muLow P then .down else .keep

/-- `Pr(r = φ | θ) = (1 − f) + f(1 − β_θ)`: the report is null if the firm is uninformed, or
informed but does not disclose. -/
def probNull (P : Params) (ξ : ℝ) (θ : State) : ℝ :=
  (1 - P.f) + P.f * (1 - betaOf P ξ θ)

/-- `t = Pr(θ = H | r = φ)`, by Bayes' rule from the prior 1/2. -/
def tNull (P : Params) (ξ : ℝ) : ℝ :=
  ((1 / 2 : ℝ) * probNull P ξ .H) /
    ((1 / 2 : ℝ) * probNull P ξ .H + (1 / 2 : ℝ) * probNull P ξ .L)

/-- `τ_θ = Pr(δ = θ | θ, r = φ)`, the probability that the firm is informed given θ and a null report. -/
def tau (P : Params) (ξ : ℝ) (θ : State) : ℝ :=
  P.f * (1 - betaOf P ξ θ) / probNull P ξ θ

/-- `R′_θ = R_θ + τ_θ (x − c)`, Eq. (5). -/
def Rprime (P : Params) (ξ : ℝ) (θ : State) : ℝ :=
  asset P θ + tau P ξ θ * (P.x - P.c)

/-- An informed speculator's pure strategy after a null report: buy on `η = H`? sell on `η = L`? -/
structure Strategy where
  buyOnH : Bool
  sellOnL : Bool

/-- No-trading profile `NT` and trading profile `T`. -/
def NT : Strategy := ⟨false, false⟩
def T : Strategy := ⟨true, true⟩

/-- The informed speculator's order in state θ under σ. -/
def order (σ : Strategy) : State → ℤ
  | .H => if σ.buyOnH then 1 else 0
  | .L => if σ.sellOnL then -1 else 0

/-- Support of the noise order `z`, each value with probability 1/3. -/
def noise : Finset ℤ := {-1, 0, 1}

/-- `Pr(X | θ)` under σ: the speculator is informed w.p. λ (then orders `order σ θ`) and
uninformed w.p. 1 − λ (no order); the noise order is independent and uniform. -/
def lik (P : Params) (σ : Strategy) (θ : State) (X : ℤ) : ℝ :=
  ∑ z ∈ noise, (1 / 3 : ℝ) *
    (P.lam * (if order σ θ + z = X then 1 else 0) +
     (1 - P.lam) * (if z = X then 1 else 0))

/-- Bayes posterior of `H` given order flow `X` from `prior`; on a zero-probability flow the
off-path belief is `H` for `X > 0` and `L` otherwise. -/
noncomputable def post (P : Params) (σ : Strategy) (prior : ℝ) (X : ℤ) : ℝ :=
  if prior * lik P σ .H X + (1 - prior) * lik P σ .L X = 0 then
    if 0 < X then 1 else 0
  else
    prior * lik P σ .H X /
      (prior * lik P σ .H X + (1 - prior) * lik P σ .L X)

/-- Posterior of an uninformed firm (`δ = φ`, prior 1/2) after order flow `X`. -/
noncomputable def muF (P : Params) (σ : Strategy) (X : ℤ) : ℝ :=
  post P σ (1 / 2) X

/-- Market maker's posterior after a null report (prior `t`) and order flow `X`. -/
noncomputable def muM (P : Params) (σ : Strategy) (ξ : ℝ) (X : ℤ) : ℝ :=
  post P σ (tNull P ξ) X

/-- `E[v | θ, r = φ, X]`: informed firm (w.p. `τ_θ`) adjusts correctly, uninformed firm follows
`firmRule` at its posterior. -/
noncomputable def valueGiven (P : Params) (σ : Strategy) (ξ : ℝ)
    (θ : State) (X : ℤ) : ℝ :=
  tau P ξ θ * v P θ (correct θ) +
    (1 - tau P ξ θ) * v P θ (firmRule P (muF P σ X))

/-- Price after a null report: `P(X, φ) = E[v | X, r = φ]`. -/
noncomputable def price (P : Params) (σ : Strategy) (ξ : ℝ) (X : ℤ) : ℝ :=
  muM P σ ξ X * valueGiven P σ ξ .H X +
    (1 - muM P σ ξ X) * valueGiven P σ ξ .L X

/-- Gross expected profit of an informed speculator who buys on `η = H` (resp. sells on `η = L`)
after a null report, against the prices and firm response of profile σ, averaged over noise. -/
noncomputable def buyProfit (P : Params) (σ : Strategy) (ξ : ℝ) : ℝ :=
  ∑ z ∈ noise, (1 / 3 : ℝ) *
    (valueGiven P σ ξ .H (1 + z) - price P σ ξ (1 + z))

noncomputable def sellProfit (P : Params) (σ : Strategy) (ξ : ℝ) : ℝ :=
  ∑ z ∈ noise, (1 / 3 : ℝ) *
    (price P σ ξ (-1 + z) - valueGiven P σ ξ .L (-1 + z))

/-- `π^NT_buy`, `π^NT_sell`, `π^T_buy`, `π^T_sell`. -/
noncomputable def piNTbuy (P : Params) (ξ : ℝ) : ℝ := buyProfit P NT ξ
noncomputable def piNTsell (P : Params) (ξ : ℝ) : ℝ := sellProfit P NT ξ
noncomputable def piTbuy (P : Params) (ξ : ℝ) : ℝ := buyProfit P T ξ
noncomputable def piTsell (P : Params) (ξ : ℝ) : ℝ := sellProfit P T ξ

/-- `κ^T = min{π^T_buy, π^T_sell}` (Proposition 2). -/
noncomputable def kappaT (P : Params) (ξ : ℝ) : ℝ :=
  min (piTbuy P ξ) (piTsell P ξ)

/-- `κ^NT = max{π^NT_buy, π^NT_sell}` (Proposition 1). -/
noncomputable def kappaNT (P : Params) (ξ : ℝ) : ℝ :=
  max (piNTbuy P ξ) (piNTsell P ξ)

end
end TimelyLoss.Feedback


