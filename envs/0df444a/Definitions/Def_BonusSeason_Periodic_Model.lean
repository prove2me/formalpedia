-- Prove2me | Definitions.Def_BonusSeason_Periodic_Model
-- name    : BonusSeason_Periodic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:20.244204+00:00
-- url     : https://prove2.me/theorems/37b5f4f9-41f8-4db7-8b01-76270b5acb81
-- title:
--   §3–§4.4, pp. 6–27 — 2-periodic search labor market: matching function (A1), state equations, Nash-bargained values, turnover plans, periodic contracts, periodic equilibrium, α̲, ᾱ
-- statement:
--   This file sets up the search model of the labor market of Van Wesep and Waters and its periodic equilibrium.
--
--   **Parameters.** A continuum of firms of mass $M>0$ and of workers of mass $N>0$, $N\neq M$. Each firm employs at most one worker. Revenue is $1$ per period of employment. A worker's disutility of work is $x^L$ when well matched and $x^H$ when poorly matched, $0<x^L<x^H<1$. The discount factor is $\beta\in(0,1)$, the exogenous separation probability $\delta\in(0,1)$, the probability that a satisfied worker becomes dissatisfied $p\in(0,1)$, and the worker's bargaining weight $\theta\in(0,1)$. Write $\hat\beta=\beta(1-\delta)$ and define the **importance of match quality**
--   $$\alpha=\frac{x^H-x^L}{1-x^L}.$$
--
--   **Matching (Assumption A1).** If $M^0$ firms and $N^0$ workers search, $m(M^0,N^0)$ matches form, where $m$ is defined on $[0,\infty)^2$, satisfies $0\le m\le\min\{M^0,N^0\}$, is homogeneous of degree one, strictly increasing in each argument on $(0,\infty)$, and differentiable on $(0,\infty)^2$.
--
--   **Labor market.** Periods alternate between odd (index 1) and even (index 2). A market state records, at the start of each period, the mass $N^0_s$ of unemployed workers, $N^L_s$ of well matched and $N^H_s$ of poorly matched workers; vacant firms are $M^0_s=N^0_s+M-N$. The state **solves** the market equations if all masses are nonnegative, $N=N^L_s+N^H_s+N^0_s$, and
--   $$N^L_1=[N^L_2+m(M^0_2,N^0_2)](1-\delta)(1-p),\qquad N^L_2=[N^L_1+m(M^0_1,N^0_1)](1-\delta)(1-p),$$
--   $$N^0_1=[N^H_2+(N^L_2+m(M^0_2,N^0_2))p](1-\delta)+[N^0_2-m(M^0_2,N^0_2)](1-\delta)+N\delta,\qquad N^0_2=[N^0_1-m(M^0_1,N^0_1)](1-\delta)+N\delta.$$
--   The matching likelihoods are $f_s=m(M^0_s,N^0_s)/M^0_s$ for a vacant firm and $g_s=m(M^0_s,N^0_s)/N^0_s$ for an unemployed worker; $h_s=\theta g_s+(1-\theta)f_s$. The thresholds are
--   $$\underline\alpha=\frac{(1-h_1)(1-\hat\beta(1-p))(1+\hat\beta(1-h_2))}{1+\hat\beta(1-h_1)(p-\hat\beta(1-p)(1-h_2))},\qquad \overline\alpha=\frac{1-h_2-\hat\beta(1-p)(1-h_1)(h_2+\hat\beta(1-p)(1-h_2))}{1-\hat\beta^2(1-p)^2(1-h_1)(1-h_2)}.$$
--
--   **Values.** $J_s$ (firm with a new hire), $V_s$ (vacant firm), $W_s$ (new hire, gross of pay), $U_s$ (unemployed worker) and the bargained present value of pay $P_s$ solve equations (16)–(23) of the paper, with the matching likelihoods above, and $P_1$, $P_2$ maximize the Nash products $(W_1+P-\beta U_2)^\theta(J_1-P-\beta V_2)^{1-\theta}$ and $(W_2+P-\beta U_1)^\theta(J_2-P-\beta V_1)^{1-\theta}$ over the transfers both sides accept. The surpluses are $S_1=J_1-\beta V_2+W_1-\beta U_2$ and $S_2=J_2-\beta V_1+W_2-\beta U_1$.
--
--   **Turnover plans.** A plan says whether a dissatisfied worker quits at the end of an odd and of an even period; satisfied workers never quit. The periodic plan quits only after even periods. For a plan, the joint values $X_{sL}$, $X_{sH}$ of a match in period $s$ with a satisfied or dissatisfied worker solve
--   $$X_{sL}=1-x^L+\beta\big[\delta\Gamma_{s'}+(1-\delta)\big((1-p)X_{s'L}+p\,Q_{s'}\big)\big],\qquad X_{sH}=1-x^H+\beta\big[\delta\Gamma_{s'}+(1-\delta)\,Q_{s'}\big],$$
--   where $s'$ is the other period, $\Gamma_s=U_s+V_s$, and $Q_{s'}=\Gamma_{s'}$ if the plan has a dissatisfied worker quit at the end of period $s$, $Q_{s'}=X_{s'H}$ otherwise. The periodic plan is **Pareto optimal** if no plan gives a newly matched pair more than $J_1+W_1$ (odd hire) or $J_2+W_2$ (even hire).
--
--   **Periodic contracts** $\{b^s_1,b^s_2,w_1,w_2\}$ pay a signing bonus $b^s_1$ ($b^s_2$) on an odd (even) hire and wages $w_1$, $w_2$ in odd and even periods. Their present values are (30)–(31), and they are **incentive compatible** if they satisfy (32), (34)–(35) and (36).
--
--   A **periodic equilibrium** consists of a market state solving the market equations with $N^0_1\neq N^0_2$, values solving (16)–(25), Pareto optimality of the periodic plan, and an incentive-compatible periodic contract whose present values are $P_1$ and $P_2$.
--
--   **Formalization Note** (1) Equation (21) is printed as $W_2=-x^L+\beta((1-p)W_1+pU_1)$, which omits $\delta$; it is used in the form $W_2=-x^L+\beta((1-\delta)(1-p)W_1+[1-(1-\delta)(1-p)]U_1)$, consistent with (17), (87) and (29), which fails with the printed form. (2) "Increasing" in A1 is read strictly; Lemma 2's strict inequalities need it. (3) Definition D3 is imposed through $N^0_1\neq N^0_2$ only. (4) Pareto optimality compares the four turnover plans that are stationary across periods of the same parity, as the proof of Proposition 1 does with its conditions (i) and (ii). (5) Search (D2.1) is costless and always weakly optimal, and beliefs (D2.5) are the equilibrium objects themselves, so neither has a separate clause. (6) The stationary value $T$ of (34) is required to exist, with $T\ge U_1$; the recursion has exactly one solution. (7) Present values are `tsum`s; they are summable since $\hat\beta(1-p)\in(0,1)$. All quantities are real numbers.
-- source:
--   Van Wesep & Waters, Bonus season: A theory of periodic labor markets and coordinated bonuses, SSRN 3124536 (version of January 13, 2021), pp. 6–27 (PDF 7–28), §3, §4.1–4.4, Assumption A1, Definitions D1–D3, eqs. (2)–(3), (11)–(12), (16)–(25), (30)–(36), (42)–(44); proof of Lemma 2, p. 45 (PDF 46), eqs. (46)–(59)

import Mathlib

namespace BonusSeason.Periodic

/-- The exogenous parameters of the model (§3, pp. 6–8): masses `M` of firms and `N` of workers,
disutilities `xL < xH` of a well and a poorly matched worker, discount factor `β`, exogenous
separation probability `δ`, probability `p` that a satisfied worker becomes dissatisfied, and the
worker's bargaining weight `θ`. -/
structure Params where
  M : ℝ
  N : ℝ
  xL : ℝ
  xH : ℝ
  β : ℝ
  δ : ℝ
  p : ℝ
  θ : ℝ

/-- The standing assumptions of §3 (pp. 6–8): `M, N > 0`, `N ≠ M`, `0 < xL < xH < 1`,
`β, δ, p, θ ∈ (0, 1)`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.M ∧ 0 < P.N ∧ P.M ≠ P.N ∧ 0 < P.xL ∧ P.xL < P.xH ∧ P.xH < 1 ∧
  0 < P.β ∧ P.β < 1 ∧ 0 < P.δ ∧ P.δ < 1 ∧ 0 < P.p ∧ P.p < 1 ∧ 0 < P.θ ∧ P.θ < 1

/-- `β̂ = β(1 − δ)` (p. 22). -/
def Params.βhat (P : Params) : ℝ := P.β * (1 - P.δ)

/-- The importance of match quality `α = (xH − xL)/(1 − xL)`, eq. (42), p. 27. -/
noncomputable def Params.matchImportance (P : Params) : ℝ := (P.xH - P.xL) / (1 - P.xL)

/-- Assumption (A1), p. 9, for a matching function `m(M⁰, N⁰)` on the closed quadrant:
`0 ≤ m ≤ min{M⁰, N⁰}`, homogeneous of degree one, (strictly) increasing in each argument on the
open half-line, and differentiable on the open quadrant. "Increasing" is read strictly. -/
def MatchingA1 (m : ℝ → ℝ → ℝ) : Prop :=
  (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ m a b ∧ m a b ≤ min a b) ∧
  (∀ l a b : ℝ, 0 < l → 0 ≤ a → 0 ≤ b → m (l * a) (l * b) = l * m a b) ∧
  (∀ b : ℝ, 0 < b → StrictMonoOn (fun a => m a b) (Set.Ioi 0)) ∧
  (∀ a : ℝ, 0 < a → StrictMonoOn (fun b => m a b) (Set.Ioi 0)) ∧
  DifferentiableOn ℝ (Function.uncurry m) (Set.Ioi 0 ×ˢ Set.Ioi 0)

/-- A 2-periodic labor-market state (index 1 = odd period, 2 = even period): masses of
unemployed workers `N0`, of well matched workers `NL` and of poorly matched workers `NH` at the
start of each period. Firm masses are derived: `Mᴸ = Nᴸ`, `Mᴴ = Nᴴ` ((50)–(53)) and
`M⁰ = N⁰ + M − N` ((58)–(59)). -/
structure MarketState where
  N0₁ : ℝ
  N0₂ : ℝ
  NL₁ : ℝ
  NL₂ : ℝ
  NH₁ : ℝ
  NH₂ : ℝ

/-- Vacant firms at the start of an odd period, `M⁰₁ = N⁰₁ + M − N` (58). -/
def MarketState.M0₁ (L : MarketState) (P : Params) : ℝ := L.N0₁ + P.M - P.N

/-- Vacant firms at the start of an even period, `M⁰₂ = N⁰₂ + M − N` (59). -/
def MarketState.M0₂ (L : MarketState) (P : Params) : ℝ := L.N0₂ + P.M - P.N

/-- `L` solves the labor-market equations (46)–(57) of the proof of Lemma 2 (p. 45) under the
periodic turnover plan (11)–(12): all masses are nonnegative, (48)–(49) and the flow equations
(54)–(57); (46)–(47), (50)–(53) are built into the derived firm masses. -/
def MarketState.Solves (L : MarketState) (P : Params) (m : ℝ → ℝ → ℝ) : Prop :=
  0 ≤ L.N0₁ ∧ 0 ≤ L.N0₂ ∧ 0 ≤ L.NL₁ ∧ 0 ≤ L.NL₂ ∧ 0 ≤ L.NH₁ ∧ 0 ≤ L.NH₂ ∧
  0 ≤ L.M0₁ P ∧ 0 ≤ L.M0₂ P ∧
  P.N = L.NL₁ + L.NH₁ + L.N0₁ ∧
  P.N = L.NL₂ + L.NH₂ + L.N0₂ ∧
  L.NL₁ = (L.NL₂ + m (L.M0₂ P) L.N0₂) * (1 - P.δ) * (1 - P.p) ∧
  L.NL₂ = (L.NL₁ + m (L.M0₁ P) L.N0₁) * (1 - P.δ) * (1 - P.p) ∧
  L.N0₁ = (L.NH₂ + (L.NL₂ + m (L.M0₂ P) L.N0₂) * P.p) * (1 - P.δ)
      + (L.N0₂ - m (L.M0₂ P) L.N0₂) * (1 - P.δ) + P.N * P.δ ∧
  L.N0₂ = (L.N0₁ - m (L.M0₁ P) L.N0₁) * (1 - P.δ) + P.N * P.δ

/-- Likelihood that a vacant firm matches in an odd period, `f₁ = m(M⁰₁, N⁰₁)/M⁰₁` (2). -/
noncomputable def MarketState.f₁ (L : MarketState) (P : Params) (m : ℝ → ℝ → ℝ) : ℝ :=
  m (L.M0₁ P) L.N0₁ / L.M0₁ P

/-- Likelihood that a vacant firm matches in an even period, `f₂ = m(M⁰₂, N⁰₂)/M⁰₂` (2). -/
noncomputable def MarketState.f₂ (L : MarketState) (P : Params) (m : ℝ → ℝ → ℝ) : ℝ :=
  m (L.M0₂ P) L.N0₂ / L.M0₂ P

/-- Likelihood that an unemployed worker matches in an odd period, `g₁ = m(M⁰₁, N⁰₁)/N⁰₁` (3). -/
noncomputable def MarketState.g₁ (L : MarketState) (P : Params) (m : ℝ → ℝ → ℝ) : ℝ :=
  m (L.M0₁ P) L.N0₁ / L.N0₁

/-- Likelihood that an unemployed worker matches in an even period, `g₂ = m(M⁰₂, N⁰₂)/N⁰₂` (3). -/
noncomputable def MarketState.g₂ (L : MarketState) (P : Params) (m : ℝ → ℝ → ℝ) : ℝ :=
  m (L.M0₂ P) L.N0₂ / L.N0₂

/-- `h₁ = θg₁ + (1 − θ)f₁` (p. 22). -/
noncomputable def MarketState.h₁ (L : MarketState) (P : Params) (m : ℝ → ℝ → ℝ) : ℝ :=
  P.θ * L.g₁ P m + (1 - P.θ) * L.f₁ P m

/-- `h₂ = θg₂ + (1 − θ)f₂` (p. 22). -/
noncomputable def MarketState.h₂ (L : MarketState) (P : Params) (m : ℝ → ℝ → ℝ) : ℝ :=
  P.θ * L.g₂ P m + (1 - P.θ) * L.f₂ P m

/-- The lower match-quality threshold `α̲`, eq. (43), p. 27. -/
noncomputable def alphaLow (P : Params) (m : ℝ → ℝ → ℝ) (L : MarketState) : ℝ :=
  (1 - L.h₁ P m) * (1 - P.βhat * (1 - P.p)) * (1 + P.βhat * (1 - L.h₂ P m)) /
    (1 + P.βhat * (1 - L.h₁ P m) * (P.p - P.βhat * (1 - P.p) * (1 - L.h₂ P m)))

/-- The upper match-quality threshold `ᾱ`, eq. (44), p. 27. -/
noncomputable def alphaHigh (P : Params) (m : ℝ → ℝ → ℝ) (L : MarketState) : ℝ :=
  (1 - L.h₂ P m - P.βhat * (1 - P.p) * (1 - L.h₁ P m) *
      (L.h₂ P m + P.βhat * (1 - P.p) * (1 - L.h₂ P m))) /
    (1 - P.βhat ^ 2 * (1 - P.p) ^ 2 * (1 - L.h₁ P m) * (1 - L.h₂ P m))

/-- Generalized Nash bargaining over a transfer (p. 22): `x` maximizes the Nash product
`(a + x)^θ (b − x)^(1−θ)` over the transfers `x'` acceptable to both sides
(`a + x' ≥ 0`, `b − x' ≥ 0`), where `a` is the worker's and `b` the firm's gain from the match
net of its outside option, gross of the transfer. -/
def IsNashTransfer (θ a b x : ℝ) : Prop :=
  0 ≤ a + x ∧ 0 ≤ b - x ∧
  ∀ x' : ℝ, 0 ≤ a + x' → 0 ≤ b - x' →
    (a + x') ^ θ * (b - x') ^ (1 - θ) ≤ (a + x) ^ θ * (b - x) ^ (1 - θ)

/-- Firm and worker values under the periodic turnover plan (pp. 20–22): firm with a newly hired
worker `J`, vacant firm `V`, newly hired worker gross of pay `W`, unemployed worker `U`, and the
bargained present value of pay `P`, in odd (1) and even (2) periods. -/
structure Values where
  J₁ : ℝ
  J₂ : ℝ
  V₁ : ℝ
  V₂ : ℝ
  W₁ : ℝ
  W₂ : ℝ
  U₁ : ℝ
  U₂ : ℝ
  P₁ : ℝ
  P₂ : ℝ

/-- Surplus of an odd-period match, `S₁ = J₁ − βV₂ + W₁ − βU₂` (p. 22). -/
def Values.S₁ (X : Values) (P : Params) : ℝ := X.J₁ - P.β * X.V₂ + X.W₁ - P.β * X.U₂

/-- Surplus of an even-period match, `S₂ = J₂ − βV₁ + W₂ − βU₁` (p. 22). -/
def Values.S₂ (X : Values) (P : Params) : ℝ := X.J₂ - P.β * X.V₁ + X.W₂ - P.β * X.U₁

/-- `X` solves the value equations (16)–(23), with (21) in its δ-corrected form, and the transfers
`P₁`, `P₂` are the generalized Nash bargaining solutions of p. 22, with matching likelihoods taken
from the labor-market state `L`. -/
def Values.Solves (X : Values) (P : Params) (L : MarketState) (m : ℝ → ℝ → ℝ) : Prop :=
  X.J₁ = 1 + P.β * (1 - P.δ) + P.β * P.δ * X.V₂ + P.β ^ 2 * (1 - P.δ) *
      ((1 - P.δ) * (1 - P.p) ^ 2 * X.J₁ + (1 - (1 - P.δ) * (1 - P.p) ^ 2) * X.V₁) ∧
  X.J₂ = 1 + P.β * ((1 - P.δ) * (1 - P.p) * X.J₁ + (1 - (1 - P.δ) * (1 - P.p)) * X.V₁) ∧
  X.V₁ = L.f₁ P m * (X.J₁ - X.P₁) + (1 - L.f₁ P m) * P.β * X.V₂ ∧
  X.V₂ = L.f₂ P m * (X.J₂ - X.P₂) + (1 - L.f₂ P m) * P.β * X.V₁ ∧
  X.W₁ = -P.xL - P.β * (1 - P.δ) * ((1 - P.p) * P.xL + P.p * P.xH) + P.β * P.δ * X.U₂ +
      P.β ^ 2 * (1 - P.δ) *
        ((1 - P.δ) * (1 - P.p) ^ 2 * X.W₁ + (1 - (1 - P.δ) * (1 - P.p) ^ 2) * X.U₁) ∧
  X.W₂ = -P.xL + P.β * ((1 - P.δ) * (1 - P.p) * X.W₁ + (1 - (1 - P.δ) * (1 - P.p)) * X.U₁) ∧
  X.U₁ = L.g₁ P m * (X.W₁ + X.P₁) + (1 - L.g₁ P m) * P.β * X.U₂ ∧
  X.U₂ = L.g₂ P m * (X.W₂ + X.P₂) + (1 - L.g₂ P m) * P.β * X.U₁ ∧
  IsNashTransfer P.θ (X.W₁ - P.β * X.U₂) (X.J₁ - P.β * X.V₂) X.P₁ ∧
  IsNashTransfer P.θ (X.W₂ - P.β * X.U₁) (X.J₂ - P.β * X.V₁) X.P₂

/-- A turnover plan: whether a dissatisfied worker quits at the end of an odd period (`.1`) and at
the end of an even period (`.2`); a satisfied worker never quits ((11), p. 17). -/
abbrev Plan := Bool × Bool

/-- The periodic plan (12), p. 17: quit only when dissatisfied at the end of an even period. -/
def periodicPlan : Plan := (false, true)

/-- Joint (firm plus worker) values of a match, gross of transfers, at the start of an odd/even
period with a satisfied (`L`) or dissatisfied (`H`) worker. -/
structure JointValues where
  x1L : ℝ
  x2L : ℝ
  x1H : ℝ
  x2H : ℝ

/-- `Y` solves the joint-value recursion of the plan `a`, given the pair's joint values
`Γ₁`, `Γ₂` of being unmatched at the start of an odd/even period. Within a period: revenue `1`
minus disutility; then separation (prob. `δ`), then dissatisfaction of a satisfied worker
(prob. `p`), then quitting according to `a`. -/
def PlanValues (P : Params) (Γ₁ Γ₂ : ℝ) (a : Plan) (Y : JointValues) : Prop :=
  Y.x1L = 1 - P.xL + P.β * (P.δ * Γ₂ +
      (1 - P.δ) * ((1 - P.p) * Y.x2L + P.p * (if a.1 then Γ₂ else Y.x2H))) ∧
  Y.x2L = 1 - P.xL + P.β * (P.δ * Γ₁ +
      (1 - P.δ) * ((1 - P.p) * Y.x1L + P.p * (if a.2 then Γ₁ else Y.x1H))) ∧
  Y.x1H = 1 - P.xH + P.β * (P.δ * Γ₂ + (1 - P.δ) * (if a.1 then Γ₂ else Y.x2H)) ∧
  Y.x2H = 1 - P.xH + P.β * (P.δ * Γ₁ + (1 - P.δ) * (if a.2 then Γ₁ else Y.x1H))

/-- Pareto optimality of the periodic plan (proof of Proposition 1, p. 51): for a newly matched
pair in either period, no turnover plan yields a higher joint value than the periodic one,
`J₁ + W₁` resp. `J₂ + W₂`, with outside values `Γ_s = U_s + V_s`. -/
def PeriodicPlanOptimal (P : Params) (X : Values) : Prop :=
  ∀ (a : Plan) (Y : JointValues), PlanValues P (X.U₁ + X.V₁) (X.U₂ + X.V₂) a Y →
    Y.x1L ≤ X.J₁ + X.W₁ ∧ Y.x2L ≤ X.J₂ + X.W₂

/-- A periodic contract `{b₁ˢ, b₂ˢ, w₁, w₂}` (p. 25): signing bonuses for an odd and an even-period
hire, and wages paid in odd and in even periods. -/
structure PeriodicContract where
  b₁ : ℝ
  b₂ : ℝ
  w₁ : ℝ
  w₂ : ℝ

/-- Payment `k` periods after an odd-period hire (bonus included at `k = 0`). -/
def PeriodicContract.oddStream (c : PeriodicContract) (k : ℕ) : ℝ :=
  if k = 0 then c.b₁ + c.w₁ else if Even k then c.w₁ else c.w₂

/-- Payment `k` periods after an even-period hire (bonus included at `k = 0`). -/
def PeriodicContract.evenStream (c : PeriodicContract) (k : ℕ) : ℝ :=
  if k = 0 then c.b₂ + c.w₂ else if Even k then c.w₂ else c.w₁

/-- Present value of pay for an odd-period hire under periodic quitting, eq. (30), p. 24. -/
noncomputable def pvOdd (P : Params) (c : PeriodicContract) : ℝ :=
  ∑' k : ℕ, P.βhat ^ (2 * k) * (1 - P.p) ^ (2 * k) *
    (c.oddStream (2 * k) + P.βhat * c.oddStream (2 * k + 1))

/-- Present value of pay for an even-period hire under periodic quitting, eq. (31), p. 24. -/
noncomputable def pvEven (P : Params) (c : PeriodicContract) : ℝ :=
  c.evenStream 0 + ∑' k : ℕ, P.βhat ^ (2 * k + 1) * (1 - P.p) ^ (2 * k + 1) *
    (c.evenStream (2 * k + 1) + P.βhat * c.evenStream (2 * k + 2))

/-- The periodic contract `c` induces the periodic plan (pp. 24–25): constraint (32) (a
dissatisfied worker stays after an odd period), (34)–(35) (a satisfied worker stays after an even
period, `T` the stationary solution of the recursion (34)), and (36) (a dissatisfied worker quits
after an even period). -/
def IncentiveCompatible (P : Params) (X : Values) (c : PeriodicContract) : Prop :=
  c.w₂ - P.xH + P.β * X.U₁ ≥ X.U₂ ∧
  (∃ T : ℝ,
    T = c.w₁ - P.xL + P.β * (1 - P.δ) * (c.w₂ - (1 - P.p) * P.xL - P.p * P.xH) +
        P.β * P.δ * X.U₂ + P.β ^ 2 * (1 - P.δ) *
          ((1 - P.δ) * (1 - P.p) ^ 2 * T + (1 - (1 - P.δ) * (1 - P.p) ^ 2) * X.U₁) ∧
    T ≥ X.U₁) ∧
  c.w₁ - P.xH + P.β * (1 - P.δ) * (c.w₂ - P.xH) + P.β * P.δ * X.U₂ +
      P.β ^ 2 * (1 - P.δ) * X.U₁ ≤ X.U₁

/-- A periodic equilibrium (§4, Definition D3 with `j = 0`): a labor-market state solving
(46)–(57) whose depth alternates, values solving (16)–(25) with Nash-bargained transfers, the
periodic plan Pareto optimal for every newly matched pair, and a periodic contract inducing the
periodic plan whose present values are the bargained `P₁`, `P₂`. -/
def PeriodicEquilibrium (P : Params) (m : ℝ → ℝ → ℝ) : Prop :=
  ∃ (L : MarketState) (X : Values) (c : PeriodicContract),
    L.Solves P m ∧ L.N0₁ ≠ L.N0₂ ∧ X.Solves P L m ∧ PeriodicPlanOptimal P X ∧
    IncentiveCompatible P X c ∧ pvOdd P c = X.P₁ ∧ pvEven P c = X.P₂

end BonusSeason.Periodic


