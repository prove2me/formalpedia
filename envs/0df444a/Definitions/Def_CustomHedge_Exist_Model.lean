-- Prove2me | Definitions.Def_CustomHedge_Exist_Model
-- name    : CustomHedge_Exist_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:12.630888+00:00
-- url     : https://prove2.me/theorems/2d32613c-9747-49f6-86fe-1ee5d9c886d8
-- title:
--   §2.2–§3.2, pp. 7–11 — combined custom hedging market: pricing kernel, mean–variance criterion, problem (4), system (5), r_XI, kernel K, Π^X_0, operator T
-- statement:
--   A **combined custom hedging market** consists of a probability space $(\Omega,\mathcal F,P)$ and
--
--   1. a claimable risk term $X$, a nonclaimable term $Y$ and a side index $I$, random elements with values in arbitrary measurable spaces; $\mathcal F_X=\sigma(X)$ and $\mathcal F_I=\sigma(I)$;
--   2. a Borel revenue function $\pi(x,y)$ (the operating control $q$ is fixed and suppressed, as in §§3–4 of the paper), giving the business position $\pi=\pi(X,Y)$;
--   3. a pricing kernel $dQ/dP$ of an equivalent martingale measure $Q$, so that $\mathbb E_Q[Z]=\mathbb E[Z\,dQ/dP]$;
--   4. scalars $\varrho$ and $a$ of the mean–variance criterion $\mathcal U(Z)=\varrho\,\mathbb E[Z]-\tfrac a2\operatorname{Var}[Z]$.
--
--   **Standing assumptions.** $P$ is a probability; $X,Y,I$ and $\pi$ are measurable; $\pi(X,Y)\in L^2(P)$; $dQ/dP$ is measurable, $P$-a.s. positive, of $P$-mean one and in $L^2(P)$; $\varrho\ge0$; $a>0$.
--
--   A pair $(H,G)$ is **feasible** for the value-centered problem if $H\in\mathcal H_X$, $G\in\mathcal H_I$ and $\mathbb E_Q[H]=\mathbb E_Q[G]=0$, and it is **optimal** if it is feasible and
--   $$\mathcal U\big(\pi+[H+G]\big)=\max_{(H',G')\ \text{feasible}}\mathcal U\big(\pi+[H'+G']\big).\qquad(4)$$
--   A pair $(H_0,G_0)$ satisfies the **first-order system (5)** if, $P$-a.s.,
--   $$\begin{aligned}H_0&=-\mathbb E[\pi-\mathbb E\pi\mid\mathcal F_X]+\mathbb E\big[\tfrac\varrho a\big(1-\tfrac{dQ}{dP}\big)\,\big|\,\mathcal F_X\big]-\mathbb E[G_0\mid\mathcal F_X],\\ G_0&=-\mathbb E[\pi-\mathbb E\pi\mid\mathcal F_I]+\mathbb E\big[\tfrac\varrho a\big(1-\tfrac{dQ}{dP}\big)\,\big|\,\mathcal F_I\big]-\mathbb E[H_0\mid\mathcal F_I].\end{aligned}$$
--   Finally, $r_{XI}=r(\mathcal F_X,\mathcal F_I)$ is the maximal correlation (6) of $X$ and $I$; $\mathcal K=\pi+(\varrho/a)\,dQ/dP$ is the **optimal hedging kernel**; $\Pi^X_0=-\mathbb E\big[\mathcal K-\mathbb E[\mathcal K\mid\mathcal F_I]\,\big|\,\mathcal F_X\big]$ is the part of $\mathcal K$ unspanned by $I$, as estimated from $X$; and $T[Z]=\mathbb E\big[\mathbb E[Z\mid\mathcal F_I]\,\big|\,\mathcal F_X\big]$.
--
--   These objects are the whole setting of the existence and uniqueness theorem for optimal combined custom hedges.
--
--   **Formalization Note** Claims are random variables $\Omega\to\mathbb R$ measurable for $\sigma(X)$ (resp. $\sigma(I)$), as on pp. 7–8 of the paper, not payoff functions of $x$. The paper assumes $a\ge0$; $a>0$ is added because $\mathcal K$ and system (5) divide by $a$, and with $a=0$ problem (4) has no maximizer in general. $\varrho=0$ (a variance-minimizing firm) is allowed. The $L^2$ conditions on $\pi$ and $dQ/dP$ are those of Appendix EC.2.1. Conditional expectation is Mathlib's `condExp`, which is the true conditional expectation here because $\sigma(X),\sigma(I)\subseteq\mathcal F$ and all its arguments are integrable under the standing assumptions.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), pp. 6–11 (PDF 6–11), §2.1–§3.2, (4), (5), (6), (7); p. ec15 (PDF 46), Appendix EC.2.1; p. ec24 (PDF 55), (EC.26) and the operator T

import Mathlib
import Definitions.Def_CustomHedge_Exist_MaxCorr

namespace CustomHedge.Exist

open MeasureTheory ProbabilityTheory

/-- The combined custom hedging market of §2: a probability space `(Ω, 𝓕, P)`, the claimable
risk term `X`, the nonclaimable term `Y`, the side index `I` (random elements valued in
arbitrary measurable spaces), the business revenue function `π(x, y)` (the operating control
`q` is fixed and suppressed), the pricing kernel `D = dQ/dP`, and the mean–variance
coefficients `ϱ` (`rho`) and `a`. -/
structure Market (Ω EX EY EI : Type*) [MeasurableSpace Ω] [MeasurableSpace EX]
    [MeasurableSpace EY] [MeasurableSpace EI] where
  /-- the physical probability `P` -/
  P : Measure Ω
  /-- claimable term `X` -/
  X : Ω → EX
  /-- nonclaimable term `Y` -/
  Y : Ω → EY
  /-- side index `I` -/
  I : Ω → EI
  /-- revenue function `π(x, y)` -/
  revenue : EX → EY → ℝ
  /-- pricing kernel `dQ/dP` -/
  D : Ω → ℝ
  /-- the coefficient `ϱ` of the mean -/
  rho : ℝ
  /-- the coefficient `a` of the variance -/
  a : ℝ

namespace Market

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

/-- The business position `π = π(X, Y)`. -/
def pos (M : Market Ω EX EY EI) : Ω → ℝ := fun ω => M.revenue (M.X ω) (M.Y ω)

/-- `𝓕_X = σ(X)`. -/
def FX (M : Market Ω EX EY EI) : MeasurableSpace Ω := MeasurableSpace.comap M.X inferInstance

/-- `𝓕_I = σ(I)`. -/
def FI (M : Market Ω EX EY EI) : MeasurableSpace Ω := MeasurableSpace.comap M.I inferInstance

/-- Standing assumptions (§2.2–§2.3 and Appendix EC.2.1): `P` is a probability; `X, Y, I` are
random elements; `π` is Borel and `π(X, Y) ∈ L²`; the pricing kernel `dQ/dP` is measurable,
a.s. positive (`Q ~ P`), has `P`-mean one and lies in `L²`; `ϱ ≥ 0`; and `a > 0`
(the paper says `a ≥ 0`; `a > 0` is added because `K` and (5) divide by `a`). -/
def Standing (M : Market Ω EX EY EI) : Prop :=
  IsProbabilityMeasure M.P ∧ Measurable M.X ∧ Measurable M.Y ∧ Measurable M.I ∧
    Measurable (Function.uncurry M.revenue) ∧ MemLp M.pos 2 M.P ∧
    Measurable M.D ∧ (∀ᵐ ω ∂M.P, 0 < M.D ω) ∧ ∫ ω, M.D ω ∂M.P = 1 ∧ MemLp M.D 2 M.P ∧
    0 ≤ M.rho ∧ 0 < M.a

/-- Risk-neutral expectation `E_Q[Z] = E[Z · dQ/dP]`. -/
noncomputable def EQ (M : Market Ω EX EY EI) (Z : Ω → ℝ) : ℝ := ∫ ω, Z ω * M.D ω ∂M.P

/-- Mean–variance criterion `U(Z) = ϱ E[Z] - (a/2) Var[Z]`. -/
noncomputable def U (M : Market Ω EX EY EI) (Z : Ω → ℝ) : ℝ :=
  M.rho * ∫ ω, Z ω ∂M.P - M.a / 2 * variance Z M.P

/-- Feasible pairs of the value-centered problem (4):
`H ∈ 𝓗_X`, `G ∈ 𝓗_I`, `E_Q[H] = E_Q[G] = 0`. -/
def Feasible (M : Market Ω EX EY EI) (H G : Ω → ℝ) : Prop :=
  InClaims M.P M.FX H ∧ InClaims M.P M.FI G ∧ M.EQ H = 0 ∧ M.EQ G = 0

/-- `(H, G)` is an optimal combined claim pair of problem (4): it is feasible and maximizes
`U(π + [H + G])` over all feasible pairs. -/
def IsOptimal (M : Market Ω EX EY EI) (H G : Ω → ℝ) : Prop :=
  M.Feasible H G ∧
    ∀ H' G', M.Feasible H' G' → M.U (M.pos + H' + G') ≤ M.U (M.pos + H + G)

/-- The first-order system (5) for a pair `(H₀, G₀)`, `P`-a.s.:
`H₀ = -E[π - E[π] | 𝓕_X] + E[(ϱ/a)(1 - dQ/dP) | 𝓕_X] - E[G₀ | 𝓕_X]` and
`G₀ = -E[π - E[π] | 𝓕_I] + E[(ϱ/a)(1 - dQ/dP) | 𝓕_I] - E[H₀ | 𝓕_I]`. -/
def FirstOrder (M : Market Ω EX EY EI) (H₀ G₀ : Ω → ℝ) : Prop :=
  H₀ =ᵐ[M.P]
      -condExp M.FX M.P (fun ω => M.pos ω - ∫ ω', M.pos ω' ∂M.P)
        + condExp M.FX M.P (fun ω => M.rho / M.a * (1 - M.D ω))
        - condExp M.FX M.P G₀ ∧
    G₀ =ᵐ[M.P]
      -condExp M.FI M.P (fun ω => M.pos ω - ∫ ω', M.pos ω' ∂M.P)
        + condExp M.FI M.P (fun ω => M.rho / M.a * (1 - M.D ω))
        - condExp M.FI M.P H₀

/-- Maximal correlation `r_XI` (6) of `X` and `I`. -/
noncomputable def maxCorr (M : Market Ω EX EY EI) : ℝ := maximalCorrelation M.P M.FX M.FI

/-- Optimal hedging kernel `K = π + (ϱ/a) dQ/dP`. -/
noncomputable def K (M : Market Ω EX EY EI) : Ω → ℝ := fun ω => M.pos ω + M.rho / M.a * M.D ω

/-- `Π^X_0 = -E[K - E[K | 𝓕_I] | 𝓕_X]` (Theorem 1, (7); `Π_0` in (EC.26)). -/
noncomputable def Pi0X (M : Market Ω EX EY EI) : Ω → ℝ :=
  -condExp M.FX M.P (M.K - condExp M.FI M.P M.K)

/-- The operator `T[Z] = E[E[Z | 𝓕_I] | 𝓕_X]`. -/
noncomputable def T (M : Market Ω EX EY EI) (Z : Ω → ℝ) : Ω → ℝ :=
  condExp M.FX M.P (condExp M.FI M.P Z)

end Market

end CustomHedge.Exist


