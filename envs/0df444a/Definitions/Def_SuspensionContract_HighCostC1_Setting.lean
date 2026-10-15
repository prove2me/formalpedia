-- Prove2me | Definitions.Def_SuspensionContract_HighCostC1_Setting
-- name    : SuspensionContract_HighCostC1_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:41.199988+00:00
-- url     : https://prove2.me/theorems/48957be5-b922-4d79-a311-105c230aa616
-- title:
--   §2–§4, pp. 7–20 — parameters, Assumption 1, β, v̲, w̄, V̄, V̄(w), R̂, Conditions 1–2, the operators 𝒜_I, 𝒜_∅ (18)–(19) and the optimality condition (20)–(22)
-- statement:
--   This file fixes the primitives of the continuous-time principal–agent model with switching cost of Cao, Sun and Tian.
--
--   A principal faces a Poisson stream of arrivals, each worth a revenue $R$. Without effort the arrival rate is $\underline\mu$; an agent who exerts effort, at cost $b$ per unit of time, raises it to $\mu>\underline\mu$. The principal's total cost rate while directing the agent to work is $c\ge b$, and restarting work costs a fixed amount $K>0$. The principal discounts at rate $r$ and the agent at rate $\rho$. The **standing assumptions** are
--
--   $$0\le\underline\mu<\mu,\qquad 0<b\le c,\qquad K>0,\qquad 0<r\le\rho,\qquad R\,\Delta\mu>c\ \text{(Assumption 1)},$$
--
--   with $\Delta\mu=\mu-\underline\mu$. The derived constants are
--
--   $$\beta=\frac{b}{\Delta\mu},\quad \bar w=\frac{\beta\mu}{\rho}\ (9),\quad \underline v=\frac{\underline\mu R}{r}\ (8),\quad \bar V=\frac{R\mu-c-(\rho-r)\bar w}{r}\ (10),\quad \bar V(w)=\frac{R\mu-c-(\rho-r)w}{r}\ (27),$$
--
--   and $\hat R=\Big[\frac{c}{b}+\frac{(\rho-r)\mu}{\Delta\mu(\rho-r-\mu)}\cdot\frac{\rho-\mu}{\rho}\Big]\beta$ (28). **Condition 1** is "$\mu\ge\rho-r$ or $R<\hat R$"; **Condition 2** is its negation "$\mu<\rho-r$ and $R\ge\hat R$".
--
--   For a function $f$ on $\mathbb R_+$ the operators (18)–(19) are
--
--   $$(\mathcal A_I f)(w)=(\mu+r)f(w)-\mu f(w+\beta)+\rho(\bar w-w)f'(w)-(\mu R-c)+(\rho-r)w,$$
--   $$(\mathcal A_\emptyset f)(w)=rf(w)-\rho wf'(w)+(\rho-r)w-R\underline\mu,$$
--
--   where $f'(w)$ is the left derivative. A pair $(V_I,V_\emptyset)$ satisfies the **optimality condition (20)–(22)** if $(\mathcal A_I V_I)(w)\ge0$ and $(\mathcal A_\emptyset V_\emptyset)(w)\ge0$, $0\le V_I(w)-V_\emptyset(w)\le K$, and $V_I(0)\ge\underline v$, $V_\emptyset(0)\ge\underline v$. By the paper's Theorem 1, such a pair certifies an upper bound on the principal's utility.
--
--   **Formalization Note** Functions are `ℝ → ℝ`; only their values on $w\ge0$ matter. The derivative in $\mathcal A_I,\mathcal A_\emptyset$ is the left derivative `derivWithin f (Set.Iic w) w` (the paper's convention on p. 15). Inequality (20) is required for $w>0$ only: at $w=0$ a left derivative of a function on $\mathbb R_+$ does not exist; (21) is required for $w\ge0$ and (22) at $0$ exactly as printed. $\underline\mu\ge0$ and $b>0$ are added to the standing assumptions (a rate and a cost; $\bar w$ is positive only if $b>0$). The formula for $\hat R$ divides by $\rho-r-\mu$, which vanishes only inside Condition 1's first disjunct, where Lean's value $x/0=0$ is irrelevant.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, pp. 7–8 (§2, Assumption 1), p. 10 (Proposition 1(ii)), pp. 11–12 (8)–(10), pp. 15–16 (18)–(22), pp. 19–21 (27), (28), Conditions 1–2

import Mathlib

namespace SuspensionContract.HighCostC1

/-- Model parameters of Cao–Sun–Tian (§2, pp. 7–8). The paper writes `µ` for the arrival rate
under effort (`μ` here) and `µ̲` for the base arrival rate (`μlow` here). -/
structure Params where
  /-- revenue per arrival -/
  R : ℝ
  /-- arrival rate when the agent exerts effort (the paper's µ) -/
  μ : ℝ
  /-- base arrival rate without effort (the paper's µ̲) -/
  μlow : ℝ
  /-- agent's effort cost rate -/
  b : ℝ
  /-- principal's total cost rate when the agent works -/
  c : ℝ
  /-- fixed switching (set-up) cost -/
  K : ℝ
  /-- principal's discount rate -/
  r : ℝ
  /-- agent's discount rate -/
  ρ : ℝ

namespace Params

variable (P : Params)

/-- Standing assumptions of §2 (pp. 7–8): `0 ≤ µ̲ < µ`, `0 < b ≤ c`, `K > 0`, `0 < r ≤ ρ`, and
Assumption 1, `RΔµ > c`. (`µ̲ ≥ 0` and `b > 0` are disclosed additions: rates and costs.) -/
def Standing : Prop :=
  0 ≤ P.μlow ∧ P.μlow < P.μ ∧ 0 < P.b ∧ P.b ≤ P.c ∧ 0 < P.K ∧ 0 < P.r ∧ P.r ≤ P.ρ ∧
    P.c < P.R * (P.μ - P.μlow)

/-- `Δµ = µ − µ̲` (p. 7). -/
noncomputable def Δμ : ℝ := P.μ - P.μlow

/-- `β = b / Δµ` (Proposition 1(ii), p. 10). -/
noncomputable def β : ℝ := P.b / P.Δμ

/-- `w̄ = βµ/ρ` (9). -/
noncomputable def wbar : ℝ := P.β * P.μ / P.ρ

/-- `v̲ = µ̲R/r` (8). -/
noncomputable def vlow : ℝ := P.μlow * P.R / P.r

/-- `V̄ = (Rµ − c − (ρ − r)w̄)/r` (10). -/
noncomputable def Vbar : ℝ := (P.R * P.μ - P.c - (P.ρ - P.r) * P.wbar) / P.r

/-- `V̄(w) = (Rµ − c − (ρ − r)w)/r` (27). -/
noncomputable def VbarFn (w : ℝ) : ℝ := (P.R * P.μ - P.c - (P.ρ - P.r) * w) / P.r

/-- `R̂ = [c/b + (ρ − r)µ/(Δµ(ρ − r − µ)) · (ρ − µ)/ρ] β` (28). Its denominator `ρ − r − µ`
vanishes only when `µ = ρ − r`, which lies inside Condition 1's first disjunct, where `R̂` is
irrelevant (Lean's `x / 0 = 0` there). -/
noncomputable def Rhat : ℝ :=
  (P.c / P.b + (P.ρ - P.r) * P.μ / (P.Δμ * (P.ρ - P.r - P.μ)) * ((P.ρ - P.μ) / P.ρ)) * P.β

/-- Condition 1 (28): `µ ≥ ρ − r` or `R < R̂`. -/
def Condition1 : Prop := P.ρ - P.r ≤ P.μ ∨ P.R < P.Rhat

/-- Condition 2 (p. 21): `µ < ρ − r` and `R ≥ R̂` (the negation of Condition 1). -/
def Condition2 : Prop := P.μ < P.ρ - P.r ∧ P.Rhat ≤ P.R

/-- The working-state operator `𝒜_I` of (18), with `f′(w)` the left derivative at `w` (p. 15). -/
noncomputable def AI (f : ℝ → ℝ) (w : ℝ) : ℝ :=
  (P.μ + P.r) * f w - P.μ * f (w + P.β) + P.ρ * (P.wbar - w) * derivWithin f (Set.Iic w) w
    - (P.μ * P.R - P.c) + (P.ρ - P.r) * w

/-- The suspension-state operator `𝒜_∅` of (19), with `f′(w)` the left derivative at `w`. -/
noncomputable def A0 (f : ℝ → ℝ) (w : ℝ) : ℝ :=
  P.r * f w - P.ρ * w * derivWithin f (Set.Iic w) w + (P.ρ - P.r) * w - P.R * P.μlow

/-- The optimality condition (20)–(22) of Theorem 1 (p. 16); (20) is required for `w > 0`,
(21) for `w ≥ 0`, and (22) at `0`. -/
def OptCond (VI V0 : ℝ → ℝ) : Prop :=
  (∀ w, 0 < w → 0 ≤ P.AI VI w ∧ 0 ≤ P.A0 V0 w) ∧
    (∀ w, 0 ≤ w → 0 ≤ VI w - V0 w ∧ VI w - V0 w ≤ P.K) ∧
    P.vlow ≤ VI 0 ∧ P.vlow ≤ V0 0

end Params

end SuspensionContract.HighCostC1


