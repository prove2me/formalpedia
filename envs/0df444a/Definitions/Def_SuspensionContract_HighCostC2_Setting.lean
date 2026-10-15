-- Prove2me | Definitions.Def_SuspensionContract_HighCostC2_Setting
-- name    : SuspensionContract_HighCostC2_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:47.610791+00:00
-- url     : https://prove2.me/theorems/7b59782a-546d-4388-b955-b6f43717c089
-- title:
--   §2–§4.1.2, pp. 7–24 — parameters, Assumption 1, β, v̲, w̄, V̄, R̂, K̄₂, Conditions 1–2, the operators 𝒜_I, 𝒜_∅ (18)–(19), the optimality condition (20)–(22) and the value functions (31)–(32)
-- statement:
--   **Model parameters.** A principal earns a revenue $R$ per arrival of a Poisson process. Without the agent's effort the arrival rate is $\underline\mu$; with effort (costing the agent $b$ per unit of time) it is $\mu>\underline\mu$. The principal's total cost rate while the agent works is $c$, every (re)start of work costs a fixed switching cost $K$, and the principal and the agent discount at rates $r$ and $\rho$. The **standing assumptions** of §2 are
--   $$0\le\underline\mu<\mu,\qquad 0<b\le c,\qquad K>0,\qquad 0<r\le\rho,\qquad R\,\Delta\mu>c\ \ (\text{Assumption 1}),$$
--   where $\Delta\mu=\mu-\underline\mu$.
--
--   **Derived constants.** $\beta=b/\Delta\mu$, $\bar w=\beta\mu/\rho$ (9), $\underline v=\underline\mu R/r$ (8), $\bar V=(R\mu-c-(\rho-r)\bar w)/r$ (10), the switching-cost threshold $\bar K_2=\bar V-\underline v-\bar w$ (K2), and the revenue threshold (28)
--   $$\hat R=\Big[\frac cb+\frac{(\rho-r)\mu}{\Delta\mu(\rho-r-\mu)}\cdot\frac{\rho-\mu}{\rho}\Big]\beta .$$
--   **Condition 1** is "$\mu\ge\rho-r$ or $R<\hat R$"; **Condition 2** is "$\mu<\rho-r$ and $R\ge\hat R$".
--
--   **Operators.** For a function $f$ on $\mathbb R_+$, with $f'(w)$ its left derivative,
--   $$(\mathcal A_I f)(w)=(\mu+r)f(w)-\mu f(w+\beta)+\rho(\bar w-w)f'(w)-(\mu R-c)+(\rho-r)w,\qquad(18)$$
--   $$(\mathcal A_\emptyset f)(w)=rf(w)-\rho wf'(w)+(\rho-r)w-R\underline\mu.\qquad(19)$$
--   A pair $(V_I,V_\emptyset)$ satisfies the **optimality condition (20)–(22)** if $(\mathcal A_IV_I)(w)\ge0$ and $(\mathcal A_\emptyset V_\emptyset)(w)\ge0$ (20), $0\le V_I(w)-V_\emptyset(w)\le K$ (21), and $V_I(0)\ge\underline v$, $V_\emptyset(0)\ge\underline v$ (22).
--
--   **Value functions of Proposition 4.**
--   $$V_I(w)=\begin{cases}\underline v+\dfrac{\bar V-\underline v}{\bar w}\,w,& w\in[0,\bar w],\\ \bar V,& w\ge\bar w,\end{cases}\ (31)\qquad V_\emptyset(w)=\begin{cases}\underline v+\dfrac{\bar V-\underline v-K}{\bar w}\,w,& w\in[0,\bar w],\\ \bar V-K,& w\ge\bar w.\end{cases}\ (32)$$
--
--   These are the objects in which the paper's guess-and-verify argument for the not-hiring region under Condition 2 is stated. The stochastic contract model itself is not formalized.
--
--   **Formalization Note.** Parameters are real fields of one structure. $\underline\mu\ge0$ and $b>0$ are added to the page's assumptions (a rate, and a cost rate whose positivity makes $\bar w>0$, which (31)–(32) divide by). Functions are `ℝ → ℝ`; $f'(w)$ in (18)–(19) is `derivWithin f (Set.Iic w) w`, the left derivative, as the paper prescribes on p. 15. In `OptCond`, (20) is required for $w>0$ only (at $w=0$ a left derivative on $\mathbb R_+$ does not exist), while (21) is required for every $w\ge0$ and (22) as printed. `Rhat` uses Lean's $x/0=0$ when $\rho-r-\mu=0$, which happens only inside Condition 1. At $w=\bar w$ both branches of (31) and of (32) agree, and the Lean `if w ≤ w̄` takes the first.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, pp. 7–24: §2 pp. 7–8 (model, Assumption 1), Proposition 1(ii) p. 10 (β), (8)–(10) pp. 10–12, (18)–(22) pp. 15–16, (28) p. 20, Condition 2 p. 21, (K2) p. 23, (31) p. 23, (32) p. 24

import Mathlib

namespace SuspensionContract.HighCostC2

/-- Parameters of the principal–agent model with switching cost (Cao, Sun, Tian, §2, pp. 7–8).
`R` revenue per arrival; `μ` arrival rate when the agent works (the paper's µ); `μlow` base arrival
rate (the paper's µ̲); `b` the agent's effort cost rate; `c` the principal's total cost rate while
the agent works; `K` the switching (set-up) cost; `r`, `ρ` the principal's and the agent's
discount rates. -/
structure Params where
  R : ℝ
  μ : ℝ
  μlow : ℝ
  b : ℝ
  c : ℝ
  K : ℝ
  r : ℝ
  ρ : ℝ

namespace Params

variable (P : Params)

/-- Standing assumptions of §2 (pp. 7–8): `0 ≤ µ̲ < µ`, `0 < b ≤ c`, `K > 0`, `0 < r ≤ ρ`, and
Assumption 1, `RΔµ > c`. (`µ̲ ≥ 0` and `b > 0` are read off the model: a rate and a cost rate.) -/
def Standing : Prop :=
  (0 ≤ P.μlow ∧ P.μlow < P.μ) ∧ (0 < P.b ∧ P.b ≤ P.c) ∧ 0 < P.K ∧ (0 < P.r ∧ P.r ≤ P.ρ) ∧
    P.c < P.R * (P.μ - P.μlow)

/-- `Δµ = µ − µ̲` (p. 7). -/
noncomputable def Δμ : ℝ := P.μ - P.μlow

/-- `β = b/Δµ` (Proposition 1(ii), p. 10). -/
noncomputable def β : ℝ := P.b / P.Δμ

/-- `w̄ = βµ/ρ` (9). -/
noncomputable def wbar : ℝ := P.β * P.μ / P.ρ

/-- `v̲ = µ̲R/r` (8). -/
noncomputable def vlow : ℝ := P.μlow * P.R / P.r

/-- `V̄ = (Rµ − c − (ρ − r)w̄)/r` (10). -/
noncomputable def Vbar : ℝ := (P.R * P.μ - P.c - (P.ρ - P.r) * P.wbar) / P.r

/-- `R̂ = [c/b + (ρ − r)µ/(Δµ(ρ − r − µ)) · (ρ − µ)/ρ] β` (28). When `ρ − r − µ = 0` Lean's
`x / 0 = 0` gives a junk value; this only happens inside Condition 1's first disjunct, never
under Condition 2. -/
noncomputable def Rhat : ℝ :=
  (P.c / P.b + (P.ρ - P.r) * P.μ / (P.Δμ * (P.ρ - P.r - P.μ)) * ((P.ρ - P.μ) / P.ρ)) * P.β

/-- `K̄₂ = V̄ − v̲ − w̄` (K2), p. 23. -/
noncomputable def Kbar2 : ℝ := P.Vbar - P.vlow - P.wbar

/-- Condition 1 (28): `µ ≥ ρ − r` or `R < R̂`. -/
def Condition1 : Prop := P.ρ - P.r ≤ P.μ ∨ P.R < P.Rhat

/-- Condition 2 (p. 21): `µ < ρ − r` and `R ≥ R̂`. -/
def Condition2 : Prop := P.μ < P.ρ - P.r ∧ P.Rhat ≤ P.R

/-- The working-state operator (18):
`(𝒜_I f)(w) = (µ + r)f(w) − µf(w + β) + ρ(w̄ − w)f′(w) − (µR − c) + (ρ − r)w`,
where `f′(w)` is the left derivative (p. 15). -/
noncomputable def AI (f : ℝ → ℝ) (w : ℝ) : ℝ :=
  (P.μ + P.r) * f w - P.μ * f (w + P.β) + P.ρ * (P.wbar - w) * derivWithin f (Set.Iic w) w
    - (P.μ * P.R - P.c) + (P.ρ - P.r) * w

/-- The suspension-state operator (19): `(𝒜_∅ f)(w) = r f(w) − ρ w f′(w) + (ρ − r)w − Rµ̲`,
with `f′(w)` the left derivative (p. 15). -/
noncomputable def A0 (f : ℝ → ℝ) (w : ℝ) : ℝ :=
  P.r * f w - P.ρ * w * derivWithin f (Set.Iic w) w + (P.ρ - P.r) * w - P.R * P.μlow

/-- The optimality condition (20)–(22) of Theorem 1 for a pair `(V_I, V_∅)`: (20) for `w > 0`,
(21) for `w ≥ 0`, and (22). -/
def OptCond (VI V0 : ℝ → ℝ) : Prop :=
  (∀ w, 0 < w → 0 ≤ P.AI VI w ∧ 0 ≤ P.A0 V0 w) ∧
    (∀ w, 0 ≤ w → 0 ≤ VI w - V0 w ∧ VI w - V0 w ≤ P.K) ∧ P.vlow ≤ VI 0 ∧ P.vlow ≤ V0 0

/-- The working-state value function (31), p. 23: the line from `v̲` at `0` to `V̄` at `w̄`,
constant `V̄` for `w ≥ w̄`. (Both branches give `V̄` at `w = w̄`.) -/
noncomputable def VI31 (w : ℝ) : ℝ :=
  if w ≤ P.wbar then P.vlow + (P.Vbar - P.vlow) / P.wbar * w else P.Vbar

/-- The suspension-state value function (32), p. 24: the line from `v̲` at `0` to `V̄ − K` at
`w̄`, constant `V̄ − K` for `w ≥ w̄`. (Both branches give `V̄ − K` at `w = w̄`.) -/
noncomputable def V032 (w : ℝ) : ℝ :=
  if w ≤ P.wbar then P.vlow + (P.Vbar - P.vlow - P.K) / P.wbar * w else P.Vbar - P.K

end Params

end SuspensionContract.HighCostC2


