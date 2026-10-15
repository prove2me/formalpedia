-- Prove2me | Definitions.Def_SuspensionContract_ControlBand_Setting
-- name    : SuspensionContract_ControlBand_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:08.588567+00:00
-- url     : https://prove2.me/theorems/67886af8-b3a1-4dfe-adc2-e41902f1faab
-- title:
--   §2–§4, pp. 7–24 — parameters, Assumption 1, β, v̲, w̄, V̄, R̂, R̄, K̲ (33, corrected), Conditions 1–2, V_c (24), operators 𝒜_I, 𝒜_∅ (18)–(19), optimality condition (20)–(22)
-- statement:
--   This file fixes the parameters and the elementary objects of the continuous-time principal–agent model of Cao, Sun and Tian.
--
--   A principal receives revenue $R$ per arrival of a Poisson process. The base arrival rate is $\underline\mu$; an agent who exerts effort, at cost $b$ per unit of time, raises it to $\mu>\underline\mu$. The principal's cost rate while the agent works is $c\ge b$, restarting work costs a fixed switching cost $K>0$, and the principal and the agent discount at rates $r$ and $\rho$. The **standing assumptions** are
--   $$0\le\underline\mu<\mu,\qquad 0<b\le c,\qquad K>0,\qquad 0<r\le\rho,\qquad R\Delta\mu>c\ \ (\text{Assumption 1}),$$
--   with $\Delta\mu=\mu-\underline\mu$. The derived constants are $\beta=b/\Delta\mu$, $\bar w=\beta\mu/\rho$ (9), $\underline v=\underline\mu R/r$ (8), $\bar V=(R\mu-c-(\rho-r)\bar w)/r$ (10), the function $\bar V(w)=(R\mu-c-(\rho-r)w)/r$ (27),
--   $$\hat R=\Big[\frac cb+\frac{(\rho-r)\mu}{\Delta\mu(\rho-r-\mu)}\cdot\frac{\rho-\mu}{\rho}\Big]\beta\ \ (28),\qquad \bar R=\Big[\frac cb+\frac{(\rho-r)\mu}{\Delta\mu(\rho-r-\mu)}\Big]\beta\ \ (34).$$
--   **Condition 1** is $\mu\ge\rho-r$ or $R<\hat R$; **Condition 2** is $\mu<\rho-r$ and $R\ge\hat R$. The threshold
--   $$\underline K=\frac1r\Big\{R\Delta\mu-c-\beta\mu-\frac{\mu\rho}{\rho-r-\mu}\Big[(R\Delta\mu-c)\frac{\rho-r-\mu}{\mu(\rho-r)}-\frac{\rho-\mu}{\rho}\beta\Big]^{1-r/\rho}\bar w^{r/\rho}\Big\}\mathbb 1_{R\in[\hat R,\bar R]}$$
--   is (33) with a printed slip corrected (see below). The suspension-state functions are $V_c(w)=\underline v+w+c\,w^{r/\rho}$ (24). For $f:\mathbb R_+\to\mathbb R$ the operators (18)–(19) are
--   $$(\mathcal A_I f)(w)=(\mu+r)f(w)-\mu f(w+\beta)+\rho(\bar w-w)f'(w)-(\mu R-c)+(\rho-r)w,$$
--   $$(\mathcal A_\emptyset f)(w)=rf(w)-\rho wf'(w)+(\rho-r)w-R\underline\mu,$$
--   where $f'(w)$ is the left derivative (the paper's convention, p. 15). A pair $(V_I,V_\emptyset)$ satisfies the **optimality condition (20)–(22)** if $(\mathcal A_IV_I)(w)\ge0$ and $(\mathcal A_\emptyset V_\emptyset)(w)\ge0$, $0\le V_I(w)-V_\emptyset(w)\le K$ for all $w\ge 0$, and $V_I(0)\ge\underline v$, $V_\emptyset(0)\ge\underline v$.
--
--   These objects are shared by every statement of the mission; Theorem 1 of the paper turns any pair satisfying (20)–(22) into an upper bound on the principal's utility.
--
--   **Formalization Note.** $\underline\mu\ge0$ and $b>0$ are disclosed additions to the standing assumptions ($\underline\mu$ is a rate, and $\bar w$ is divided by). Functions are `ℝ → ℝ` and every statement restricts to $w\ge0$; the left derivative is `derivWithin f (Set.Iic w) w`. Condition (20) is posed for $w>0$ only: at $w=0$ the left derivative of a function on $\mathbb R_+$ does not exist, and $V_c'(0^+)=+\infty$ for $c>0$. The paper prints the last term of the bracket in (33) as $(r/\rho)\beta$; the proof of Lemma 5 identifies $\underline K$ with (EC.69), whose bracket is $((\rho-\mu)/\rho)\beta$, and the printed form makes Lemma 5 false, so the corrected form is used. $\hat R$ and $\bar R$ take Lean's junk value at $\mu=\rho-r$ (division by zero), a case only inside Condition 1's first disjunct where neither is used.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, pp. 7–24, §2 (pp. 7–8), Assumption 1, (8)–(10), (18)–(22), (24), (27), (28), Conditions 1–2 (pp. 20–21), (33)–(34)

import Mathlib

namespace SuspensionContract.ControlBand

/-- Model parameters of Cao–Sun–Tian (§2, pp. 7–8): revenue `R` per arrival, arrival rate `μ` with
effort (the paper's µ), base arrival rate `μlow` (the paper's µ̲), effort cost rate `b`, principal's
cost rate `c`, switching cost `K`, principal's discount rate `r`, agent's discount rate `ρ`. -/
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
Assumption 1, `RΔµ > c`. (`µ̲ ≥ 0` and `b > 0` are disclosed additions.) -/
def Standing : Prop :=
  (0 ≤ P.μlow ∧ P.μlow < P.μ) ∧ (0 < P.b ∧ P.b ≤ P.c) ∧ 0 < P.K ∧ (0 < P.r ∧ P.r ≤ P.ρ) ∧
    P.c < P.R * (P.μ - P.μlow)

/-- `Δµ = µ − µ̲`. -/
noncomputable def Δμ : ℝ := P.μ - P.μlow

/-- `β = b/Δµ` (Proposition 1(ii), p. 10). -/
noncomputable def β : ℝ := P.b / P.Δμ

/-- `w̄ = βµ/ρ` (9). -/
noncomputable def wbar : ℝ := P.β * P.μ / P.ρ

/-- `v̲ = µ̲R/r` (8). -/
noncomputable def vlow : ℝ := P.μlow * P.R / P.r

/-- `V̄ = (Rµ − c − (ρ − r)w̄)/r` (10). -/
noncomputable def Vbar : ℝ := (P.R * P.μ - P.c - (P.ρ - P.r) * P.wbar) / P.r

/-- `V̄(w) = (Rµ − c − (ρ − r)w)/r` (27). -/
noncomputable def VbarFn (w : ℝ) : ℝ := (P.R * P.μ - P.c - (P.ρ - P.r) * w) / P.r

/-- `R̂ = [c/b + (ρ − r)µ/(Δµ(ρ − r − µ)) · (ρ − µ)/ρ] β` (28). Its denominator vanishes only when
`µ = ρ − r`, inside Condition 1's first disjunct, where Lean's `x / 0 = 0` gives a junk value that
no statement uses. -/
noncomputable def Rhat : ℝ :=
  (P.c / P.b + (P.ρ - P.r) * P.μ / (P.Δμ * (P.ρ - P.r - P.μ)) * ((P.ρ - P.μ) / P.ρ)) * P.β

/-- `R̄ = [c/b + (ρ − r)µ/(Δµ(ρ − r − µ))] β` (34). -/
noncomputable def Rbar : ℝ :=
  (P.c / P.b + (P.ρ - P.r) * P.μ / (P.Δμ * (P.ρ - P.r - P.μ))) * P.β

/-- Condition 1 (28): `µ ≥ ρ − r` or `R < R̂`. -/
def Condition1 : Prop := P.ρ - P.r ≤ P.μ ∨ P.R < P.Rhat

/-- Condition 2 (p. 21): `µ < ρ − r` and `R ≥ R̂`. -/
def Condition2 : Prop := P.μ < P.ρ - P.r ∧ P.Rhat ≤ P.R

/-- The threshold `K̲` of (33), p. 24, **with the printed slip corrected**: the bracket's last term
is `((ρ − µ)/ρ)β`, not the printed `(r/ρ)β` (it must equal the proof's (EC.69)). The indicator
`𝟙_{R ∈ [R̂, R̄]}` is kept. -/
noncomputable def Klow : ℝ :=
  if P.Rhat ≤ P.R ∧ P.R ≤ P.Rbar then
    (1 / P.r) * (P.R * P.Δμ - P.c - P.β * P.μ
      - (P.μ * P.ρ / (P.ρ - P.r - P.μ))
        * ((P.R * P.Δμ - P.c) * (P.ρ - P.r - P.μ) / (P.μ * (P.ρ - P.r))
            - ((P.ρ - P.μ) / P.ρ) * P.β) ^ (1 - P.r / P.ρ)
        * P.wbar ^ (P.r / P.ρ))
  else 0

/-- The suspension-state solutions `V_c(w) = v̲ + w + c·w^{r/ρ}` (24). -/
noncomputable def Vc (c w : ℝ) : ℝ := P.vlow + w + c * w ^ (P.r / P.ρ)

/-- The operator `𝒜_I` of (18); `f′(w)` is the left derivative (p. 15). -/
noncomputable def AI (f : ℝ → ℝ) (w : ℝ) : ℝ :=
  (P.μ + P.r) * f w - P.μ * f (w + P.β) + P.ρ * (P.wbar - w) * derivWithin f (Set.Iic w) w
    - (P.μ * P.R - P.c) + (P.ρ - P.r) * w

/-- The operator `𝒜_∅` of (19); `f′(w)` is the left derivative (p. 15). -/
noncomputable def A0 (f : ℝ → ℝ) (w : ℝ) : ℝ :=
  P.r * f w - P.ρ * w * derivWithin f (Set.Iic w) w + (P.ρ - P.r) * w - P.R * P.μlow

/-- The optimality condition (20)–(22) of Theorem 1, p. 16, with (20) posed for `w > 0`. -/
def OptCond (VI V0 : ℝ → ℝ) : Prop :=
  (∀ w, 0 < w → 0 ≤ P.AI VI w ∧ 0 ≤ P.A0 V0 w) ∧
    (∀ w, 0 ≤ w → 0 ≤ VI w - V0 w ∧ VI w - V0 w ≤ P.K) ∧ P.vlow ≤ VI 0 ∧ P.vlow ≤ V0 0

end Params

end SuspensionContract.ControlBand


