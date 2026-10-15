-- Prove2me | Definitions.Def_SuspensionContract_AlwaysWork_Setting
-- name    : SuspensionContract_AlwaysWork_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:53.672141+00:00
-- url     : https://prove2.me/theorems/579d1c2e-2a60-4a35-bae8-a9ca09b347de
-- title:
--   §2–§4.2, pp. 7–24 — parameters, Assumption 1, β, v̲, w̄, V̄, R̂, R̄, K̄₂, K̲ (33, corrected), Conditions 1–2, V_c (24), 𝒜_I, 𝒜_∅ (18)–(19) and the optimality condition (20)–(22)
-- statement:
--   This file fixes the deterministic data of the continuous-time principal–agent model of Cao, Sun and Tian with a switching cost.
--
--   **Parameters.** A principal faces Poisson arrivals, each worth revenue $R$. The base arrival rate is $\underline\mu$; an agent who exerts effort, at cost $b$ per unit time, raises it to $\mu$. The principal's cost rate while the agent works is $c$, restarting work costs a fixed $K$, and the principal and agent discount at rates $r$ and $\rho$. The **standing assumptions** are
--   $$0\le\underline\mu<\mu,\qquad 0<b\le c,\qquad K>0,\qquad 0<r\le\rho,\qquad R\Delta\mu>c\ \text{(Assumption 1)},$$
--   where $\Delta\mu=\mu-\underline\mu$.
--
--   **Derived constants.**
--   $$\beta=\frac{b}{\Delta\mu},\quad \bar w=\frac{\beta\mu}{\rho}\ (9),\quad \underline v=\frac{\underline\mu R}{r}\ (8),\quad \bar V=\frac{R\mu-c-(\rho-r)\bar w}{r}\ (10),\quad \bar V(w)=\frac{R\mu-c-(\rho-r)w}{r}\ (27),$$
--   $$\hat R=\Big[\frac cb+\frac{(\rho-r)\mu}{\Delta\mu(\rho-r-\mu)}\cdot\frac{\rho-\mu}{\rho}\Big]\beta\ (28),\qquad \bar R=\Big[\frac cb+\frac{(\rho-r)\mu}{\Delta\mu(\rho-r-\mu)}\Big]\beta\ (34),\qquad \bar K_2=\bar V-\underline v-\bar w,$$
--   and the threshold
--   $$\underline K=\frac1r\Big\{R\Delta\mu-c-\beta\mu-\frac{\mu\rho}{\rho-r-\mu}\Big[(R\Delta\mu-c)\frac{\rho-r-\mu}{\mu(\rho-r)}-\frac{\rho-\mu}{\rho}\beta\Big]^{1-r/\rho}\bar w^{r/\rho}\Big\}\mathbb 1_{R\in[\hat R,\bar R]}.$$
--
--   **Condition 1** is "$\mu\ge\rho-r$ or $R<\hat R$"; **Condition 2** is "$\mu<\rho-r$ and $R\ge\hat R$".
--
--   **Suspension-state solutions.** For a constant $c$, $V_c(w)=\underline v+w+c\,w^{r/\rho}$ (24).
--
--   **Operators.** For $f:\mathbb R_+\to\mathbb R$, with $f'(w)$ the left derivative,
--   $$(\mathcal A_I f)(w)=(\mu+r)f(w)-\mu f(w+\beta)+\rho(\bar w-w)f'(w)-(\mu R-c)+(\rho-r)w\quad(18),$$
--   $$(\mathcal A_\emptyset f)(w)=rf(w)-\rho wf'(w)+(\rho-r)w-R\underline\mu\quad(19).$$
--
--   **Optimality condition.** A pair $(V_I,V_\emptyset)$ satisfies (20)–(22) when $(\mathcal A_IV_I)(w)\ge0$ and $(\mathcal A_\emptyset V_\emptyset)(w)\ge0$ (20), $0\le V_I(w)-V_\emptyset(w)\le K$ (21), and $V_I(0)\ge\underline v$, $V_\emptyset(0)\ge\underline v$ (22).
--
--   These objects are shared by every value-function certificate of the paper; Theorem 1 of the paper turns any pair satisfying (20)–(22) into an upper bound on the principal's utility.
--
--   **Formalization Note.** Functions are $\mathbb R\to\mathbb R$ and only their values on $w\ge0$ matter. The left derivative is `derivWithin f (Set.Iic w) w`. Condition (20) is imposed for $w>0$ only: at $w=0$ a left derivative does not exist and, for $V_c$ with $c>0$, the right derivative is $+\infty$, so the paper's (20) at $0$ is an extended-real statement. (21) is imposed for $w\ge0$. The hypotheses $\underline\mu\ge0$ and $b>0$ are read off the model (a rate, a cost rate) and are added explicitly. **$\underline K$ corrects a misprint**: the paper prints the term $\frac r\rho\beta$ inside the bracket of (33); its proof of Lemma 5 identifies $\underline K$ with $\check K_2$ of (EC.69), which gives $\frac{\rho-\mu}{\rho}\beta$, and with the printed term Lemma 5 is false (e.g. $r=0.2,\rho=1.2,b=c=1,R=5,\mu=0.9,\underline\mu=0.1$: corrected $\underline K\approx7.2533$, printed $\approx-0.069$). With the correction the bracket is nonnegative exactly when $R\ge\hat R$. $\hat R$ and $\bar R$ use Lean's $x/0=0$ when $\rho-r-\mu=0$, which happens only under Condition 1. Powers $w^{r/\rho}$ are `Real.rpow`.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, pp. 7–8 (model, Assumption 1), pp. 10–12 (8)–(10), p. 15 (18)–(19), p. 16 Theorem 1 (20)–(22), p. 19 (24), (27), pp. 20–21 Conditions 1–2 (28), p. 23 (K2), p. 24 (33)–(34)

import Mathlib

namespace SuspensionContract.AlwaysWork

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

/-- `V̄(w) = (Rµ − c − (ρ − r)w)/r` (27). -/
noncomputable def VbarFn (w : ℝ) : ℝ := (P.R * P.μ - P.c - (P.ρ - P.r) * w) / P.r

/-- `R̂ = [c/b + (ρ − r)µ/(Δµ(ρ − r − µ)) · (ρ − µ)/ρ] β` (28). When `ρ − r − µ = 0` Lean's
`x / 0 = 0` gives a junk value; this only happens inside Condition 1's first disjunct. -/
noncomputable def Rhat : ℝ :=
  (P.c / P.b + (P.ρ - P.r) * P.μ / (P.Δμ * (P.ρ - P.r - P.μ)) * ((P.ρ - P.μ) / P.ρ)) * P.β

/-- `R̄ = [c/b + (ρ − r)µ/(Δµ(ρ − r − µ))] β` (34). -/
noncomputable def Rbar : ℝ :=
  (P.c / P.b + (P.ρ - P.r) * P.μ / (P.Δμ * (P.ρ - P.r - P.μ))) * P.β

/-- `K̄₂ = V̄ − v̲ − w̄` (K2). -/
noncomputable def Kbar2 : ℝ := P.Vbar - P.vlow - P.wbar

/-- The threshold `K̲(R)` of (33), p. 24, **with the printed term `(r/ρ)β` corrected to
`((ρ − µ)/ρ)β`** (the proof of Lemma 5 identifies `K̲` with `Ǩ₂` of (EC.69), which gives the
corrected bracket):
`K̲ = (1/r){RΔµ − c − βµ − (µρ/(ρ − r − µ))[(RΔµ − c)(ρ − r − µ)/(µ(ρ − r)) − ((ρ − µ)/ρ)β]^{1−r/ρ} w̄^{r/ρ}} 𝟙_{R ∈ [R̂, R̄]}`.
Powers are `Real.rpow`; the bracket is nonnegative exactly when `R ≥ R̂`. -/
noncomputable def Klow : ℝ :=
  if P.Rhat ≤ P.R ∧ P.R ≤ P.Rbar then
    (1 / P.r) * (P.R * P.Δμ - P.c - P.β * P.μ
      - P.μ * P.ρ / (P.ρ - P.r - P.μ)
        * ((P.R * P.Δμ - P.c) * (P.ρ - P.r - P.μ) / (P.μ * (P.ρ - P.r))
            - (P.ρ - P.μ) / P.ρ * P.β) ^ (1 - P.r / P.ρ)
        * P.wbar ^ (P.r / P.ρ))
  else 0

/-- Condition 1 (28): `µ ≥ ρ − r` or `R < R̂`. -/
def Condition1 : Prop := P.ρ - P.r ≤ P.μ ∨ P.R < P.Rhat

/-- Condition 2 (p. 21): `µ < ρ − r` and `R ≥ R̂`. -/
def Condition2 : Prop := P.μ < P.ρ - P.r ∧ P.Rhat ≤ P.R

/-- The suspension-state solutions `V_c(w) = v̲ + w + c·w^{r/ρ}` (24), with `Real.rpow`. -/
noncomputable def Vc (c w : ℝ) : ℝ := P.vlow + w + c * w ^ (P.r / P.ρ)

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

end Params

end SuspensionContract.AlwaysWork


