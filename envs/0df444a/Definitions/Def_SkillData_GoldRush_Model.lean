-- Prove2me | Definitions.Def_SkillData_GoldRush_Model
-- name    : SkillData_GoldRush_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:51.292071+00:00
-- url     : https://prove2.me/theorems/f91c2722-f2f4-4dbf-aa5b-45dc26a7d80a
-- title:
--   §2–§3, (8)–(19), (C1)–(C4), (C12), (C13), (21) — data-sales economy: variances, equations (14) and (19), seller's problem (3), equilibrium, market variables
-- statement:
--   This file sets up the data-sales economy of Huang, Xiong and Yang, in closed form.
--
--   **Parameters.** The risky asset pays $\tilde\theta\sim N(0,\tau_\theta^{-1})$; noise demand is $\tilde u\sim N(0,\tau_u^{-1})$; the seller observes $\tilde\theta+\tilde\eta$ with $\tilde\eta\sim N(0,\tau_\eta^{-1})$. Investors have CARA utility with coefficient $\gamma$; the seller has Nash-bargaining power $\beta$; a skilled investor becomes high-skilled ($Z_H$) or low-skilled ($Z_L$) with probability $\tfrac12$ each. The **standing assumptions** are
--   $$\tau_\theta>0,\quad \tau_u>0,\quad \gamma>0,\quad 0<\beta<1,\quad 0<Z_L<Z_H .$$
--   The data accuracy $\tau_\eta>0$ is kept as a separate argument.
--
--   **Skill-acquisition cost.** A cost family $C(c,i)$, with cost parameter $c>0$ and investor index $i\in[0,1)$, is admissible when, for every $c>0$, $C(c,\cdot)$ is continuous and strictly increasing on $[0,1)$ with $C(c,0)=0$ and $C(c,i)\to+\infty$ as $i\to1^-$; and, for every $i\in(0,1)$, $C(c,i)$ is strictly increasing in $c$.
--
--   **Posterior variances** (8), (10), (12). With clarity $x$ and price-signal precision $\alpha^2\tau_u$,
--   $$\operatorname{Var}(\tilde\theta\mid\tilde p,\tilde s_{k})=\frac{1}{\tau_\theta+\tau_\eta}+\Big(\frac{\tau_\eta}{\tau_\theta+\tau_\eta}\Big)^2\frac{1}{\frac{\tau_\theta\tau_\eta}{\tau_\theta+\tau_\eta}+\alpha^2\tau_u+xZ_k},\qquad k\in\{H,L\},$$
--   and $\operatorname{Var}(\tilde\theta\mid\tilde p)$ is the same expression without the $xZ_k$ term.
--
--   **Trading gain** (15): $G(x,\alpha)=\frac1\gamma\ln\Big[\sqrt{\operatorname{Var}(\tilde\theta\mid\tilde p)}\big/\big(\tfrac12\sqrt{\operatorname{Var}(\tilde\theta\mid\tilde p,\tilde s_H)}+\tfrac12\sqrt{\operatorname{Var}(\tilde\theta\mid\tilde p,\tilde s_L)}\big)\Big]$. When the data are sold "as is" ($x=\infty$), both conditional variances given a signal equal $1/(\tau_\theta+\tau_\eta)$.
--
--   **Equilibrium equations.** Equation (14) is
--   $$\gamma\alpha\big(xZ_H+\tau_u\alpha^2+\tau_\eta\big)-\tfrac12 x\lambda\tau_\eta\Big(Z_H+Z_L+\frac{xZ_L(Z_H-Z_L)}{xZ_L+\tau_u\alpha^2+\tau_\eta}\Big)=0,$$
--   which at $x=\infty$ reads $\gamma\alpha=\lambda\tau_\eta$; equation (19) is $(1-\beta)G=C(c,\lambda)$. A clarity $X\in(0,\infty]$ with $\lambda\in(0,1)$ and $\alpha>0$ is **feasible** when (14) and (19) hold. The seller's profit (3) is $\pi=\lambda q$ with data price $q=\beta G$ (16). An **equilibrium** (Definition 1, Proposition 2) is a feasible $(X,\lambda,\alpha)$ whose profit is at least the profit of every feasible tuple.
--
--   **Market variables** at a finite clarity: data price $q=\beta G$; price informativeness $1/\operatorname{Var}(\tilde\theta\mid\tilde p)$; the price coefficients $a_0=-1/D$, $a_\theta=(A+B)/D$, $a_u=a_\theta/B$ of (C1)–(C4); the cost of capital $E(\tilde\theta-\tilde p)=-a_0$ (C12); return volatility $\sigma(\tilde\theta-\tilde p)=\sqrt{(1-a_\theta)^2/\tau_\theta+a_\theta^2/\tau_\eta+a_u^2/\tau_u}$ (C13); and performance (21), $\tfrac12\big(\tfrac1{2\gamma}\ln\frac{\operatorname{Var}(\tilde\theta\mid\tilde p)}{\operatorname{Var}(\tilde\theta\mid\tilde p,\tilde s_H)}+\tfrac1{2\gamma}\ln\frac{\operatorname{Var}(\tilde\theta\mid\tilde p)}{\operatorname{Var}(\tilde\theta\mid\tilde p,\tilde s_L)}\big)$. Here $D=\frac{\lambda}{2\gamma V_H}+\frac{\lambda}{2\gamma V_L}+\frac{1-\lambda}{\gamma V_U}$ and $A,B$ are the weighted sums printed on p. 32. Finally, (C18) is the equation $\tfrac12e^{\gamma C(c,\lambda)/(1-\beta)}\big(\sqrt{1/(\frac{\gamma Z_H}{\lambda(Z_H+Z_L)\sqrt{\tau_\theta\tau_u}}+1)}+\sqrt{1/(\frac{\gamma Z_L}{\lambda(Z_H+Z_L)\sqrt{\tau_\theta\tau_u}}+1)}\big)=1$.
--
--   These objects carry every statement of the mission.
--
--   **Formalization Note.** The closed forms are the definitions; their CARA-normal derivation (Bayes' rule, market clearing, certainty equivalents) is not formalized. Clarity is a two-constructor type: a finite real $x$ or "as is". Equilibria are relational, with no choice functions. Two hypotheses are added to the page's parameter domains: $\beta>0$, since with $\beta=0$ every clarity is optimal; and $Z_L>0$, which is the paper's own condition on p. 23. "Increasing" cost is read strictly. Clarity $x=0$ is excluded from the choice set because it yields no positive root of (14). (C2) and (C3) print $\operatorname{Var}(\tilde v\mid\cdot)$, which is read as $\operatorname{Var}(\tilde\theta\mid\cdot)$.
-- source:
--   Huang, Xiong & Yang, Skill Acquisition and Data Sales, working paper (July 2019 version), pp. 7–17, 20 and 32–39 (PDF 8–18, 21, 33–40), §2, §3, Definition 1, (3), (8)–(21), (C1)–(C4), (C12), (C13), (C18)

import Mathlib

namespace SkillData.GoldRush

/-- The exogenous parameters of §2 other than the data accuracy `τη`:
prior precision `τθ` of the cash flow θ̃, precision `τu` of the noise demand ũ,
CARA coefficient `γ`, the seller's bargaining power `β`, and the two skill levels `ZH`, `ZL`. -/
structure Params where
  τθ : ℝ
  τu : ℝ
  γ : ℝ
  β : ℝ
  ZH : ℝ
  ZL : ℝ

/-- Standing assumptions of §2 (pp. 7–11): `τθ, τu ∈ (0, ∞)`, `γ > 0`, `β < 1` (p. 35),
skill uncertainty `ZL < ZH` (Δ > 0, p. 21). Added: `0 < β` and `0 < ZL` (p. 23). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.τθ ∧ 0 < P.τu ∧ 0 < P.γ ∧ 0 < P.β ∧ P.β < 1 ∧ 0 < P.ZL ∧ P.ZL < P.ZH

/-- The cost family `C c i` = C(i) at cost parameter `c` (pp. 9, 16, 18): for every `c > 0`,
`C c ·` is continuous and strictly increasing on `[0, 1)`, `C c 0 = 0`, and `C c i → +∞` as
`i → 1⁻` (the paper's `C(1) = +∞`); and `C c i` is strictly increasing in `c > 0` for
every `i ∈ (0, 1)` (`∂C/∂c > 0`). -/
def IsCostFamily (C : ℝ → ℝ → ℝ) : Prop :=
  (∀ c, 0 < c →
    ContinuousOn (C c) (Set.Ico 0 1) ∧ StrictMonoOn (C c) (Set.Ico 0 1) ∧ C c 0 = 0 ∧
    Filter.Tendsto (C c) (nhdsWithin 1 (Set.Iio 1)) Filter.atTop) ∧
  ∀ i ∈ Set.Ioo (0 : ℝ) 1, StrictMonoOn (fun c => C c i) (Set.Ioi 0)

/-- Equations (8), (10), (12): the conditional variance of θ̃ given the price and a signal
whose total precision about θ̃ + η̃ is `prec` (`prec = α²τu + x z`). -/
noncomputable def condVar (P : Params) (τη prec : ℝ) : ℝ :=
  1 / (P.τθ + τη) + (τη / (P.τθ + τη)) ^ 2 * (1 / (P.τθ * τη / (P.τθ + τη) + prec))

/-- (12): `Var(θ̃ | p̃)`. -/
noncomputable def varU (P : Params) (τη α : ℝ) : ℝ := condVar P τη (α ^ 2 * P.τu)

/-- (8): `Var(θ̃ | p̃, s̃_H)`. -/
noncomputable def varH (P : Params) (τη x α : ℝ) : ℝ := condVar P τη (α ^ 2 * P.τu + x * P.ZH)

/-- (10): `Var(θ̃ | p̃, s̃_L)`. -/
noncomputable def varL (P : Params) (τη x α : ℝ) : ℝ := condVar P τη (α ^ 2 * P.τu + x * P.ZL)

/-- (15): the trading gain `G(x, α)` at a finite clarity `x`. -/
noncomputable def gain (P : Params) (τη x α : ℝ) : ℝ :=
  1 / P.γ * Real.log (Real.sqrt (varU P τη α) /
    (1 / 2 * Real.sqrt (varH P τη x α) + 1 / 2 * Real.sqrt (varL P τη x α)))

/-- (15) at `x = ∞` (data sold "as is"): both conditional variances given a signal equal
`1/(τθ + τη)`, the `x → ∞` limit of (8) and (10). -/
noncomputable def gainAsIs (P : Params) (τη α : ℝ) : ℝ :=
  1 / P.γ * Real.log (Real.sqrt (varU P τη α) / Real.sqrt (1 / (P.τθ + τη)))

/-- Equation (14) of Proposition 1, at a finite clarity `x`. -/
def Eq14 (P : Params) (τη x lam α : ℝ) : Prop :=
  P.γ * α * (x * P.ZH + P.τu * α ^ 2 + τη)
    - 1 / 2 * x * lam * τη *
      (P.ZH + P.ZL + x * P.ZL * (P.ZH - P.ZL) / (x * P.ZL + P.τu * α ^ 2 + τη)) = 0

/-- The seller's choice of clarity: a finite `x` or "as is" (`x = ∞`). -/
inductive Clarity
  | finite (x : ℝ)
  | asIs

/-- `(X, λ, α)` solves (14) and (19) at cost parameter `c`, with `λ ∈ (0, 1)`, `α > 0` and,
for a finite clarity, `x > 0`. At `x = ∞`, (14) reads `γα = λτη` (proof of Proposition 3,
p. 36). -/
def Feasible (P : Params) (C : ℝ → ℝ → ℝ) (c τη : ℝ) : Clarity → ℝ → ℝ → Prop
  | .finite x, lam, α => 0 < x ∧ 0 < lam ∧ lam < 1 ∧ 0 < α ∧ Eq14 P τη x lam α ∧
      (1 - P.β) * gain P τη x α = C c lam
  | .asIs, lam, α => 0 < lam ∧ lam < 1 ∧ 0 < α ∧ P.γ * α = lam * τη ∧
      (1 - P.β) * gainAsIs P τη α = C c lam

/-- The seller's profit `π = λ q` (3), with `q = βG` (16). -/
noncomputable def profit (P : Params) (τη : ℝ) : Clarity → ℝ → ℝ → ℝ
  | .finite x, lam, α => lam * (P.β * gain P τη x α)
  | .asIs, lam, α => lam * (P.β * gainAsIs P τη α)

/-- Definition 1 with (14), (16), (19): an overall equilibrium (Proposition 2) at cost
parameter `c` is a feasible tuple whose profit is at least that of every feasible tuple. -/
def IsEquilibrium (P : Params) (C : ℝ → ℝ → ℝ) (c τη : ℝ) (X : Clarity) (lam α : ℝ) : Prop :=
  Feasible P C c τη X lam α ∧
  ∀ X' lam' α', Feasible P C c τη X' lam' α' → profit P τη X' lam' α' ≤ profit P τη X lam α

/-- (16): the data price `q = βG` at a finite clarity. -/
noncomputable def dataPrice (P : Params) (τη x α : ℝ) : ℝ := P.β * gain P τη x α

/-- p. 14: price informativeness `1 / Var(θ̃ | p̃)`. -/
noncomputable def priceInformativeness (P : Params) (τη α : ℝ) : ℝ := 1 / varU P τη α

/-- The denominator of (C1)–(C3). -/
noncomputable def coefD (P : Params) (τη x lam α : ℝ) : ℝ :=
  lam / (2 * P.γ * varH P τη x α) + lam / (2 * P.γ * varL P τη x α)
    + (1 - lam) / (P.γ * varU P τη α)

/-- `A` of (C1), p. 32. -/
noncomputable def coefA (P : Params) (τη x lam α : ℝ) : ℝ :=
  lam / (2 * P.γ * varH P τη x α) * (τη / (P.τθ + τη)) *
      (α ^ 2 * P.τu / (P.τθ * τη / (P.τθ + τη) + α ^ 2 * P.τu + x * P.ZH))
    + lam / (2 * P.γ * varL P τη x α) * (τη / (P.τθ + τη)) *
      (α ^ 2 * P.τu / (P.τθ * τη / (P.τθ + τη) + α ^ 2 * P.τu + x * P.ZL))
    + (1 - lam) / (P.γ * varU P τη α) * (τη / (P.τθ + τη)) *
      (α ^ 2 * P.τu / (P.τθ * τη / (P.τθ + τη) + α ^ 2 * P.τu))

/-- `B` of (C1), p. 32. -/
noncomputable def coefB (P : Params) (τη x lam α : ℝ) : ℝ :=
  lam / (2 * P.γ * varH P τη x α) * (τη / (P.τθ + τη)) *
      (x * P.ZH / (P.τθ * τη / (P.τθ + τη) + α ^ 2 * P.τu + x * P.ZH))
    + lam / (2 * P.γ * varL P τη x α) * (τη / (P.τθ + τη)) *
      (x * P.ZL / (P.τθ * τη / (P.τθ + τη) + α ^ 2 * P.τu + x * P.ZL))

/-- (C2): `a₀ = −1/D`. -/
noncomputable def a0 (P : Params) (τη x lam α : ℝ) : ℝ := -1 / coefD P τη x lam α

/-- (C3): `a_θ = (A + B)/D`. -/
noncomputable def aθ (P : Params) (τη x lam α : ℝ) : ℝ :=
  (coefA P τη x lam α + coefB P τη x lam α) / coefD P τη x lam α

/-- (C4): `a_u = B⁻¹ a_θ`. -/
noncomputable def au (P : Params) (τη x lam α : ℝ) : ℝ :=
  aθ P τη x lam α / coefB P τη x lam α

/-- (C12): the cost of capital `E(θ̃ − p̃) = −a₀`. -/
noncomputable def costOfCapital (P : Params) (τη x lam α : ℝ) : ℝ := -a0 P τη x lam α

/-- (C13): return volatility `σ(θ̃ − p̃)`. -/
noncomputable def returnVolatility (P : Params) (τη x lam α : ℝ) : ℝ :=
  Real.sqrt ((1 - aθ P τη x lam α) ^ 2 / P.τθ + aθ P τη x lam α ^ 2 / τη
    + au P τη x lam α ^ 2 / P.τu)

/-- (21): skilled investors' performance. -/
noncomputable def performance (P : Params) (τη x α : ℝ) : ℝ :=
  1 / 2 * (1 / (2 * P.γ) * Real.log (varU P τη α / varH P τη x α)
    + 1 / (2 * P.γ) * Real.log (varU P τη α / varL P τη x α))

/-- (C18), with `C = C(c, λ)`. -/
def EqC18 (P : Params) (C : ℝ → ℝ → ℝ) (c lam : ℝ) : Prop :=
  1 / 2 * Real.exp (P.γ * C c lam / (1 - P.β)) *
    (Real.sqrt (1 / (P.γ * P.ZH / (lam * (P.ZH + P.ZL) * Real.sqrt (P.τθ * P.τu)) + 1))
     + Real.sqrt (1 / (P.γ * P.ZL / (lam * (P.ZH + P.ZL) * Real.sqrt (P.τθ * P.τu)) + 1))) = 1

end SkillData.GoldRush


