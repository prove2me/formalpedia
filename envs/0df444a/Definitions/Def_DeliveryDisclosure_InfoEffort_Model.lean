-- Prove2me | Definitions.Def_DeliveryDisclosure_InfoEffort_Model
-- name    : DeliveryDisclosure_InfoEffort_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:38.729632+00:00
-- url     : https://prove2.me/theorems/b0762991-e1f8-44d9-a3a0-c96db7141c77
-- title:
--   §3, pp. 5–10, and p. OA-7 — logit demand with M/M/1 delivery-time conformance, profit (11), feasible plans, optimal profit Π*(ϕ), the gap h(ϕ) and condition (23)
-- statement:
--   The model of Leng, Becerril-Arreola, Parlar and Ferguson. A firm serves consumers at service rate $\mu$. It quotes a promised delivery time $t$, sets a price $p$, and chooses an effort $\phi\in[0,1]$ toward the quality of the information it discloses about its delivery-time conformance.
--
--   **Parameters.** Market size $\Lambda$, base value $\alpha$, sensitivity $\beta_r$ to the conformance score and $\beta_t$ to the promised delivery time, score scale $\rho$, deterministic outside utility $V_e$, valuation scale $\omega_Y$, service rate $\mu$, unit acquisition cost $c$ and unit effort cost $b$, all real numbers.
--
--   **Standing assumptions.** $\Lambda,\beta_r,\beta_t,\rho,\omega_Y,b>0$, $c\ge 0$, and the capacity condition (16) for every effort level:
--   $$\mu \;\ge\; \bar S(\phi)\,\Lambda+\frac{\beta_t}{\beta_r\rho}\,e \qquad\text{for all }\phi\in[0,1].$$
--
--   **Utility and demand.** The utility scale at effort $\phi$ is $\omega_\theta(\phi)=\sqrt{\beta_r^2(1-\phi^2)+\omega_Y^2}$ (eq. (6)). When the demand rate is $l$, the M/M/1 queue delivers within $t$ with probability $q=1-e^{-(\mu-l)t}$ (eq. (1)), and the deterministic utility is
--   $$V(p,t,l)=\alpha-p+\beta_r\rho\bigl(1-e^{-(\mu-l)t}\bigr)-\beta_t t \qquad\text{(eq. (4))}.$$
--   The demand rate $\lambda(p,t,\phi)$ is the solution $l\in[0,\Lambda]$ of the logit fixed point (eqs. (8)–(9))
--   $$l=\frac{\Lambda}{1+\exp[-(V(p,t,l)-V_e)/\omega_\theta(\phi)]},$$
--   taken as the supremum of the $l\in[0,\Lambda]$ with $l\le$ the right-hand side. The upper bound of $V$ is $\bar V=\alpha-c+\beta_r\rho$ and the maximum share is $\bar S(\phi)=1/(1+\exp[-(\bar V-V_e)/\omega_\theta(\phi)])$ (eq. (10)).
--
--   **The firm.** The profit is $\Pi(p,t,\phi)=\lambda(p,t,\phi)(p-b\phi-c)$ (eq. (11)). A plan $(p,t)$ is feasible at $\phi$ when $p\ge c$, $t\ge 0$ and $(\mu-\lambda)t\ge 1$. A plan is optimal when it is feasible and earns at least as much as every feasible plan. The optimal profit $\Pi^*(\phi)$ is the supremum of the profit over all feasible plans; $(p^*(\phi),t^*(\phi))$ is an optimal plan (chosen when one exists), $\lambda^*(\phi)$ the demand there and $V^*(\phi)$ the deterministic utility there.
--
--   **The gap and condition (23).** From the proof of Theorem 1 (p. OA-7),
--   $$h(\phi)=\frac{b\,\omega_\theta(\phi)}{\beta_r^2\phi}-\frac{V^*(\phi)-V_e}{\omega_\theta(\phi)},$$
--   the difference of the two sides of Lemma 2's condition (19), divided by $\omega_\theta$. Condition (23) is $b\omega_Y^2/\beta_r^2\ge V_1-V_e$, where $V_1=V^*(1)$ is the deterministic utility at the optimal plan under full effort.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** The paper derives the logit share (8) from a claim that a Gumbel shock plus a $C(\phi)$-distributed inference error is again Gumbel with scale $\omega_\theta$; that claim holds only when $\omega_Y=\phi\beta_r$. Every result from (8) on uses only the logit formula, so the logit demand with scale (6) is taken as the primitive and the error distribution is not formalized. Added relative to the page: positivity of $\Lambda,\beta_r,\beta_t,\rho,\omega_Y$ (the page writes $\beta_r,\beta_t\ge 0$ but divides by them) and $c\ge0$; the shortest delivery time is $\underline t=0$; condition (16) is required for every $\phi\in[0,1]$, since $\bar S$ depends on $\phi$. The effort range is the closed interval $[0,1]$ (p. 5); the paper's $0^+$ and $1^-$ are its endpoints. The real-valued supremum defining $\lambda$ is over a nonempty set bounded by $\Lambda$, and the theorem `demand_wellposed` shows it is the unique fixed point; $\Pi^*$ is a supremum over all feasible plans, which Lemma 1 shows is attained. `optPlan` falls back to $(c,0)$ when no optimal plan exists, which never happens under the standing assumptions. $h$ divides by $\phi$ and is used only for $\phi\in(0,1]$.
-- source:
--   Leng, Becerril-Arreola, Parlar & Ferguson, Disclosing Delivery Performance Information (authors' preprint, April 2nd, 2023), pp. 5–10, §3, eqs. (1), (4), (6), (8)–(11), condition (16) p. 11; h(ϕ) from the proof of Theorem 1, p. OA-7; condition (23), p. 15

import Mathlib

namespace DeliveryDisclosure.InfoEffort

/-- The primitive data of the delivery-disclosure model of Leng, Becerril-Arreola, Parlar and
Ferguson (§3, pp. 5–10): market size `Λ`, base value `α`, sensitivity `βr` to the conformance
score and `βt` to the promised delivery time, score scale `ρ`, deterministic outside utility `Ve`,
valuation scale `ωY`, service rate `μ`, unit acquisition cost `c` and unit effort cost `b`. -/
structure Params where
  Λ : ℝ
  α : ℝ
  βr : ℝ
  βt : ℝ
  ρ : ℝ
  Ve : ℝ
  ωY : ℝ
  μ : ℝ
  c : ℝ
  b : ℝ

/-- The scale of the consumer's utility shock at information-quality effort `ϕ`, eq. (6), p. 9:
`ω_θ = √(β_r²(1 − ϕ²) + ω_Y²)`. -/
noncomputable def ωθ (P : Params) (ϕ : ℝ) : ℝ :=
  Real.sqrt (P.βr ^ 2 * (1 - ϕ ^ 2) + P.ωY ^ 2)

/-- The deterministic component of utility, eq. (4), p. 8, `V = α − p + β_r ρ q − β_t t`, with the
M/M/1 delivery-time conformance `q = 1 − exp(−(μ − l)t)` of eq. (1), p. 5, evaluated at the demand
rate `l`. -/
noncomputable def Vdet (P : Params) (p t l : ℝ) : ℝ :=
  P.α - p + P.βr * P.ρ * (1 - Real.exp (-(P.μ - l) * t)) - P.βt * t

/-- The upper bound `V̄ = α − c + β_r ρ − β_t t̲` of `V` (p. 9), with shortest delivery time
`t̲ = 0`. -/
def Vbar (P : Params) : ℝ :=
  P.α - P.c + P.βr * P.ρ

/-- The maximum market share `S̄ = 1/(1 + exp[−(V̄ − V_e)/ω_θ])` at effort `ϕ`, eq. (10), p. 10. -/
noncomputable def Sbar (P : Params) (ϕ : ℝ) : ℝ :=
  Real.sigmoid ((Vbar P - P.Ve) / ωθ P ϕ)

/-- The demand rate `λ(p, t, ϕ)`, eqs. (8)–(9), p. 10: the solution `l ∈ [0, Λ]` of the fixed-point
equation `l = Λ / (1 + exp[−(V − V_e)/ω_θ])`, where `V` depends on `l` through the conformance `q`.
It is defined, without choice, as the supremum of the set of `l ∈ [0, Λ]` with
`l ≤ Λ σ((V(l) − V_e)/ω_θ)`; the theorem `demand_wellposed` shows that, for `t ≥ 0`, this is the
unique fixed point. -/
noncomputable def dem (P : Params) (p t ϕ : ℝ) : ℝ :=
  sSup {l : ℝ | l ∈ Set.Icc 0 P.Λ ∧ l ≤ P.Λ * Real.sigmoid ((Vdet P p t l - P.Ve) / ωθ P ϕ)}

/-- The firm's profit `Π(p, t, ϕ) = λ(p, t, ϕ)(p − bϕ − c)`, eq. (11), p. 10. -/
noncomputable def profit (P : Params) (p t ϕ : ℝ) : ℝ :=
  dem P p t ϕ * (p - P.b * ϕ - P.c)

/-- A plan `x = (p, t)` (price, promised delivery time) is feasible at effort `ϕ` when `p ≥ c`,
`t ≥ t̲ = 0` and `(μ − λ)t ≥ 1` (p. 5 and p. 9). -/
def Feasible (P : Params) (ϕ : ℝ) (x : ℝ × ℝ) : Prop :=
  P.c ≤ x.1 ∧ 0 ≤ x.2 ∧ 1 ≤ (P.μ - dem P x.1 x.2 ϕ) * x.2

/-- A plan is optimal at effort `ϕ` when it is feasible and no feasible plan earns more
(the first step of §4, p. 11). -/
def IsOptimal (P : Params) (ϕ : ℝ) (x : ℝ × ℝ) : Prop :=
  Feasible P ϕ x ∧ ∀ y : ℝ × ℝ, Feasible P ϕ y → profit P y.1 y.2 ϕ ≤ profit P x.1 x.2 ϕ

/-- The optimal profit `Π*(ϕ)`: the supremum of the profit over all feasible plans at effort `ϕ`. -/
noncomputable def optProfit (P : Params) (ϕ : ℝ) : ℝ :=
  sSup ((fun x : ℝ × ℝ => profit P x.1 x.2 ϕ) '' {x | Feasible P ϕ x})

open Classical in
/-- An optimal plan `(p*(ϕ), t*(ϕ))` at effort `ϕ`, if one exists (Lemma 1 makes it unique);
the default `(c, 0)` is never used under the standing assumptions. -/
noncomputable def optPlan (P : Params) (ϕ : ℝ) : ℝ × ℝ :=
  if hx : ∃ x, IsOptimal P ϕ x then hx.choose else (P.c, 0)

/-- The optimal demand rate `λ*(ϕ) = λ(p*(ϕ), t*(ϕ), ϕ)` (p. 11). -/
noncomputable def optDem (P : Params) (ϕ : ℝ) : ℝ :=
  dem P (optPlan P ϕ).1 (optPlan P ϕ).2 ϕ

/-- The deterministic utility `V` at the optimal plan for effort `ϕ`. -/
noncomputable def optV (P : Params) (ϕ : ℝ) : ℝ :=
  Vdet P (optPlan P ϕ).1 (optPlan P ϕ).2 (optDem P ϕ)

/-- The gap in Lemma 2's condition (19), from the proof of Theorem 1, p. OA-7:
`h(ϕ) = bω_θ/(β_r²ϕ) − (V − V_e)/ω_θ`, with `V` at the optimal plan. Meaningful for `ϕ > 0`. -/
noncomputable def h (P : Params) (ϕ : ℝ) : ℝ :=
  P.b * ωθ P ϕ / (P.βr ^ 2 * ϕ) - (optV P ϕ - P.Ve) / ωθ P ϕ

/-- The standing assumptions: positivity of `Λ, β_r, β_t, ρ, ω_Y, b`, `c ≥ 0`, and the capacity
condition (16), p. 11, `μ ≥ S̄Λ + (β_t/(β_r ρ)) exp(1)`, for every effort `ϕ ∈ [0, 1]`. -/
def Standing (P : Params) : Prop :=
  0 < P.Λ ∧ 0 < P.βr ∧ 0 < P.βt ∧ 0 < P.ρ ∧ 0 < P.ωY ∧ 0 ≤ P.c ∧ 0 < P.b ∧
    ∀ ϕ ∈ Set.Icc (0 : ℝ) 1, Sbar P ϕ * P.Λ + P.βt / (P.βr * P.ρ) * Real.exp 1 ≤ P.μ

/-- Condition (23), p. 15: `bω_Y²/β_r² ≥ V₁ − V_e`, with `V₁` the deterministic utility at the
optimal plan under full effort `ϕ = 1`. -/
def cond23 (P : Params) : Prop :=
  optV P 1 - P.Ve ≤ P.b * P.ωY ^ 2 / P.βr ^ 2

end DeliveryDisclosure.InfoEffort


