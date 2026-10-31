-- Prove2me | Definitions.Def_DebtDoubleMarg_Model
-- name    : DebtDoubleMarg_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:40:01.582852+00:00
-- url     : https://prove2.me/theorems/3e2e813b-aafa-44fa-9cae-a30833444bf7
-- title:
--   The lender–firm investment model without bankruptcy: payoffs $\tilde J_F$, $J_F$, $J_D$, coupon schemes, $V_F$, $V_D$, $\rho^{NBO}$, $\rho^{imm}$
-- statement:
--   A monopolist can install capacity $I\ge0$ in a market with inverse demand $p=x(t)(1-\eta Q)$, where the demand level $x$ is the geometric Brownian motion $x^X$ started at the investment level $X>0$. The investment outlay $\delta I$ is borrowed from a lender, who receives a perpetual coupon $\rho\delta I$. The firm commits never to default.
--
--   1. **Parameters and standing assumptions.** $\mu,\sigma,r,\delta,\eta$ with $\eta>0$, $r>\mu$, $\delta>0$, $\sigma>0$, $r>0$.
--   2. **Profit flow** $\pi(x,I;\rho)=\sup_{0\le Q\le I}x(1-\eta Q)Q-\rho\delta I$.
--   3. **Firm's NPV** for a finite coupon $\rho$:
--   $$\tilde J_F(X,\rho,I)=\mathbb E\Big[\int_0^\infty e^{-rt}\pi\big(x^X(t),I;\rho\big)\,dt\Big].$$
--   4. **Optimal capacity** $I^*(X,\rho)$, a maximizer of $\tilde J_F(X,\rho,\cdot)$ over $I\ge0$, and the **firm's value** $J_F(X,\rho)=\tilde J_F(X,\rho,I^*(X,\rho))$.
--   5. **Lender's NPV** $J_D(X,\rho)=\int_0^\infty\rho\delta I^*(X,\rho)e^{-rt}\,dt-\delta I^*(X,\rho)$.
--   6. **Coupon schemes** $\rho:\mathbb R\to[0,\infty]$ (finite values nonnegative at every $X>0$); $\rho(X)=\infty$ means financing is refused, and then $J_F(X,\infty)=J_D(X,\infty)=0$.
--   7. **Timing payoffs** for a threshold $X_F$ and initial level $x_0$:
--   $$V_F(x_0;\rho,X_F)=\begin{cases}\mathbb E[e^{-r\tilde\tau(X_F;x_0)}]\,J_F(X_F,\rho(X_F)) & x_0<X_F,\\ J_F(x_0,\rho(x_0)) & \text{otherwise},\end{cases}$$
--   and $V_D$ in the same way with $J_D$. A threshold $X_F\ge0$ is **firm-optimal at $x_0$ under $\rho$** if it maximizes $V_F(x_0;\rho,\cdot)$ over all thresholds $X'_F\ge0$.
--   8. **The scheme (6)**: with $X_F^*=\frac{\beta_1+1}{\beta_1-1}\delta(r-\mu)$,
--   $$\rho^{NBO}(X)=\begin{cases}\dfrac{r(X+\delta(r-\mu))}{2\delta(r-\mu)} & X\ge X_F^*,\\ \infty & \text{otherwise},\end{cases}$$
--   and the **immediate-investment coupon** $\rho^{imm}(X)=\dfrac{r(X+\delta(r-\mu))}{2\delta(r-\mu)}$ for every $X$.
--
--   Items 2 to 7 are the paper's objects (1), (2), (3), (4), $V_F$ and $V_D$ in the scenario of §3.1, where the bankruptcy time is $\tau_B=\infty$ and the bankruptcy cost plays no role. $\rho^{NBO}$, $X_F^*$ and $\rho^{imm}$ are transcribed because the theorems name them; every payoff is defined by its expectation or optimization problem, never by a closed form.
--
--   **Formalization Note** The supremum over the output $Q$ is kept as printed. $I^*$ is a chosen maximizer (with value $0$ if none exists); existence and uniqueness are milestones. The expectation $\mathbb E_0$ of (3) is dropped because its integrand is deterministic. The firm's timing strategies are thresholds (stopping region $[X_F,\infty)$, p.6 and endnote 6). Values of a scheme at $X\le0$ are never used.
-- source:
--   Huberts, Wen, Dawid, Huisman, Kort, Double Marginalization Because of External Financing: Capacity Investment Under Uncertainty, Management Science (2025), doi:10.1287/mnsc.2023.01152, §2.1–2.4 pp.4–6 ((1), (2), V_F, (3), (4), V_D), §3.1 p.7 ((6)), (9) p.10 (ρ^imm), endnote 8 p.16

import Mathlib
import Definitions.Def_DebtDoubleMarg_GeometricBM

open MeasureTheory
open scoped NNReal ENNReal

namespace DebtDoubleMarg

/-- **Model parameters**: drift `µ` and volatility `σ` of the demand level, risk-free rate `r`,
unit investment cost `δ`, price sensitivity `η`.

Huberts et al., *Double Marginalization Because of External Financing: Capacity Investment
Under Uncertainty*, Management Science (2025), doi:10.1287/mnsc.2023.01152, §2.1, pp.4–5. -/
structure Params where
  /-- drift of the demand level -/
  μ : ℝ
  /-- volatility of the demand level -/
  σ : ℝ
  /-- risk-free discount rate -/
  r : ℝ
  /-- unit investment cost (total outlay `δI`) -/
  δ : ℝ
  /-- price sensitivity of the inverse demand `p = x(1 − ηQ)` -/
  η : ℝ

/-- **Standing assumptions**: `η > 0` (p.4), `r > µ` (p.5, "the usual assumption"), `δ > 0`
(the unit investment cost, p.4), and `σ > 0`, `r > 0`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, §2.1, pp.4–5.

**Formalization Note** `σ > 0` and `r > 0` are not printed. `r > 0` is needed for the coupon
stream `∫₀^∞ ρδI e^{−rt} dt` to be finite, and `σ ≠ 0` for the quadratic defining `β₁` to have
two roots; `σ > 0` is the volatility convention (`−σ` gives the same law). `µ` may be negative. -/
def Params.Standing (p : Params) : Prop :=
  0 < p.η ∧ p.μ < p.r ∧ 0 < p.δ ∧ 0 < p.σ ∧ 0 < p.r

/-- **Instantaneous profit after investment**
`π(x, I; ρ) = sup_{0 ≤ Q ≤ I} x(1 − ηQ)Q − ρδI`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, §2.3, p.5.

**Formalization Note** The supremum over the output `Q ∈ [0, I]` is kept as printed (a real
`sSup` of the image of a compact interval, so a genuine maximum for `I ≥ 0`); the paper's
replacement `Q = I` is a consequence, not part of the definition. -/
noncomputable def profitFlow (p : Params) (x I ρ : ℝ) : ℝ :=
  sSup ((fun Q : ℝ => x * (1 - p.η * Q) * Q) '' Set.Icc 0 I) - ρ * p.δ * I

/-- **The firm's net present value without bankruptcy**
`J̃_F(X, ρ, I) = E₀[∫₀^∞ e^{−rt} π(x(t), I; ρ) dt | x(0) = X]`,
for a finite coupon rate `ρ`, investment level `X` and capacity `I`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, (1), p.5, with the
bankruptcy time `τ_B = ∞` (§3.1, p.7: "the firm is able to commit to paying coupons perpetually
after investment").

**Formalization Note** The inner integral is the Bochner integral over `t ∈ (0, ∞)` along the
path `x^X(·, ω) = gbm µ σ W X`, the outer one the expectation under `P`. -/
noncomputable def firmNPV (p : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (X ρ I : ℝ) : ℝ :=
  ∫ ω, (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(p.r * t)) * profitFlow p (gbm p.μ p.σ W X t.toNNReal ω) I ρ) ∂P

/-- **`I` is an optimal capacity** at investment level `X` and coupon `ρ`: `I ≥ 0` and `I`
maximizes `J̃_F(X, ρ, ·)` over `[0, ∞)`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, §2.3, p.5: "the firm's
optimal capacity size follows from arg sup_{I≥0} J̃F(X, ρ(X), I)". -/
def IsOptimalSize (p : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (X ρ I : ℝ) : Prop :=
  0 ≤ I ∧ ∀ I' : ℝ, 0 ≤ I' → firmNPV p P W X ρ I' ≤ firmNPV p P W X ρ I

/-- **The firm's optimal capacity** `I*(X, ρ)`: a maximizer of `J̃_F(X, ρ, ·)` over `I ≥ 0`
(chosen when one exists; `0` otherwise).

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, §2.3, p.5: "The scale
of investment that follows from the solution to the optimization problem is denoted by
I∗(X, ρ(X))".

**Formalization Note** Existence and uniqueness of the maximizer (for `X > 0`, `ρ > 0`) are the
milestone `firm_optimal_size`; the fallback value `0` is never reached there. -/
noncomputable def optSize (p : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (X ρ : ℝ) : ℝ := by
  classical
  exact if h : ∃ I, IsOptimalSize p P W X ρ I then h.choose else 0

/-- **The firm's value at investment** `J_F(X, ρ) = J̃_F(X, ρ, I*(X, ρ))`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, §2.3, p.5. -/
noncomputable def firmValue (p : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (X ρ : ℝ) : ℝ :=
  firmNPV p P W X ρ (optSize p P W X ρ)

/-- **The lender's net present value without bankruptcy**
`J_D(X, ρ) = ∫₀^∞ ρδI*(X, ρ) e^{−rt} dt − δI*(X, ρ)`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, (3), p.6, with the
bankruptcy time `τ_B = ∞`: the post-bankruptcy term of (3) is absent, so the bankruptcy cost `α`
plays no role.

**Formalization Note** The integrand of (3) is deterministic once `X` and `ρ` are fixed, so the
expectation `E₀` of (3) is dropped (it is the integral of a constant against a probability
measure). -/
noncomputable def lenderValue (p : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (X ρ : ℝ) : ℝ :=
  (∫ t in Set.Ioi (0 : ℝ), ρ * p.δ * optSize p P W X ρ * Real.exp (-(p.r * t)))
    - p.δ * optSize p P W X ρ

/-- **Coupon scheme**: `ρ : ℝ → [0, ∞]`, the coupon rate offered if the firm invests at demand
level `X`; `ρ(X) = ∞` (`⊤`) means that financing is refused.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, §2.2, p.5 ("the lender
offers a scheme ρ(X) determining the coupon rate if the firm invests at a demand level X>0"),
§2.3, p.6 ("e.g., ρ(X) = ∞"), endnote 8, p.16.

**Formalization Note** Only levels `X > 0` are constrained (demand stays positive); values at
`X ≤ 0` are never used. -/
def IsCouponScheme (ρ : ℝ → WithTop ℝ) : Prop :=
  ∀ X : ℝ, 0 < X → ∀ a : ℝ, ρ X = (a : WithTop ℝ) → 0 ≤ a

/-- **The firm's value at investment for a coupon in `[0, ∞]`**: `J_F(X, ρ)` for finite `ρ`,
and `0` for `ρ = ∞`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, p.6.

**Formalization Note** At an infinite coupon the firm cannot finance the investment, so nothing
is invested and both payoffs are `0`. -/
noncomputable def firmValueAt (p : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (X : ℝ) (c : WithTop ℝ) : ℝ :=
  WithTop.recTopCoe 0 (fun ρ : ℝ => firmValue p P W X ρ) c

/-- **The lender's value at investment for a coupon in `[0, ∞]`**: `J_D(X, ρ)` for finite `ρ`,
and `0` for `ρ = ∞`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, p.6.

**Formalization Note** As for `firmValueAt`: no financing, no investment, no cash flows. -/
noncomputable def lenderValueAt (p : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (X : ℝ) (c : WithTop ℝ) : ℝ :=
  WithTop.recTopCoe 0 (fun ρ : ℝ => lenderValue p P W X ρ) c

/-- **The firm's payoff from initial demand `x₀` under scheme `ρ` with threshold `X_F`**:
`E₀[e^{−r τ̃(X_F; x₀)}] · J_F(X_F, ρ(X_F))` if `x₀ < X_F` (wait until demand reaches `X_F`), and
`J_F(x₀, ρ(x₀))` otherwise (invest immediately).

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, (2) and `V_F`, p.6.

**Formalization Note** The firm's timing strategy is a threshold: its stopping region is
`[X_F, ∞)` (p.6 and endnote 6). On the event `τ̃ = ∞` the discount factor is `0`. -/
noncomputable def firmPayoff (p : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (ρ : ℝ → WithTop ℝ) (x0 XF : ℝ) : ℝ :=
  if x0 < XF then
    expectedPassageDiscount p.μ p.σ p.r P W XF x0 * firmValueAt p P W XF (ρ XF)
  else firmValueAt p P W x0 (ρ x0)

/-- **The lender's payoff from initial demand `x₀` under scheme `ρ` when the firm uses
threshold `X_F`**: `E₀[e^{−r τ̃(X_F; x₀)}] · J_D(X_F, ρ(X_F))` if `x₀ < X_F`, and
`J_D(x₀, ρ(x₀))` otherwise.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, `V_D` in (4), p.6. -/
noncomputable def lenderPayoff (p : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (ρ : ℝ → WithTop ℝ) (x0 XF : ℝ) : ℝ :=
  if x0 < XF then
    expectedPassageDiscount p.μ p.σ p.r P W XF x0 * lenderValueAt p P W XF (ρ XF)
  else lenderValueAt p P W x0 (ρ x0)

/-- **`X_F` is a firm-optimal threshold at `x₀` under `ρ`**: `X_F ≥ 0` and it maximizes the
firm's payoff over all thresholds `X'_F ≥ 0`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, (2), p.6
("sup_{XF≥0} E0{e^{−rτ̃(XF;x(0))} JF(XF, ρ(XF), I∗(XF, ρ(XF)))}"). -/
def IsFirmOptimal (p : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (ρ : ℝ → WithTop ℝ) (x0 XF : ℝ) : Prop :=
  0 ≤ XF ∧ ∀ XF' : ℝ, 0 ≤ XF' → firmPayoff p P W ρ x0 XF' ≤ firmPayoff p P W ρ x0 XF

/-- **The investment trigger** `X*_F = (β₁ + 1)/(β₁ − 1) · δ(r − µ)`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, (6) and Proposition 1,
p.7. Transcribed: it is named by the goal theorem. -/
noncomputable def nboTrigger (p : Params) : ℝ :=
  (beta1 p.μ p.σ p.r + 1) / (beta1 p.μ p.σ p.r - 1) * (p.δ * (p.r - p.μ))

/-- **The no-bankruptcy-option coupon scheme (6)**:
`ρ^NBO(X) = r(X + δ(r − µ)) / (2δ(r − µ))` for `X ≥ (β₁ + 1)/(β₁ − 1) · δ(r − µ)`, and `∞`
otherwise.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, Proposition 1, (6), p.7.
Transcribed: it is the strategy the goal theorem claims optimal. -/
noncomputable def nboScheme (p : Params) (X : ℝ) : WithTop ℝ :=
  if nboTrigger p ≤ X then
    ((p.r * (X + p.δ * (p.r - p.μ)) / (2 * p.δ * (p.r - p.μ)) : ℝ) : WithTop ℝ)
  else ⊤

/-- **The immediate-investment coupon** `ρ^imm(X) = r(X + δ(r − µ)) / (2δ(r − µ))`, for every
level `X`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, (9), p.10 (defined
there as `arg sup_{ρ≥0} J_D(X, ρ)`), and §3.1, p.8 ("ρNBO(X) = ρimm(X) for X ≥ X∗_F").

**Formalization Note** The closed form is transcribed; that it is the unique maximizer of
`J_D(X, ·)` on `ρ ≥ 0` for `X > δ(r − µ)` is the milestone `lender_immediate_coupon`. -/
noncomputable def immCoupon (p : Params) (X : ℝ) : ℝ :=
  p.r * (X + p.δ * (p.r - p.μ)) / (2 * p.δ * (p.r - p.μ))

end DebtDoubleMarg


