-- Prove2me | Definitions.Def_BellmanDP_ContGoldMining_Process
-- name    : BellmanDP_ContGoldMining_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T16:57:41.993433+00:00
-- url     : https://prove2.me/theorems/485f39e7-82d5-46e2-9053-7cf5331d3171
-- title:
--   The continuous gold-mining process: controls, states $x(t), y(t), p(t)$, and returns $f(T)$, $f(\infty)$
-- statement:
--   This file sets up the continuous stochastic decision process of Chapter VIII of Bellman's *Dynamic Programming*. Two mines, A and B, contain amounts $x_0 \ge 0$ and $y_0 \ge 0$ of gold, and a single machine is used to mine them. There are three decisions: $A$ (mine A), $B$ (mine B) and, in the three-choice problem of § 12, a third decision $C$ that works on both mines. Decision $A$ removes gold from mine A at relative rate $r_1$ and destroys the machine at rate $q_1$; $B$ removes gold from mine B at relative rate $r_2$ and destroys the machine at rate $q_2$; $C$ removes gold from A and B at relative rates $r_3$, $r_4$ and destroys the machine at rate $q_3$.
--
--   1. A **control** is a triple $\varphi = (\varphi_1, \varphi_2, \varphi_3)$ of functions of time; $\varphi_i(t)$ is the proportion of the time near $t$ devoted to decision $i$. It is **admissible** when each $\varphi_i$ is measurable, $\varphi_i(t) \ge 0$ and $\varphi_1(t) + \varphi_2(t) + \varphi_3(t) = 1$ for all $t$ (Eq. (12.2)). A **two-choice control** (§ 7) is given by one measurable function $\varphi_1$ with $0 \le \varphi_1(t) \le 1$, and then $\varphi_2 = 1 - \varphi_1$, $\varphi_3 = 0$ (Eq. (7.3)).
--   2. With the cumulative times $\Phi_i(t) = \int_0^t \varphi_i(s)\,ds$, the gold remaining in the two mines and the survival probability of the machine are
--   $$x(t) = x_0 e^{-r_1 \Phi_1(t) - r_3 \Phi_3(t)},\qquad y(t) = y_0 e^{-r_2 \Phi_2(t) - r_4 \Phi_3(t)},\qquad p(t) = e^{-q_1\Phi_1(t) - q_2 \Phi_2(t) - q_3 \Phi_3(t)}.$$
--   3. The expected gold is mined at rate $f'(t) = p(t)\,[(\varphi_1 r_1 + \varphi_3 r_3)\,x(t) + (\varphi_2 r_2 + \varphi_3 r_4)\,y(t)]$, the expected gold mined by time $T$ is $f(T) = \int_0^T f'(t)\,dt$, and the expected total gold is $f(\infty) = \int_0^\infty f'(t)\,dt$.
--   4. A two-choice control $\varphi_1$ **follows the index rule** of Chapter VIII, Theorem 1 when, for almost every $t \ge 0$, along its own trajectory $(x(t), y(t))$:
--   $$\varphi_1(t) = 1 \text{ if } q_1 r_2 y(t) < q_2 r_1 x(t),\qquad \varphi_1(t) = 0 \text{ if } q_1 r_2 y(t) > q_2 r_1 x(t),\qquad \varphi_1(t) = \frac{r_2}{r_1 + r_2} \text{ if } q_1 r_2 y(t) = q_2 r_1 x(t).$$
--
--   These objects are shared by every theorem of the mission: the goal (Theorem 1) concerns two-choice controls, and the lemmas of §§ 13–14 and "Theorem 8" concern the three-choice problem.
--
--   **Formalization Note** The book defines the process by the differential equations (7.2) and (12.1). The functions $x, y, p$ above are their unique absolutely continuous solutions for a measurable control, so the process is defined by these closed forms and no ODE theory is needed. The rate data are a structure `Params` with fields `q₁ q₂ q₃ r₁ r₂ r₃ r₄`. Decisions are indexed `0, 1, 2` for $A, B, C$. The two-choice process uses `Params.two q₁ q₂ r₁ r₂`, in which $q_3, r_3, r_4$ are set to $0$ and never enter because $\varphi_3 = 0$. $f(\infty)$ is a lower Lebesgue integral with values in $[0, \infty]$, so it has no junk value (the integrand is nonnegative for admissible controls and nonnegative data). `Params.Positive` states that all seven rates are positive, the chapter's implicit range.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter VIII, § 7, Eqs. (7.2)-(7.3), p. 228; § 12, Eqs. (12.1)-(12.2), p. 233; Theorem 1, Eq. (2), p. 231

import Mathlib

namespace BellmanDP.ContGoldMining

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. VIII, § 7, Eq. (7.2), p. 228, and § 12, Eq. (12.1),
p. 233: the rate parameters of the continuous gold-mining process with three decisions
`A` (index `0`), `B` (index `1`), `C` (index `2`).
Decision `A` removes gold from mine A at relative rate `r₁` and stops the machine at rate `q₁`;
`B` removes gold from mine B at relative rate `r₂` and stops the machine at rate `q₂`;
`C` removes gold from A at relative rate `r₃` and from B at relative rate `r₄`, and stops the
machine at rate `q₃`. The two-choice process of § 7 is the case in which `C` is never used. -/
structure Params where
  q₁ : ℝ
  q₂ : ℝ
  q₃ : ℝ
  r₁ : ℝ
  r₂ : ℝ
  r₃ : ℝ
  r₄ : ℝ

namespace Params

/-- Failure rate of decision `i`: `(q₁, q₂, q₃)`. -/
def q (P : Params) : Fin 3 → ℝ := ![P.q₁, P.q₂, P.q₃]

/-- Rate at which decision `i` depletes mine A: `(r₁, 0, r₃)` (Eq. (12.1), first line). -/
def a (P : Params) : Fin 3 → ℝ := ![P.r₁, 0, P.r₃]

/-- Rate at which decision `i` depletes mine B: `(0, r₂, r₄)` (Eq. (12.1), second line). -/
def b (P : Params) : Fin 3 → ℝ := ![0, P.r₂, P.r₄]

/-- All rates of the three-choice process are positive (the chapter's implicit range for rates). -/
def Positive (P : Params) : Prop :=
  0 < P.q₁ ∧ 0 < P.q₂ ∧ 0 < P.q₃ ∧ 0 < P.r₁ ∧ 0 < P.r₂ ∧ 0 < P.r₃ ∧ 0 < P.r₄

/-- The two-choice process of § 7 with data `(q₁, q₂, r₁, r₂)`; the entries `q₃, r₃, r₄` are set
to `0` and are never used, because the two-choice control gives `C` weight `0`. -/
def two (q₁ q₂ r₁ r₂ : ℝ) : Params := ⟨q₁, q₂, 0, r₁, r₂, 0, 0⟩

end Params

/-- A control of the three-choice process: `φ i t` is the proportion `φ_{i+1}(t)` of time devoted
to decision `i` at time `t` (Eq. (12.1)). -/
abbrev Control := Fin 3 → ℝ → ℝ

/-- Eq. (12.2), p. 233: an admissible control is measurable with `φ_i(t) ≥ 0` and
`φ₁(t) + φ₂(t) + φ₃(t) = 1` for all `t`. -/
def Admissible (φ : Control) : Prop :=
  (∀ i, Measurable (φ i)) ∧ (∀ i t, 0 ≤ φ i t) ∧ ∀ t, ∑ i, φ i t = 1

/-- The two-choice control of § 7 determined by `φ₁`: `φ₂ = 1 − φ₁` and `φ₃ = 0`
(Eq. (7.3)). -/
def twoChoice (φ₁ : ℝ → ℝ) : Control := fun i t => ![φ₁ t, 1 - φ₁ t, 0] i

/-- Eq. (7.3), p. 228: an admissible two-choice control is a measurable `φ₁` with
`0 ≤ φ₁(t) ≤ 1` for all `t`. -/
def TwoAdmissible (φ₁ : ℝ → ℝ) : Prop :=
  Measurable φ₁ ∧ ∀ t, φ₁ t ∈ Set.Icc (0 : ℝ) 1

/-- Cumulative time `Φ_i(t) = ∫₀ᵗ φ_i(s) ds` devoted to decision `i` up to time `t`. -/
noncomputable def cumTime (φ : Control) (i : Fin 3) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, φ i s

/-- Gold remaining in mine A at time `t`, `x(t) = x₀ exp(−r₁Φ₁(t) − r₃Φ₃(t))`: the solution of
`dx/dt = −[φ₁ r₁ + φ₃ r₃] x`, `x(0) = x₀` (Eqs. (7.2), (12.1)). -/
noncomputable def stateX (P : Params) (x₀ : ℝ) (φ : Control) (t : ℝ) : ℝ :=
  x₀ * Real.exp (-∑ i, P.a i * cumTime φ i t)

/-- Gold remaining in mine B at time `t`, `y(t) = y₀ exp(−r₂Φ₂(t) − r₄Φ₃(t))`: the solution of
`dy/dt = −[φ₂ r₂ + φ₃ r₄] y`, `y(0) = y₀`. -/
noncomputable def stateY (P : Params) (y₀ : ℝ) (φ : Control) (t : ℝ) : ℝ :=
  y₀ * Real.exp (-∑ i, P.b i * cumTime φ i t)

/-- Probability that the machine survives until `t`, `p(t) = exp(−q₁Φ₁(t) − q₂Φ₂(t) − q₃Φ₃(t))`:
the solution of `dp/dt = −p [φ₁ q₁ + φ₂ q₂ + φ₃ q₃]`, `p(0) = 1`. -/
noncomputable def survival (P : Params) (φ : Control) (t : ℝ) : ℝ :=
  Real.exp (-∑ i, P.q i * cumTime φ i t)

/-- The rate `f′(t) = p(t) [(φ₁ r₁ + φ₃ r₃) x(t) + (φ₂ r₂ + φ₃ r₄) y(t)]` at which expected gold
is mined (last line of Eqs. (7.2), (12.1)). -/
noncomputable def goldRate (P : Params) (x₀ y₀ : ℝ) (φ : Control) (t : ℝ) : ℝ :=
  survival P φ t *
    ∑ i, φ i t * (P.a i * stateX P x₀ φ t + P.b i * stateY P y₀ φ t)

/-- Expected amount of gold mined up to time `T`, `f(T) = ∫₀ᵀ f′(t) dt` (`f(0) = 0`). -/
noncomputable def gold (P : Params) (x₀ y₀ : ℝ) (φ : Control) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, goldRate P x₀ y₀ φ t

/-- Expected total amount of gold mined, `f(∞) = ∫₀^∞ f′(t) dt`, as an extended nonnegative real
(a lower Lebesgue integral, so it has no junk value when the integrand is not integrable). -/
noncomputable def goldInfty (P : Params) (x₀ y₀ : ℝ) (φ : Control) : ENNReal :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (goldRate P x₀ y₀ φ t)

/-- Ch. VIII, Theorem 1, Eq. (2), p. 231: the control `φ₁` follows the feedback rule
`φ₁ = 1` where `q₁ r₂ y < q₂ r₁ x`, `φ₂ = 1` (i.e. `φ₁ = 0`) where `q₁ r₂ y > q₂ r₁ x`, and
`φ₁ = r₂/(r₁ + r₂)`, `φ₂ = r₁/(r₁ + r₂)` where `q₁ r₂ y = q₂ r₁ x`, evaluated along its own
two-choice trajectory `(x(t), y(t))` from `(x₀, y₀)`, for almost every `t ≥ 0`. -/
def FollowsIndexRule (q₁ q₂ r₁ r₂ x₀ y₀ : ℝ) (φ₁ : ℝ → ℝ) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
    let x := stateX (Params.two q₁ q₂ r₁ r₂) x₀ (twoChoice φ₁) t
    let y := stateY (Params.two q₁ q₂ r₁ r₂) y₀ (twoChoice φ₁) t
    (q₁ * r₂ * y < q₂ * r₁ * x → φ₁ t = 1) ∧
    (q₂ * r₁ * x < q₁ * r₂ * y → φ₁ t = 0) ∧
    (q₁ * r₂ * y = q₂ * r₁ * x → φ₁ t = r₂ / (r₁ + r₂))

end BellmanDP.ContGoldMining


