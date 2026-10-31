-- Prove2me | Definitions.Def_DirectTradeCoffee_Model
-- name    : DirectTradeCoffee_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:50:40.830565+00:00
-- url     : https://prove2.me/theorems/e0d6ca72-b9e5-4b73-b1b1-f4715882b25a
-- title:
--   Two-stage direct-trade sourcing model: MNL clearing price, second-stage and first-stage problems, benchmarks $Q_D, Q_L, Q_H$, markups and shadow price
-- statement:
--   A specialty coffee roaster contracts $Q \ge 0$ normalized acres of a single-origin label (SL) before harvest, at cost $k(Q)$, where $k$ is continuous, nondecreasing and convex. Afterwards the yield $y$ per normalized acre and the blend-label (BL) price $\varphi$ are realized, with joint law $F$ of support $\Omega = [\varphi_l,\varphi_h]\times[y_l,y_h]$, $\varphi_l, y_l > 0$, and $E[\tilde y] = 1$. Parameters: price sensitivity $b>0$, nominal qualities $v, v_B$, post-harvest cost $c$.
--
--   **Second stage.** Selling $q$ of the harvest $Qy$ as SL clears at
--
--   $$
--   p(q) = \frac1b\left(v - \ln\frac{q\,(1+e^{v_B-b\varphi})}{1-q}\right),
--   $$
--
--   and the remaining $Qy-q$ sells as BL at $\varphi$, so the profit is
--
--   $$
--   \pi(q\mid Q,\varphi,y) = (p(q)-c)\,q + (\varphi-c)(Qy-q) - k(Q).
--   $$
--
--   The second-stage value is $\pi^*(Q,\varphi,y) = \max\{\pi(q) : 0\le q\le 1,\ q\le Qy\}$.
--
--   **First stage.** $\Pi(Q) = E[\pi^*(Q,\tilde\varphi,\tilde y)]$ is maximized over $Q\ge 0$.
--
--   **Closed forms.** With $x(\varphi) = e^{v-1}/(e^{b\varphi}+e^{v_B})$,
--
--   $$
--   q^{\circ}(\varphi) = W(x(\varphi))\,(1+W(x(\varphi)))^{-1},\quad Q_D = q^{\circ}(\mu_\varphi),\quad Q_L = \frac{q^{\circ}(\varphi_h)}{y_h},\quad Q_H = \frac{q^{\circ}(\varphi_l)}{y_l}.
--   $$
--
--   An acreage is *specialized* if $Q\le Q_L$, *diversified* if $Q\ge Q_H$ and *mixed* if $Q_L<Q<Q_H$.
--
--   **Markups.** For $0<Qy<1$,
--
--   $$
--   m_c(Q,\varphi,y) = \frac yb \ln\left[\frac{e^{v}}{e^{b\varphi}+e^{v_B}}\cdot\frac{1-Qy}{Qy}\right],\qquad m_u(Q,y) = \frac yb\cdot\frac{1}{1-Qy},
--   $$
--
--   with expectations $\bar m_c, \bar m_u$ and the expected shadow price $\lambda(Q) = E[(m_c(Q,\tilde\varphi,\tilde y) - m_u(Q,\tilde y))^+]$.
--
--   These objects are the shared vocabulary of every statement of the mission.
--
--   **Formalization Note** $\pi^*$ and $\Pi$ are the values of the optimization problems, not Proposition 1's formulas. The feasible set uses $q<1$: at $q=1$ no finite price clears the market. Support $\Omega$ is encoded as $F(\Omega^c)=0$ together with positive mass of every ball around a point of $\Omega$; no density is assumed and the rectangle may be degenerate. $\rho\sigma_\varphi\sigma_y$ is represented by the covariance. $\lambda$'s integrand is written as $0$ where $Qy\ge 1$. The one-sided derivatives of $k$ are `derivWithin` on `Ioi` and `Iio`.
-- source:
--   Webster–Kazaz–Gheibi, Direct Trade Sourcing Strategies for Specialty Coffee, MSOM (2024), doi:10.1287/msom.2021.0586, §3.2 pp.9–10, displays (2), (3); §3.3 p.11, display (4); §4.1 p.11, displays (5), (6), p.12; §4.2 p.13, displays (8), (9), p.14; notation p.31

import Mathlib
import Definitions.Def_DirectTradeCoffee_lambertW

open MeasureTheory

namespace DirectTradeCoffee

/-- **Demand and cost parameters** of Webster–Kazaz–Gheibi, *Direct Trade Sourcing Strategies for
Specialty Coffee*, MSOM (2024), doi:10.1287/msom.2021.0586, §3.2, pp.9–10, notation p.31: the
connoisseur price sensitivity `b`, the nominal qualities `v` of the single-origin label (SL) and
`vB` of the blend label (BL), and the post-harvest cost `c` per normalized pound.

**Formalization Note.** `0 < b` is the meaning of "price-sensitivity" and every formula divides by
`b`. The paper's `v > v_B` (p.9; p.31 prints `v_B > v`) is not assumed: no statement uses it. -/
structure Params where
  /-- price sensitivity -/
  b : ℝ
  /-- nominal quality of SL -/
  v : ℝ
  /-- nominal quality of BL -/
  vB : ℝ
  /-- post-harvest variable cost per normalized pound -/
  c : ℝ
  b_pos : 0 < b

/-- **The pre-harvest cost** `k(Q)`: "Function `k(Q)` is continuous, nondecreasing, and convex"
(§3.2, p.10), on the acreage domain `Q ≥ 0`. Not assumed differentiable.

**Formalization Note.** `k` is real-valued on `[0, ∞)`. Values on `Q < 0` are irrelevant. -/
structure IsCost (k : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn k (Set.Ici 0)
  monotoneOn : MonotoneOn k (Set.Ici 0)
  convexOn : ConvexOn ℝ (Set.Ici 0) k

/-- Right derivative `k′₊(Q)` of the cost: the paper's `k′(Q)`, "the right-derivative at `Q` if
left- and right-derivatives differ" (§4.2, p.13). -/
noncomputable def kRight (k : ℝ → ℝ) (Q : ℝ) : ℝ := derivWithin k (Set.Ioi Q) Q

/-- Left derivative `k′₋(Q)` of the cost. -/
noncomputable def kLeft (k : ℝ → ℝ) (Q : ℝ) : ℝ := derivWithin k (Set.Iio Q) Q

/-- **The uncertainty** (notation list, p.31): the joint law `F` of the blend price and the yield,
`(φ̃, ỹ)`, with first coordinate the price, second coordinate the yield. It has positive support
`Ω = [φ_l, φ_h] × [y_l, y_h]`, and mean yield `μ_y = 1` (normalized units).

**Formalization Note.** "Support `Ω`" is encoded by `null_compl` (`F(Ωᶜ) = 0`) and `ball_pos`
(every open ball around a point of `Ω` has positive mass). No density, atomlessness or independence
is assumed: the rectangle may be degenerate (the deterministic case (7), p.12). -/
structure Uncertainty where
  /-- lower end of the price support -/
  φl : ℝ
  /-- upper end of the price support -/
  φh : ℝ
  /-- lower end of the yield support -/
  yl : ℝ
  /-- upper end of the yield support -/
  yh : ℝ
  /-- joint law of `(φ̃, ỹ)` -/
  F : Measure (ℝ × ℝ)
  prob : IsProbabilityMeasure F
  φl_pos : 0 < φl
  yl_pos : 0 < yl
  φl_le : φl ≤ φh
  yl_le : yl ≤ yh
  null_compl : F ((Set.Icc φl φh ×ˢ Set.Icc yl yh)ᶜ) = 0
  ball_pos : ∀ z ∈ Set.Icc φl φh ×ˢ Set.Icc yl yh, ∀ ε : ℝ, 0 < ε → 0 < F (Metric.ball z ε)
  mean_yield : ∫ z, z.2 ∂F = 1

/-- The support rectangle `Ω = [φ_l, φ_h] × [y_l, y_h]`. -/
def Uncertainty.Ω (U : Uncertainty) : Set (ℝ × ℝ) := Set.Icc U.φl U.φh ×ˢ Set.Icc U.yl U.yh

/-- Mean blend price `μ_φ = E[φ̃]`. -/
noncomputable def Uncertainty.meanφ (U : Uncertainty) : ℝ := ∫ z, z.1 ∂U.F

/-- Blend-price variance `σ_φ²`. -/
noncomputable def Uncertainty.varφ (U : Uncertainty) : ℝ := ∫ z, (z.1 - U.meanφ) ^ 2 ∂U.F

/-- Yield variance `σ_y²`; the mean yield is `1`. -/
noncomputable def Uncertainty.varY (U : Uncertainty) : ℝ := ∫ z, (z.2 - 1) ^ 2 ∂U.F

/-- Covariance of `(φ̃, ỹ)`, the paper's `ρσ_φσ_y` (p.31: `σ_φy`).

**Formalization Note.** `ρ` is undefined when a variance is `0`, so the covariance itself is used.
With `μ_y = 1`, `μ_φ + Cov = E[φ̃ỹ]` (p.14). -/
noncomputable def Uncertainty.cov (U : Uncertainty) : ℝ :=
  ∫ z, (z.1 - U.meanφ) * (z.2 - 1) ∂U.F

/-- **SL clearing price**, display (2), p.10:
`p(q) = (1/b)(v − ln(q(1 + e^{v_B − bφ})/(1 − q)))`, at realized blend price `φ`.

**Formalization Note.** Used on `0 ≤ q < 1`. At `q = 0` Lean's `log 0 = 0` makes `p(0) = v/b`, but
`p` enters the profit only through `p(q) q`, whose value `0` there is the limit as `q → 0`. -/
noncomputable def price (P : Params) (q φ : ℝ) : ℝ :=
  (1 / P.b) * (P.v - Real.log (q * (1 + Real.exp (P.vB - P.b * φ)) / (1 - q)))

/-- **Second-stage profit**, display (3), p.10:
`π(q | Q, φ, y) = (p(q) − c) q + (φ − c)(Qy − q) − k(Q)`. -/
noncomputable def profit (P : Params) (k : ℝ → ℝ) (q Q φ y : ℝ) : ℝ :=
  (price P q φ - P.c) * q + (φ - P.c) * (Q * y - q) - k Q

/-- **Feasible SL quantities** of the second-stage problem (p.10): `0 ≤ q`, `q ≤ Qy`, and `q < 1`.

**Formalization Note.** The paper writes `q ≤ 1`. At `q = 1` no finite price clears the market
(`p → −∞`, the objective tends to `−∞`), and Lean's `x / 0 = 0` would give `q = 1` the junk price
`v/b`, so `q = 1` is excluded. The maximum is unchanged. -/
def feasible (Q y : ℝ) : Set ℝ := {q | 0 ≤ q ∧ q < 1 ∧ q ≤ Q * y}

/-- **Second-stage optimal value** `π*(Q, φ, y) = max_q {π(q) : 0 ≤ q ≤ 1, q ≤ Qy}` (p.10), as the
supremum of the profit over the feasible set. Not defined by the closed form of Proposition 1. -/
noncomputable def secondStageValue (P : Params) (k : ℝ → ℝ) (Q φ y : ℝ) : ℝ :=
  sSup ((fun q => profit P k q Q φ y) '' feasible Q y)

/-- `q` solves the second-stage problem at `(Q, φ, y)` (p.10). -/
def IsOptimalQuantity (P : Params) (k : ℝ → ℝ) (Q φ y q : ℝ) : Prop :=
  q ∈ feasible Q y ∧ IsMaxOn (fun r => profit P k r Q φ y) (feasible Q y) q

/-- **First-stage expected profit** `Π(Q) = E[π*(Q, φ̃, ỹ)]`, display (4), p.11. -/
noncomputable def expectedProfit (P : Params) (k : ℝ → ℝ) (U : Uncertainty) (Q : ℝ) : ℝ :=
  ∫ z, secondStageValue P k Q z.1 z.2 ∂U.F

/-- `Q` is an optimal acreage: a maximizer of `Π` on `Q ≥ 0`, display (4), p.11. -/
def IsOptimalAcreage (P : Params) (k : ℝ → ℝ) (U : Uncertainty) (Q : ℝ) : Prop :=
  0 ≤ Q ∧ IsMaxOn (expectedProfit P k U) (Set.Ici 0) Q

/-- The argument `e^{v−1}/(e^{bφ} + e^{v_B})` of `W` in Proposition 1, p.10, and (5), (6), (8). -/
noncomputable def xArg (P : Params) (φ : ℝ) : ℝ :=
  Real.exp (P.v - 1) / (Real.exp (P.b * φ) + Real.exp P.vB)

/-- **Unconstrained second-stage quantity**, display (8), p.13:
`q°(φ) = W(x(φ)) (1 + W(x(φ)))⁻¹`. -/
noncomputable def qo (P : Params) (φ : ℝ) : ℝ :=
  lambertW (xArg P φ) * (1 + lambertW (xArg P φ))⁻¹

/-- **Deterministic benchmark** `Q_D`, p.11: `q°` at the mean price `μ_φ`. -/
noncomputable def QD (P : Params) (U : Uncertainty) : ℝ := qo P U.meanφ

/-- **Benchmark** `Q_L`, display (5), p.11: `Q_L = (1/y_h) W(x(φ_h)) (1 + W(x(φ_h)))⁻¹`. -/
noncomputable def QL (P : Params) (U : Uncertainty) : ℝ := qo P U.φh / U.yh

/-- **Benchmark** `Q_H`, display (6), p.11: `Q_H = (1/y_l) W(x(φ_l)) (1 + W(x(φ_l)))⁻¹`. -/
noncomputable def QH (P : Params) (U : Uncertainty) : ℝ := qo P U.φl / U.yl

/-- An acreage is **specialized** if `Q ≤ Q_L` (p.12; proof of Proposition 3, p.43: "a specialized
sourcing strategy is optimal (i.e., `Q* ≤ Q_L`)"). -/
def IsSpecialized (P : Params) (U : Uncertainty) (Q : ℝ) : Prop := Q ≤ QL P U

/-- An acreage is **diversified** if `Q ≥ Q_H` (p.12). -/
def IsDiversified (P : Params) (U : Uncertainty) (Q : ℝ) : Prop := QH P U ≤ Q

/-- An acreage is **mixed** if `Q ∈ (Q_L, Q_H)` (p.12). -/
def IsMixed (P : Params) (U : Uncertainty) (Q : ℝ) : Prop := QL P U < Q ∧ Q < QH P U

/-- **Constrained markup per input unit** (p.13):
`m_c(Q, φ, y) = (y/b) ln[(e^v/(e^{bφ} + e^{v_B})) ((1 − Qy)/(Qy))]`.

**Formalization Note.** Meaningful for `0 < Qy < 1`; outside that range the formula is undefined in
the paper and a Lean junk value here. Statements use it only inside that range. -/
noncomputable def mc (P : Params) (Q φ y : ℝ) : ℝ :=
  (y / P.b) *
    Real.log (Real.exp P.v / (Real.exp (P.b * φ) + Real.exp P.vB) * ((1 - Q * y) / (Q * y)))

/-- **Unconstrained markup per input unit** (p.13): `m_u(Q, y) = (y/b)(1/(1 − Qy))`.

**Formalization Note.** Meaningful for `Qy < 1`. -/
noncomputable def mu (P : Params) (Q y : ℝ) : ℝ := (y / P.b) * (1 / (1 - Q * y))

/-- `m̄_c(Q) = E[m_c(Q, φ̃, ỹ)]`, p.14. -/
noncomputable def mcBar (P : Params) (U : Uncertainty) (Q : ℝ) : ℝ :=
  ∫ z, mc P Q z.1 z.2 ∂U.F

/-- `m̄_u(Q) = E[m_u(Q, ỹ)]`, p.14. -/
noncomputable def muBar (P : Params) (U : Uncertainty) (Q : ℝ) : ℝ :=
  ∫ z, mu P Q z.2 ∂U.F

/-- **Expected shadow price**, display (9), p.13: `λ(Q) = E[(m_c(Q, φ̃, ỹ) − m_u(Q, ỹ))⁺]`.

**Formalization Note.** The paper's positive part is `0` at every realization with `Qy ≥ q°(φ)`
(p.13), in particular wherever `Qy ≥ 1`, where `m_c` and `m_u` are undefined. The integrand writes
that value explicitly, so Lean's junk values of `log` and division never enter. -/
noncomputable def lam (P : Params) (U : Uncertainty) (Q : ℝ) : ℝ :=
  ∫ z, (if Q * z.2 < 1 then max (mc P Q z.1 z.2 - mu P Q z.2) 0 else 0) ∂U.F

end DirectTradeCoffee


