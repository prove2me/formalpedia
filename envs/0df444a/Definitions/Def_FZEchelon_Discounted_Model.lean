-- Prove2me | Definitions.Def_FZEchelon_Discounted_Model
-- name    : FZEchelon_Discounted_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:03:24.338749+00:00
-- url     : https://prove2.me/theorems/649432b7-f4c0-434c-b57f-79ca240dfe00
-- title:
--   The two-echelon depot–outlet model of §1: data, states, dynamics, costs $D, R, c^d$, the penalty $P$, the depot problem and the policy $\pi_\alpha^*$
-- statement:
--   This file defines the one-depot, one-outlet inventory system of Federgruen and Zipkin (1984), §1, and the objects of the infinite-horizon problems built from it.
--
--   **Data.** The cost data are a fixed order cost $K$, a proportional order cost rate $c^d$, a proportional shipment cost rate $c^r$, a holding cost rate $h^d$ on total system inventory, an additional holding cost rate $h^r$ at the outlet, and a backorder penalty rate $p^r$. Further parameters are the discount rate $\alpha$, the shipment leadtime $l \in \mathbb N$, the order leadtime $L \in \mathbb N$, and the law $\nu$ of the one-period demand $u$. The $i$-period demand $u^{(i)}$ is the sum of $i$ independent copies of $u$, $\mu = E(u)$ and $\mu^{(i)} = i\mu$. The standing assumptions of §1 (p. 821) are bundled as: all six cost factors positive, $0 \le \alpha \le 1$, and $u$ nonnegative, continuous (no atoms) and of finite mean.
--
--   **State and dynamics.** A state is $(\hat y, v^d, x^r)$, where $\hat y = (y^1, \dots, y^L)$ lists the outstanding orders ($y^i$ was placed $i$ periods ago), $v^d$ is the depot's echelon inventory and $x^r$ is the outlet inventory plus shipments in transit. An action is an order $y$ and a shipment $z$, subject to
--   $$
--   y \ge 0, \qquad z \ge 0, \qquad x^r + z \le v^d + y^L .
--   $$
--   With demand $u$ the next state is $\big((y, y^1, \dots, y^{L-1}),\ v^d + y^L - u,\ x^r + z - u\big)$. The physical states are those with $\hat y \ge 0$ and $x^r \le v^d$.
--
--   **Costs** (p. 822). $D(v) = h^d v$,
--   $$
--   R(x) = \alpha^l\big\{-h^d(x - \mu^{(l)}) + p^r E[u^{(l+1)} - x]^+ + (h^d + h^r) E[x - u^{(l+1)}]^+\big\},
--   $$
--   and $c^d(y) = 0$ if $y = 0$, $K + c^d y$ if $y > 0$. The one-period cost is $c^d(y) + D(v^d + y^L) + c^r z + R(x^r + z)$.
--
--   **Outlet and depot problems.** The outlet problem $IH^r_\alpha$ has state $x^r$, action $z \ge 0$, dynamics $x^r \mapsto x^r + z - u$ and cost $c^r z + R(x^r + z)$. A critical number $x^{r*}$ is a global minimizer of $(1-\alpha)c^r x + R(x)$ (property (b), p. 824), and the stationary induced penalty is
--   $$
--   P(x) = \begin{cases} 0, & x \ge x^{r*},\\ (1-\alpha)c^r(x - x^{r*}) + [R(x) - R(x^{r*})], & x < x^{r*}.\end{cases}
--   $$
--   The depot problem $IH^d_\alpha$ (p. 825) has state $(\hat y, v^d)$, action $y \ge 0$, the same order dynamics, and cost $c^d(y) + D(v^d + y^L) + P(v^d + y^L)$.
--
--   **The policy $\pi_\alpha^*$** (p. 825, with the shipment rule of p. 819). Given a stationary order policy $\sigma^d(\hat y, v^d)$, the action of $\pi_\alpha^*$ in state $(\hat y, v^d, x^r)$ is $y = \sigma^d(\hat y, v^d)$ and
--   $$
--   z = \max\{0,\ \min\{x^{r*},\ v^d + y^L\} - x^r\},
--   $$
--   i.e. ship up to the critical number if the depot has that much stock, otherwise ship as much as possible.
--
--   **Formalization Note.** The pipeline $\hat y$ is a vector indexed by $\{0, \dots, L-1\}$; index $k$ holds the paper's $y^{k+1}$. The arriving order $y^L$ is the last pipeline entry when $L \ge 1$; when $L = 0$ the paper does not write $y^0$, and the current order is taken to arrive at once, which is the leadtime-zero reading of "an order arrives $L$ periods after it is placed". $\mu^{(l)}$ is $l\mu$ as on p. 821, so for $l = 0$ it is $0$ and $u^{(1)} = u$. The model structure carries no sign conditions; theorems state them through the standing-assumption bundle.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 819 (shipment rule), pp. 820-822 §1 (data, variables, dynamics, D, R, c^d), p. 824 (IH_α^r, property (b), P), p. 825 (IH_α^d, π_α*)

import Mathlib
import Definitions.Def_FZEchelon_Discounted_ControlSystem

open MeasureTheory

namespace FZEchelon.Discounted

/-- The data of the two-echelon (depot → retail outlet) inventory model of Federgruen–Zipkin
(1984), §1, pp. 820–821: the cost data `K, c^d, c^r, h^d, h^r, p^r`, the discount factor `α`,
the shipment leadtime `l`, the order leadtime `L`, and the law `ν` of the one-period demand `u`
(a probability measure on `ℝ`). No sign conditions are built in; theorems state them. -/
structure Model where
  /-- fixed cost to place an order -/
  K : ℝ
  /-- cost rate for proportional order costs `c^d` -/
  cd : ℝ
  /-- cost rate for proportional shipment costs `c^r` -/
  cr : ℝ
  /-- holding cost rate for total system inventory `h^d` -/
  hd : ℝ
  /-- additional holding cost rate at the retail outlet `h^r` -/
  hr : ℝ
  /-- penalty cost rate for backorders at the retail outlet `p^r` -/
  pr : ℝ
  /-- the discount rate `α` -/
  α : ℝ
  /-- leadtime for shipments -/
  l : ℕ
  /-- leadtime for orders -/
  L : ℕ
  /-- the law of the one-period demand `u` -/
  ν : Measure ℝ
  isProb : IsProbabilityMeasure ν

attribute [instance] Model.isProb

namespace Model

variable (M : Model)

/-- The standing assumptions of §1 (p. 821): the six cost factors are positive, `0 ≤ α ≤ 1`, the
one-period demand is nonnegative, continuous (no atoms) and has a finite mean. -/
structure StandingAssumptions : Prop where
  K_pos : 0 < M.K
  cd_pos : 0 < M.cd
  cr_pos : 0 < M.cr
  hd_pos : 0 < M.hd
  hr_pos : 0 < M.hr
  pr_pos : 0 < M.pr
  α_nonneg : 0 ≤ M.α
  α_le_one : M.α ≤ 1
  demand_nonneg : M.ν (Set.Iio 0) = 0
  demand_noAtoms : ∀ x : ℝ, M.ν {x} = 0
  demand_integrable : Integrable (fun t : ℝ => t) M.ν

/-- The mean one-period demand `μ = E(u)`. -/
noncomputable def mu : ℝ := ∫ t, t ∂M.ν

/-- The law of the `i`-period demand `u^(i)`, the sum of `i` independent copies of `u`
(`u^(0) = 0`). -/
noncomputable def demandLaw (i : ℕ) : Measure ℝ :=
  (Measure.pi fun _ : Fin i => M.ν).map (fun t => ∑ j, t j)

/-- The depot holding cost `D(v) = h^d v` (p. 822). -/
def D (v : ℝ) : ℝ := M.hd * v

/-- The outlet cost (p. 822)
`R(x) = α^l {−h^d (x − μ^(l)) + p^r E[u^(l+1) − x]⁺ + (h^d + h^r) E[x − u^(l+1)]⁺}`,
with `μ^(l) = l μ`. -/
noncomputable def R (x : ℝ) : ℝ :=
  M.α ^ M.l * (-(M.hd * (x - (M.l : ℝ) * M.mu))
    + M.pr * ∫ t, max (t - x) 0 ∂(M.demandLaw (M.l + 1))
    + (M.hd + M.hr) * ∫ t, max (x - t) 0 ∂(M.demandLaw (M.l + 1)))

/-- The order cost function `c^d(y) = 0` if `y = 0`, `K + c^d y` if `y > 0` (p. 822). -/
noncomputable def orderCost (y : ℝ) : ℝ := if y = 0 then 0 else M.K + M.cd * y

/-- A depot state `(ŷ, v^d)`: `ŷ k` is the outstanding order placed `k + 1` periods ago
(the paper's `y^{k+1}`), and `v^d` is the depot's echelon inventory. -/
abbrev DepotState := (Fin M.L → ℝ) × ℝ

/-- A system state `(ŷ, v^d, x^r)`; `x^r` is outlet inventory plus shipments in transit. -/
abbrev State := (Fin M.L → ℝ) × ℝ × ℝ

/-- The order `y^L` arriving now: the order placed `L` periods ago, `ŷ (L − 1)`, when `L ≥ 1`;
when `L = 0` it is the current order `y`. -/
def arrival (yhat : Fin M.L → ℝ) (y : ℝ) : ℝ :=
  if h : 0 < M.L then yhat ⟨M.L - 1, by omega⟩ else y

/-- The next pipeline `(y, y^1, …, y^{L−1})` after ordering `y`. -/
def shift (yhat : Fin M.L → ℝ) (y : ℝ) : Fin M.L → ℝ :=
  fun k => if h : (k : ℕ) = 0 then y else yhat ⟨(k : ℕ) - 1, by omega⟩

/-- The two-echelon system of §1 (pp. 821–822). Action `a = (y, z)` (order, shipment); with
demand `u`: `x^r ↦ x^r + z − u`, `v^d ↦ v^d + y^L − u`, `ŷ ↦ (y, y^1, …, y^{L−1})`; one-period
cost `c^d(y) + D(v^d + y^L) + c^r z + R(x^r + z)`; constraints `y ≥ 0, z ≥ 0,
x^r + z ≤ v^d + y^L`. -/
noncomputable def system : ControlSystem M.State (ℝ × ℝ) where
  next s a u := (M.shift s.1 a.1, s.2.1 + M.arrival s.1 a.1 - u, s.2.2 + a.2 - u)
  cost s a := M.orderCost a.1 + M.D (s.2.1 + M.arrival s.1 a.1) + M.cr * a.2 + M.R (s.2.2 + a.2)
  feasible s a := 0 ≤ a.1 ∧ 0 ≤ a.2 ∧ s.2.2 + a.2 ≤ s.2.1 + M.arrival s.1 a.1

/-- The outlet problem `IH_α^r` (p. 824): state `x^r`, action the shipment `z ≥ 0` (the only
constraint), dynamics `x^r ↦ x^r + z − u`, one-period cost `c^r z + R(x^r + z)`. -/
noncomputable def outletSystem : ControlSystem ℝ ℝ where
  next x z u := x + z - u
  cost x z := M.cr * z + M.R (x + z)
  feasible _ z := 0 ≤ z

/-- The physical states: outstanding orders are nonnegative and the depot's on-hand stock
`v^d − x^r` is nonnegative. -/
def InDomain (s : M.State) : Prop := (∀ k, 0 ≤ s.1 k) ∧ s.2.2 ≤ s.2.1

/-- `x^{r*}` is a critical number of the stationary outlet problem: a global minimizer of
`(1 − α) c^r x + R(x)` (property (b), p. 824). -/
def IsStationaryCriticalNumber (xstar : ℝ) : Prop :=
  ∀ x, (1 - M.α) * M.cr * xstar + M.R xstar ≤ (1 - M.α) * M.cr * x + M.R x

/-- The stationary induced penalty cost (p. 824): `P(x) = 0` for `x ≥ x^{r*}` and
`P(x) = (1 − α) c^r (x − x^{r*}) + [R(x) − R(x^{r*})]` for `x < x^{r*}`. -/
noncomputable def P (xstar x : ℝ) : ℝ :=
  if xstar ≤ x then 0 else (1 - M.α) * M.cr * (x - xstar) + (M.R x - M.R xstar)

/-- The depot problem `IH_α^d` (p. 825): state `(ŷ, v^d)`, action the order `y ≥ 0`,
dynamics `v^d ↦ v^d + y^L − u`, `ŷ ↦ (y, y^1, …, y^{L−1})`, one-period cost
`c^d(y) + D(v^d + y^L) + P(v^d + y^L)`. -/
noncomputable def depotSystem (xstar : ℝ) : ControlSystem M.DepotState ℝ where
  next p y u := (M.shift p.1 y, p.2 + M.arrival p.1 y - u)
  cost p y := M.orderCost y + M.D (p.2 + M.arrival p.1 y) + M.P xstar (p.2 + M.arrival p.1 y)
  feasible _ y := 0 ≤ y

/-- The stationary policy `π_α*` (p. 825, with the shipment rule of p. 819): order according to
the depot policy `σd`, and ship up to `x^{r*}` if the depot has that much stock, otherwise as
much as possible: `z = max(0, min(x^{r*}, v^d + y^L) − x^r)`. -/
noncomputable def piStar (σd : M.DepotState → ℝ) (xstar : ℝ) (s : M.State) : ℝ × ℝ :=
  (σd (s.1, s.2.1), max 0 (min xstar (s.2.1 + M.arrival s.1 (σd (s.1, s.2.1))) - s.2.2))

end Model

end FZEchelon.Discounted


