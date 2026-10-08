-- Prove2me | Definitions.Def_FZEchelon_AverageCost_Model
-- name    : FZEchelon_AverageCost_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:00:04.198477+00:00
-- url     : https://prove2.me/theorems/824f5e0d-784d-47b3-8cd1-0207bed1ce99
-- title:
--   The depot–outlet inventory model of §1: data, states, actions, dynamics, the costs D, R, c^d, the penalty P and the shipment rule of π*
-- statement:
--   This file sets up the two-echelon inventory system of Federgruen and Zipkin (1984), §1: a **depot** that orders from an outside supplier and a **retail outlet** that is supplied by the depot and faces random customer demand. Backorders are allowed at the outlet.
--
--   **Data.** The cost factors are the fixed order cost $K$, the proportional order cost rate $c^d$, the proportional shipment cost rate $c^r$, the holding cost rate $h^d$ on total system inventory, the additional holding cost rate $h^r$ at the outlet and the backorder penalty rate $p^r$ at the outlet. Further, $\alpha$ is the discount factor, $l \ge 0$ the shipment lead time and $L \ge 0$ the order lead time. The one-period demand $u$ has law $\nu$, with mean $\mu = E(u)$; demands in different periods are independent with law $\nu$. The $i$-period demand $u^{(i)}$ is the sum of $i$ independent one-period demands, and $\mu^{(l)} = l\mu$.
--
--   **State and actions.** A state is $(\tilde y, v^d, x^r)$: the outstanding orders $\tilde y = (y^1, \dots, y^L)$, $y^i$ being the order placed $i$ periods ago; the echelon inventory $v^d$ of the depot (depot stock plus $x^r$); and the inventory position $x^r$ of the outlet (stock plus shipments in transit). The actions are an order $y$ and a shipment $z$, constrained by
--   $$y \ge 0,\qquad z \ge 0,\qquad x^r + z \le v^d + y^L,$$
--   where $y^L$ is the order arriving now. With demand $u$ the state moves to
--   $$\big((y, y^1, \dots, y^{L-1}),\; v^d + y^L - u,\; x^r + z - u\big).$$
--   The **physical states** are those with $\tilde y \ge 0$ and $x^r \le v^d$ (the depot's own stock $v^d - x^r$ is nonnegative).
--
--   **Costs.** With $(t)^+ = \max(t, 0)$,
--   $$D(v) = h^d v,\qquad R(x) = \alpha^l\big\{-h^d(x - \mu^{(l)}) + p^r E[u^{(l+1)} - x]^+ + (h^d + h^r) E[x - u^{(l+1)}]^+\big\},$$
--   and the order cost is $c^d(y) = 0$ if $y = 0$ and $K + c^d y$ if $y > 0$. The one-period system cost is $c^d(y) + D(v^d + y^L) + c^r z + R(x^r + z)$. For a critical number $x^{r*}$ the stationary induced penalty is
--   $$P(x) = 0 \ (x \ge x^{r*}),\qquad P(x) = (1 - \alpha)c^r(x - x^{r*}) + [R(x) - R(x^{r*})] \ (x < x^{r*}).$$
--   The **depot problem** has states $(\tilde y, v^d)$, orders $y \ge 0$ and one-period cost $c^d(y) + D(v^d + y^L) + P(v^d + y^L)$; the **outlet problem** has states $x^r$, shipments $z \ge 0$ and one-period cost $c^r z + R(x^r + z)$.
--
--   **The decision rule of $\pi^*$.** Given a stationary order rule $\sigma^d(\tilde y, v^d)$ for the depot problem, $\pi^*$ orders $y = \sigma^d(\tilde y, v^d)$ and ships according to the modified critical-number rule of the Introduction, "ship up to the critical number, if the depot has that much stock; if not, ship as much as possible":
--   $$z = \max\big(0,\ \min(x^{r*}, v^d + y^L) - x^r\big).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** A state is a triple in $(\mathrm{Fin}\,L \to \mathbb R) \times \mathbb R \times \mathbb R$; the Lean entry $\tilde y_k$ is the paper's $y^{k+1}$, so for $L \ge 1$ the arriving order is $\tilde y_{L-1}$. The page does not write $y^0$; for $L = 0$ the order placed now arrives at once, so $y^L$ is the current order $y$. The law of $u^{(i)}$ is the image of the product measure $\nu^{\otimes i}$ under $(t_1,\dots,t_i) \mapsto \sum_j t_j$. No positivity or probability hypothesis is built into the structure; each theorem states its own.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, pp. 819-825: Introduction (shipment rule, p. 819); §1 cost data and parameters (pp. 820-821), variables, constraints and dynamics (p. 821), D, R, c^d (p. 822), P (p. 824), depot problem (p. 825), outlet problem (p. 824)

import Mathlib

namespace FZEchelon.AverageCost

open MeasureTheory

/-- The data of the two-echelon (depot / retail outlet) inventory model of Federgruen and Zipkin
(1984), §1, pp. 820–821.

* `K` fixed order cost, `cd` proportional order cost rate, `cr` proportional shipment cost rate,
  `hd` holding cost rate for total system inventory, `hr` additional holding cost rate at the
  outlet, `pr` backorder penalty rate at the outlet;
* `α` the discount factor (`0 ≤ α ≤ 1` on the page; `α = 1` for the average-cost criterion);
* `l` the shipment lead time, `L` the order lead time (nonnegative integers);
* `ν` the law of the one-period demand `u`; demands of different periods are i.i.d. with law `ν`.

No positivity or probability assumption is built in: every theorem states the hypotheses it
uses. -/
structure Model where
  K : ℝ
  cd : ℝ
  cr : ℝ
  hd : ℝ
  hr : ℝ
  pr : ℝ
  α : ℝ
  l : ℕ
  L : ℕ
  ν : Measure ℝ

namespace Model

variable (m : Model)

/-- `μ = E(u)`, the mean one-period demand. -/
noncomputable def μ : ℝ := ∫ t, t ∂m.ν

/-- The law of the `i`-period demand `u^(i)`, the sum of `i` independent one-period demands:
the image of the product measure `ν^{⊗ i}` under `(t_1, …, t_i) ↦ t_1 + ⋯ + t_i`. -/
noncomputable def demandLaw (i : ℕ) : Measure ℝ :=
  (Measure.pi fun _ : Fin i => m.ν).map (fun t => ∑ j, t j)

/-- `D(v) = h^d v` (p. 822). -/
def D (v : ℝ) : ℝ := m.hd * v

/-- `R(x) = α^l {−h^d (x − μ^(l)) + p^r E[u^(l+1) − x]^+ + (h^d + h^r) E[x − u^(l+1)]^+}`
(p. 822), with `μ^(l) = l μ`. -/
noncomputable def R (x : ℝ) : ℝ :=
  m.α ^ m.l * (-m.hd * (x - (m.l : ℝ) * m.μ)
    + m.pr * ∫ t, max (t - x) 0 ∂(m.demandLaw (m.l + 1))
    + (m.hd + m.hr) * ∫ t, max (x - t) 0 ∂(m.demandLaw (m.l + 1)))

/-- The order cost function `c^d(y) = 0` if `y = 0`, `K + c^d y` if `y > 0` (p. 822). -/
noncomputable def orderCost (y : ℝ) : ℝ := if y = 0 then 0 else m.K + m.cd * y

/-- The stationary induced penalty cost (p. 824), for a critical number `xstar`:
`P(x) = 0` for `x ≥ x^{r*}`, `P(x) = (1 − α) c^r (x − x^{r*}) + [R(x) − R(x^{r*})]` for `x < x^{r*}`. -/
noncomputable def P (xstar : ℝ) (x : ℝ) : ℝ :=
  if xstar ≤ x then 0 else (1 - m.α) * m.cr * (x - xstar) + (m.R x - m.R xstar)

end Model

/-- The order arriving now, `y^L`, given the pipeline `ŷ` and the current order `y`. The Lean
entry `ŷ k` is the paper's `y^{k+1}`, the order placed `k + 1` periods ago, so for `L ≥ 1` the
arriving order is `ŷ (L − 1)`. For `L = 0` the order placed now arrives at once, so `y^L = y`. -/
def arrival {L : ℕ} (yh : Fin L → ℝ) (y : ℝ) : ℝ :=
  if h : 0 < L then yh ⟨L - 1, Nat.sub_lt h Nat.one_pos⟩ else y

/-- The new pipeline `(y, y^1, …, y^{L−1})` after ordering `y` (p. 821): entry `0` is `y`,
entry `k ≥ 1` is the old entry `k − 1`. -/
def shift {L : ℕ} (yh : Fin L → ℝ) (y : ℝ) : Fin L → ℝ :=
  fun k => if k.val = 0 then y else yh ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩

/-- A state of the whole system: `(ŷ, v^d, x^r)`, the order pipeline, the echelon inventory at
the depot and the inventory position at the outlet. -/
abbrev SysState (L : ℕ) : Type := (Fin L → ℝ) × ℝ × ℝ

/-- A state of the depot problem: `(ŷ, v^d)`. -/
abbrev DepotState (L : ℕ) : Type := (Fin L → ℝ) × ℝ

/-- Shipments allowed in the outlet problem: `z ≥ 0` (p. 824). -/
def OutletFeasible (_x : ℝ) (z : ℝ) : Prop := 0 ≤ z

/-- Outlet dynamics: `x^r ← x^r + z − u`. -/
def outletNext (x : ℝ) (z : ℝ) (u : ℝ) : ℝ := x + z - u

/-- The physical states: outstanding orders are nonnegative and the depot's own stock
`v^d − x^r` is nonnegative. -/
def InDomain {L : ℕ} (s : SysState L) : Prop := (∀ k, 0 ≤ s.1 k) ∧ s.2.2 ≤ s.2.1

namespace Model

variable (m : Model)

/-- The actions `(y, z)` allowed at state `s = (ŷ, v^d, x^r)` (p. 821):
`y ≥ 0, z ≥ 0, x^r + z ≤ v^d + y^L`. -/
def SysFeasible (s : SysState m.L) (a : ℝ × ℝ) : Prop :=
  0 ≤ a.1 ∧ 0 ≤ a.2 ∧ s.2.2 + a.2 ≤ s.2.1 + arrival s.1 a.1

/-- The dynamics (p. 821): with action `(y, z)` and demand `u`,
`x^r ← x^r + z − u`, `v^d ← v^d + y^L − u`, `ŷ ← (y, y^1, …, y^{L−1})`. -/
def sysNext (s : SysState m.L) (a : ℝ × ℝ) (u : ℝ) : SysState m.L :=
  (shift s.1 a.1, s.2.1 + arrival s.1 a.1 - u, s.2.2 + a.2 - u)

/-- The one-period system cost `c^d(y) + D(v^d + y^L) + c^r z + R(x^r + z)` (pp. 822, 824). -/
noncomputable def sysCost (s : SysState m.L) (a : ℝ × ℝ) : ℝ :=
  m.orderCost a.1 + m.D (s.2.1 + arrival s.1 a.1) + m.cr * a.2 + m.R (s.2.2 + a.2)

/-- Orders allowed in the depot problem: `y ≥ 0`. -/
def DepotFeasible (_p : DepotState m.L) (y : ℝ) : Prop := 0 ≤ y

/-- Depot dynamics: `v^d ← v^d + y^L − u`, `ŷ ← (y, y^1, …, y^{L−1})`. -/
def depotNext (p : DepotState m.L) (y : ℝ) (u : ℝ) : DepotState m.L :=
  (shift p.1 y, p.2 + arrival p.1 y - u)

/-- The one-period depot cost `c^d(y) + D(v^d + y^L) + P(v^d + y^L)` (p. 825). -/
noncomputable def depotCost (xstar : ℝ) (p : DepotState m.L) (y : ℝ) : ℝ :=
  m.orderCost y + m.D (p.2 + arrival p.1 y) + m.P xstar (p.2 + arrival p.1 y)

/-- The one-period outlet cost `c^r z + R(x^r + z)` (p. 824). -/
noncomputable def outletCost (x : ℝ) (z : ℝ) : ℝ := m.cr * z + m.R (x + z)

/-- The modified critical-number shipment rule of the Introduction (p. 819): ship up to the
critical number `x^{r*}` if the depot has that much stock, otherwise ship as much as possible,
`z = max(0, min(x^{r*}, v^d + y^L) − x^r)`, where `y` is the order placed this period. -/
def shipStar (xstar : ℝ) (s : SysState m.L) (y : ℝ) : ℝ :=
  max 0 (min xstar (s.2.1 + arrival s.1 y) - s.2.2)

/-- The stationary decision rule of `π*` (p. 825): order according to the depot rule `σd`, ship
according to the modified critical-number rule. -/
def sigmaStar (σd : DepotState m.L → ℝ) (xstar : ℝ) (s : SysState m.L) : ℝ × ℝ :=
  (σd (s.1, s.2.1), m.shipStar xstar s (σd (s.1, s.2.1)))

end Model

end FZEchelon.AverageCost


