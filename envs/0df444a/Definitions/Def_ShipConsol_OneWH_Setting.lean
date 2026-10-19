-- Prove2me | Definitions.Def_ShipConsol_OneWH_Setting
-- name    : ShipConsol_OneWH_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:43.178298+00:00
-- url     : https://prove2.me/theorems/abc39269-a5ab-467d-a948-1dce980f6bd0
-- title:
--   §3–§4, pp. 8–12 — one-warehouse fixed-cost DP (2)–(3): V_t(z), V_t(∞), ship/hold optimality
-- statement:
--   This file defines the one-warehouse, fixed-cost shipment-consolidation dynamic program of Wei, Kapuscinski and Jasin, in the reduced form (2)–(3) of their §4.
--
--   **Data.** A fixed shipping cost $F$, where $F(p)$ is the cost of delivering a package in $p$ periods (used at integer arguments $p \ge 1$); an arrival probability $\alpha \in [0,1]$ (the probability that at least one new order arrives in a period); and a delivery deadline $d \ge 1$ (every order must be delivered within $d$ periods of its arrival).
--
--   **Time and state.** Time is counted backward: $t$ is the number of periods to go, period $1$ is the last. The state $z \in \{1,\dots,d\}$ is the smallest slack time among pending orders, and the state $\infty$ means that no order is pending.
--
--   **Value functions.** $V_t(z)$ and $V_t(\infty)$ are defined by the recursion: for $t = 1$,
--   $$V_1(z) = F(z), \qquad V_1(\infty) = 0,$$
--   and for $t > 1$ and $1 \le z \le d$,
--   $$V_t(z) = \min\begin{cases} F(z) + V_t(\infty) & \text{(ship)}\\ V_{t-1}(z-1) & \text{(do not ship)}\end{cases}, \qquad V_t(\infty) = \alpha V_{t-1}(d) + (1-\alpha) V_{t-1}(\infty).$$
--   At $z = 1$ holding is infeasible (an order with slack $1$ must leave now; the paper's boundary condition $V_{t-1}(0) = \infty$), so $V_t(1) = F(1) + V_t(\infty)$.
--
--   **Optimal decisions.** Shipping all pending orders is *optimal* at $(t,z)$ if the ship branch attains the minimum, $V_t(z) = F(z) + V_t(\infty)$. Holding all pending orders is *optimal* at $(t,z)$ if it is feasible ($t \ge 2$ and $z \ge 2$) and the do-not-ship branch attains the minimum, $V_t(z) = V_{t-1}(z-1)$. With ties both decisions are optimal.
--
--   These objects are the model of every theorem in the mission.
--
--   **Formalization Note.** `valuePair F α d t` returns the pair $(z \mapsto V_t(z),\, V_t(\infty))$; `V` and `Vinf` are its components. $F$ is a function $\mathbb R \to \mathbb R$ evaluated at the real cast of the natural number $z$. The value $V_1(\infty) = 0$ is the last-period value of the paper's general DP (1) with nothing to ship. The case $t = 0$ (outside the horizon), and the values at $z = 0$ and $z > d$, are placeholders that no theorem of the mission uses. The paper's infinite boundary value is encoded as the forced shipment at $z = 1$.
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), §3 (time and slack p. 8; cost assumptions p. 9; boundary condition and V_1 of (1) p. 11), §4 DP (2)–(3), p. 12

import Mathlib

namespace ShipConsol.OneWH

/-- `valuePair F α d t = (fun z => V_t(z), V_t(∞))` for `t ≥ 1` periods to go (period 1 is the last),
the one-warehouse fixed-cost dynamic program (2)–(3) of Wei, Kapuscinski & Jasin, p. 12:
for `t > 1` and `1 ≤ z ≤ d`,
`V_t(z) = min {F(z) + V_t(∞) (ship), V_{t-1}(z - 1) (do not ship)}`,
`V_t(∞) = α V_{t-1}(d) + (1 - α) V_{t-1}(∞)`, and `V_1(z) = F(z)`.
`V_1(∞) = 0` (no pending order in the last period costs nothing, from (1), p. 11). At `z = 1` holding
is infeasible (boundary condition `V_{t-1}(0) = ∞`, p. 11), so `V_t(1) = F(1) + V_t(∞)`.
`t = 0` is outside the horizon, and values at `z = 0` or `z > d` are never used (junk). -/
noncomputable def valuePair (F : ℝ → ℝ) (α : ℝ) (d : ℕ) : ℕ → (ℕ → ℝ) × ℝ
  | 0 => (fun _ => 0, 0)
  | 1 => (fun z => F z, 0)
  | (t + 2) =>
      let prev := valuePair F α d (t + 1)
      let vInf := α * prev.1 d + (1 - α) * prev.2
      (fun z => if z ≤ 1 then F z + vInf else min (F z + vInf) (prev.1 (z - 1)), vInf)

/-- `V_t(z)`: optimal expected cost-to-go with `t` periods to go when the smallest slack time among
pending orders is `z`. -/
noncomputable def V (F : ℝ → ℝ) (α : ℝ) (d t z : ℕ) : ℝ := (valuePair F α d t).1 z

/-- `V_t(∞)`: optimal expected cost-to-go with `t` periods to go and no pending order. -/
noncomputable def Vinf (F : ℝ → ℝ) (α : ℝ) (d t : ℕ) : ℝ := (valuePair F α d t).2

/-- "Ship all pending orders" is an optimal decision at `(t, z)`: the Ship branch of (2) attains
`V_t(z)`. -/
def ShipOptimal (F : ℝ → ℝ) (α : ℝ) (d t z : ℕ) : Prop := V F α d t z = F z + Vinf F α d t

/-- "Hold all pending orders" is a feasible and optimal decision at `(t, z)`: there is a next period
(`t ≥ 2`), holding does not violate the deadline (`z ≥ 2`), and the Do-not-ship branch of (2)
attains `V_t(z)`. -/
def HoldOptimal (F : ℝ → ℝ) (α : ℝ) (d t z : ℕ) : Prop :=
  2 ≤ t ∧ 2 ≤ z ∧ V F α d t z = V F α d (t - 1) (z - 1)

end ShipConsol.OneWH


