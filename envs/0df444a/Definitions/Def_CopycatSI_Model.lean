-- Prove2me | Definitions.Def_CopycatSI_Model
-- name    : CopycatSI_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:33.377912+00:00
-- url     : https://prove2.me/theorems/94511558-1c13-420e-b8d9-0a146aacaa28
-- title:
--   Two-period brand-name channel with copycat entry: demands, sales, inventory and profits ($\gamma=0$)
-- statement:
--   A supplier sells a brand-name product through a retailer over two periods. In each period a unit mass of short-lived customers arrives; a customer's valuation $\theta$ of the brand-name product is uniform on $[0,1]$, and each customer buys at most one unit, in its own period. In period 2 copycats enter, and a customer of type $\theta$ values the copycat product at $\beta\theta$ with $0\le\beta<1$.
--
--   **Demands.** At the period-1 price $p_1$ a customer buys iff $\theta-p_1\ge 0$, so
--   $$
--   D_1(p_1)=\Pr\{\theta\in[0,1]:\ \theta-p_1\ge 0\}.
--   $$
--   In period 2, at brand price $p_2$ and copycat price $p_C$, a customer buys the brand-name product iff $\theta-p_2\ge 0$ and $\theta-p_2\ge\beta\theta-p_C$, and the copycat iff $\beta\theta-p_C\ge 0$ and $\beta\theta-p_C>\theta-p_2$:
--   $$
--   D_2(p_2,p_C)=\Pr\{\theta:\ 0\le\theta-p_2,\ \beta\theta-p_C\le\theta-p_2\},\qquad D_C(p_2,p_C)=\Pr\{\theta:\ 0\le\beta\theta-p_C,\ \theta-p_2<\beta\theta-p_C\}.
--   $$
--
--   **Quantities and profits.** The wholesale prices are $(w_1,w_2)$, the retailer orders $(q_1,q_2)$ and sets $(p_1,p_2)$. She sells $s_1=\min(q_1,D_1(p_1))$ and carries $I=q_1-s_1$ into period 2 at unit holding cost $h$; she sells $s_2=\min(I+q_2,D_2(p_2,p_C))$, and the copycats sell $s_C=D_C(p_2,p_C)$. The profits are
--   $$
--   \pi_S=w_1q_1+w_2q_2,\qquad \pi_R=p_1s_1+p_2s_2-w_1q_1-w_2q_2-hI,\qquad \pi_C=p_Cs_C.
--   $$
--   Under the paper's $h=\infty$ the retailer cannot carry inventory: the period-1 leftover is lost, $I=0$ and no holding cost is paid.
--
--   These are the primitives on which every equilibrium statement of the mission is made; the closed forms of Tables 1 and 2 are never used as definitions.
--
--   **Formalization Note** The model is built with no network externality ($\gamma=0$), the case of every result in this mission. $\Pr$ is Lebesgue measure as a real number. The holding regime is `Holding.finite h` or `Holding.infinite` (the paper's $h=\infty$). Production costs are zero. The copycats are not stock-constrained and their demand is not rationed by the retailer's stock. A play is a record `Plan` of $(w_1,w_2,q_1,q_2,p_1,p_2,p_C)$, and `Plan.outcome` lists the entries the paper's tables report.
-- source:
--   Jin–Wu–Chen, Managing Competition from Within and Outside: Using Strategic Inventory and Network Externality to Combat Copycats, SSRN 3826955 (version of 2023-05-17), §2 Model, pp.5–7 (customers and valuations p.6; network externality p.6; sequence of events and holding cost p.7); §2.1 (h = ∞), p.7

import Mathlib

open MeasureTheory

namespace CopycatSI

/-- The retailer's inventory regime between the two selling periods.
Jin–Wu–Chen, *Managing Competition from Within and Outside*, SSRN 3826955 (version of
2023-05-17), §2, p.7 ("the retailer incurs a unit cost h for carrying inventory across periods")
and §2.1, p.7 ("h = ∞").

* `finite h`: units left over after period 1 are carried into period 2 at unit cost `h`;
* `infinite`: the paper's `h = ∞`; the retailer cannot hold inventory, and units left over after
  period 1 are lost (the paper's gloss "the retailer cannot hold inventory (h = ∞)", §4, p.12).

**Formalization Note** `h = ∞` is not a real number; it is the separate constructor `infinite`,
not "a large `h`". -/
inductive Holding where
  | finite (h : ℝ)
  | infinite

/-- Period-1 demand for the brand-name product at retail price `p₁`, §2, pp.6–7.
A unit mass of short-lived customers arrives; a customer's valuation `θ` of the brand-name product
is uniform on `[0, 1]`, and the customer buys one unit iff `θ − p₁ ≥ 0`. The demand is the
Lebesgue measure of `{θ ∈ [0, 1] : θ − p₁ ≥ 0}`.

**Formalization Note** The measure is taken as a real number (`toReal` of a finite measure). -/
noncomputable def demand1 (p1 : ℝ) : ℝ :=
  (volume {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ θ - p1}).toReal

/-- Period-2 demand for the brand-name product at brand price `p₂` and copycat price `p_C`,
copycat quality `β`, §2, pp.6–7, with no network externality (`γ = 0`).
A customer of type `θ ~ U[0, 1]` has utility `θ − p₂` for the brand-name product and `βθ − p_C`
for the copycat product. The customer buys the brand-name product iff its utility is
non-negative and at least the copycat's.

**Formalization Note** The model is built with `γ = 0` (the brand utility `θ + γ s₁ − p₂` of p.6
with `γ = 0`): every result formalized in this mission (Propositions 1 and 2) assumes `γ = 0`.
A customer indifferent between the two products buys the brand-name product; for `β < 1` such
customers form a null set. -/
noncomputable def demand2 (β p2 pC : ℝ) : ℝ :=
  (volume {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ θ - p2 ∧ β * θ - pC ≤ θ - p2}).toReal

/-- Period-2 demand for the copycat product, §2, pp.6–7 (`γ = 0`): the customers whose copycat
utility `βθ − p_C` is non-negative and strictly greater than their brand utility `θ − p₂`.

**Formalization Note** The copycats are not stock-constrained, and their demand is computed from
the two prices only: customers who are not served because the retailer runs out of stock do not
switch to the copycat (the paper's model has no rationing). -/
noncomputable def demandC (β p2 pC : ℝ) : ℝ :=
  (volume {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ β * θ - pC ∧ θ - p2 < β * θ - pC}).toReal

/-- The units carried into period 2 out of a period-1 leftover `x`: `x` itself when holding is
possible, `0` under `h = ∞` (the leftover is lost). -/
def carried : Holding → ℝ → ℝ
  | .finite _, x => x
  | .infinite, _ => 0

/-- The retailer's holding cost of carrying `I` units: `h · I` (§2, p.7), and `0` under `h = ∞`
(nothing is carried). -/
def holdingCost : Holding → ℝ → ℝ
  | .finite h, I => h * I
  | .infinite, _ => 0

/-- A complete play of the game: the wholesale prices `(w₁, w₂)`, the retailer's orders
`(q₁, q₂)` and prices `(p₁, p₂)`, and the copycats' price `p_C` (§2, p.7). -/
structure Plan where
  w1 : ℝ
  w2 : ℝ
  q1 : ℝ
  q2 : ℝ
  p1 : ℝ
  p2 : ℝ
  pC : ℝ

namespace Plan

/-- Period-1 sales `s₁ = min(q₁, D₁(p₁))`. -/
noncomputable def s1 (x : Plan) : ℝ := min x.q1 (demand1 x.p1)

/-- Inventory carried into period 2, `I = q₁ − s₁` (`0` under `h = ∞`). -/
noncomputable def inv (H : Holding) (x : Plan) : ℝ := carried H (x.q1 - x.s1)

/-- Period-2 brand sales `s₂ = min(I + q₂, D₂(p₂, p_C))`: the retailer sells from her inventory
and her period-2 order. -/
noncomputable def s2 (β : ℝ) (H : Holding) (x : Plan) : ℝ :=
  min (x.inv H + x.q2) (demand2 β x.p2 x.pC)

/-- Copycat sales `s_C = D_C(p₂, p_C)`. -/
noncomputable def sC (β : ℝ) (x : Plan) : ℝ := demandC β x.p2 x.pC

/-- The supplier's profit `π_S = w₁q₁ + w₂q₂` (zero production cost). -/
def profitS (x : Plan) : ℝ := x.w1 * x.q1 + x.w2 * x.q2

/-- The retailer's profit `π_R = p₁s₁ + p₂s₂ − w₁q₁ − w₂q₂ − h·I` (unsold units are worth `0`). -/
noncomputable def profitR (β : ℝ) (H : Holding) (x : Plan) : ℝ :=
  x.p1 * x.s1 + x.p2 * x.s2 β H - x.w1 * x.q1 - x.w2 * x.q2 - holdingCost H (x.inv H)

/-- The copycats' profit `π_C = p_C · s_C` (zero production cost). -/
noncomputable def profitC (β : ℝ) (x : Plan) : ℝ := x.pC * x.sC β

end Plan

/-- The record of a play that the paper's Tables 1 and 2 report (pp.8–9): wholesale prices, orders,
inventory, sales, prices and profits. -/
structure Outcome where
  w1 : ℝ
  w2 : ℝ
  q1 : ℝ
  q2 : ℝ
  inv : ℝ
  s1 : ℝ
  s2 : ℝ
  sC : ℝ
  p1 : ℝ
  p2 : ℝ
  pC : ℝ
  piS : ℝ
  piR : ℝ
  piC : ℝ

/-- The outcome record of a play `x`, with copycat quality `β` and holding regime `H`. -/
noncomputable def Plan.outcome (β : ℝ) (H : Holding) (x : Plan) : Outcome where
  w1 := x.w1
  w2 := x.w2
  q1 := x.q1
  q2 := x.q2
  inv := x.inv H
  s1 := x.s1
  s2 := x.s2 β H
  sC := x.sC β
  p1 := x.p1
  p2 := x.p2
  pC := x.pC
  piS := x.profitS
  piR := x.profitR β H
  piC := x.profitC β

end CopycatSI


