-- Prove2me | Definitions.Def_PerishableReturns_Coordination_Model
-- name    : PerishableReturns_Coordination_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:24:21.951582+00:00
-- url     : https://prove2.me/theorems/29273075-992f-4574-a1e0-4c49ea7c4ed8
-- title:
--   Pasternack's model: costs, admissible pricing and return policies (1)–(2), demand laws, expected profits (3), (6), (8), optimal orders and channel coordination
-- statement:
--   This file sets up the single-period manufacturer–retailer model of Pasternack (1985), "The Model", pp. 169–171.
--
--   **Costs.** A manufacturer produces a perishable item at cost $c$ per unit; leftover units have salvage value $c_3$ per unit; the retailer sells at the fixed price $p$. Each unit of unmet demand costs the retailer a goodwill penalty $g \ge 0$ and the manufacturer an additional goodwill penalty $g_1 \ge 0$; the total goodwill cost is $g_2 = g + g_1$. These data satisfy $c_3 < c < p$, the part of relationship (1) that does not involve the manufacturer's policy.
--
--   **Policies.** The manufacturer's policy is a triple $(c_1, c_2, R)$: the retailer pays $c_1$ per unit ordered, and may return up to the fraction $R$ of its order $Q$ for a credit of $c_2$ per unit. The policy is *admissible* when relationships (1) and (2) of the paper hold,
--   $$c_3 < c < c_1 < p, \qquad c_3 < c_2 \le c_1 < p,$$
--   and $0 \le R \le 1$.
--
--   **Demand.** Demand $X$ is a random variable with law $D$, a probability measure on $[0,\infty)$ with finite mean. Its distribution function is $F(k) = D((-\infty,k])$.
--
--   **Expected profits.** For an order (or production) quantity $Q$:
--
--   1. the company store's (integrated system's) expected profit, equation (3),
--   $$EP_T(Q) = -cQ + \int_0^Q [xp + (Q-x)c_3]\,dF(x) + \int_Q^\infty [pQ - g_2(x-Q)]\,dF(x);$$
--   2. the independent retailer's expected profit, equation (6),
--   $$EP_R(Q) = -Qc_1 + \int_0^{(1-R)Q} [xp + RQc_2 + ((1-R)Q - x)c_3]\,dF(x) + \int_{(1-R)Q}^Q [xp + (Q-x)c_2]\,dF(x) + \int_Q^\infty [pQ - (x-Q)g]\,dF(x);$$
--   3. the manufacturer's expected profit when the retailer orders $Q$, equation (8),
--   $$EP_M(Q) = Q(c_1 - c) - \int_0^{(1-R)Q} RQ(c_2 - c_3)\,dF(x) - \int_{(1-R)Q}^Q (Q-x)(c_2-c_3)\,dF(x) - \int_Q^\infty (x-Q)g_1\,dF(x).$$
--
--   **Optimal orders and coordination.** A quantity $Q$ is an *optimal order* for an expected-profit function $\pi$ when $Q \ge 0$ and $\pi(Q) \ge \pi(Q')$ for every $Q' \ge 0$. The channel is *coordinated* by the policy $(c_1,c_2,R)$ (p. 171) when the retailer's optimal orders for $EP_R$ are exactly the company store's optimal orders for $EP_T$.
--
--   These objects are shared by every statement of the mission: the first-order conditions (5) and (7), the coordination criteria (10) and (11), and Theorem 3.
--
--   **Formalization Note.** The paper describes demand by a density $f$; here demand is a probability measure `D` on $\mathbb R$ with `D (Iio 0) = 0` and an integrable identity (finite mean), and $F$ is Mathlib's `cdf D`. The paper's density is the separate hypothesis `NullSingletonClass D` (no atoms, so $F$ is continuous), stated on each theorem that needs it. Because `D` charges no negative number, the paper's integrals from $0$ equal Lean's integrals over $\mathbb R$. The integrands are the paper's piecewise integrands written with `if`; at the breakpoints $x = (1-R)Q$ and $x = Q$ adjacent pieces agree, so the choice of $\le$ versus $<$ is immaterial. The nonnegativity of $g$ and $g_1$ is not stated in the paper but is implicit (they are costs) and is needed for Theorems 2 and 3. $R$ is the returnable fraction in $[0,1]$, as (6) uses it. Coordination is stated as equality of the two sets of optimal orders, the paper's definition through the quantities ordered, not as equality of first-order conditions.
-- source:
--   Pasternack, Optimal Pricing and Return Policies for Perishable Commodities, Marketing Science 4(2) (1985), The Model, (1)–(3), (6), (8), pp. 169–171, and the definition of coordination, p. 171

import Mathlib

namespace PerishableReturns.Coordination

open MeasureTheory ProbabilityTheory

/-- The cost data of "The Model" (Pasternack 1985, pp. 169–170) that do not belong to the
manufacturer's policy: manufacturing cost `c`, salvage value `c3`, retail price `p`, goodwill
costs `g` (retailer) and `g1` (manufacturer, additional). The part `c3 < c < p` of (1) is a
field; the goodwill costs are nonnegative (implicit in the paper: they are costs). -/
structure Costs where
  c : ℝ
  c3 : ℝ
  p : ℝ
  g : ℝ
  g1 : ℝ
  c3_lt_c : c3 < c
  c_lt_p : c < p
  g_nonneg : 0 ≤ g
  g1_nonneg : 0 ≤ g1

namespace Costs

/-- `g2 = g + g1`, the total goodwill cost (p. 170). -/
def g2 (K : Costs) : ℝ := K.g + K.g1

/-- The manufacturer's policy `(c1, c2, R)` satisfies (1)–(2) (p. 170), `c < c1 < p` and
`c3 < c2 ≤ c1`, and the returnable fraction lies in `[0, 1]`. -/
def Admissible (K : Costs) (c1 c2 R : ℝ) : Prop :=
  K.c < c1 ∧ c1 < K.p ∧ K.c3 < c2 ∧ c2 ≤ c1 ∧ 0 ≤ R ∧ R ≤ 1

end Costs

/-- A demand law as in "The Model": a probability law on `[0, ∞)` with finite mean. The paper's
density `f` is the further hypothesis `NullSingletonClass D` (no atoms: every singleton is null), added where a theorem needs it. -/
structure IsDemand (D : Measure ℝ) : Prop where
  isProb : IsProbabilityMeasure D
  nonneg : D (Set.Iio 0) = 0
  integrable : Integrable (fun x : ℝ => x) D

/-- (3): the company store's expected profit `EP_T(Q)`. -/
noncomputable def EPT (K : Costs) (D : Measure ℝ) (Q : ℝ) : ℝ :=
  -K.c * Q + ∫ x, (if x ≤ Q then x * K.p + (Q - x) * K.c3
                   else K.p * Q - K.g2 * (x - Q)) ∂D

/-- (6): the retailer's expected profit `EP_R(Q)` under the policy `(c1, c2, R)`. -/
noncomputable def EPR (K : Costs) (c1 c2 R : ℝ) (D : Measure ℝ) (Q : ℝ) : ℝ :=
  -Q * c1 + ∫ x, (if x ≤ (1 - R) * Q then x * K.p + R * Q * c2 + ((1 - R) * Q - x) * K.c3
                  else if x ≤ Q then x * K.p + (Q - x) * c2
                  else K.p * Q - (x - Q) * K.g) ∂D

/-- (8): the manufacturer's expected profit `EP_M(Q)` when the retailer orders `Q`. -/
noncomputable def EPM (K : Costs) (c1 c2 R : ℝ) (D : Measure ℝ) (Q : ℝ) : ℝ :=
  Q * (c1 - K.c) - ∫ x, (if x ≤ (1 - R) * Q then R * Q * (c2 - K.c3)
                         else if x ≤ Q then (Q - x) * (c2 - K.c3)
                         else (x - Q) * K.g1) ∂D

/-- `Q` is an optimal order quantity for the expected profit `f`: `Q ≥ 0` and `Q` maximizes `f`
on `[0, ∞)`. -/
def IsOptimalOrder (f : ℝ → ℝ) (Q : ℝ) : Prop :=
  0 ≤ Q ∧ IsMaxOn f (Set.Ici 0) Q

/-- The channel is coordinated (p. 171): the independent retailer's optimal orders under the
policy `(c1, c2, R)` are exactly the company store's optimal orders. -/
def Coordinates (K : Costs) (c1 c2 R : ℝ) (D : Measure ℝ) : Prop :=
  ∀ Q : ℝ, IsOptimalOrder (EPR K c1 c2 R D) Q ↔ IsOptimalOrder (EPT K D) Q

end PerishableReturns.Coordination


