-- Prove2me | Definitions.Def_PerishableReturns_Suboptimal_Model
-- name    : PerishableReturns_Suboptimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:23:43.620987+00:00
-- url     : https://prove2.me/theorems/4255738d-6c22-4988-9baa-e79b632d5190
-- title:
--   Pasternack's model: costs, demand, return policies, expected profits, and optimal orders
-- statement:
--   A manufacturer produces a perishable item at unit cost $c$ and sells it to a retailer at wholesale price $c_1$. The retailer sells at fixed price $p$. Unsold units have salvage value $c_3$; a returned unit earns credit $c_2$. The retailer incurs goodwill cost $g$ for each unit of unmet demand, and the manufacturer incurs an additional $g_1$. Write $g_2=g+g_1$. A return policy allows a fraction $R$ of the ordered quantity $Q$ to be returned. Admissible data satisfy $c_3<c<c_1<p$, $c_3<c_2\le c_1$, and $0\le R\le1$.
--
--   Demand $X$ has a probability law $D$ on $[0,\infty)$ with finite mean. The integrated company store, retailer and manufacturer have expected profits $EP_T(Q)$, $EP_R(Q)$ and $EP_M(Q)$ from equations (3), (6) and (8), respectively. For example, the company store's expected profit is
--
--   $$EP_T(Q)=-cQ+\mathbb E\!\left[\begin{cases}Xp+(Q-X)c_3,&X\le Q,\\pQ-g_2(X-Q),&X>Q.\end{cases}\right]$$
--
--   An optimal order maximizes the relevant expected profit over $Q\ge0$. A policy coordinates the channel when the retailer's set of optimal orders equals the integrated company's set. These definitions provide the common model for the mission's first order conditions and its two failure results.
--
--   **Formalization Note** The paper writes a density $f$; the definition uses a probability measure, with absence of atoms assumed by the theorems that use a continuous distribution function. Finite mean ensures that the piecewise linear profit integrands are integrable. The paper calls $g$ and $g_1$ costs, and they are taken nonnegative. The integrands follow the paper's three pieces; adjacent pieces agree at the breakpoints. $R$ is a fraction, and the optimal-order predicate explicitly includes $Q\ge0$. Coordination compares whole sets of maximizers.
-- source:
--   Pasternack, Optimal Pricing and Return Policies for Perishable Commodities, Marketing Science 4(2) (1985), The Model, (1)–(3), (6), (8), pp. 169–171

import Mathlib

namespace PerishableReturns.Suboptimal

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

end PerishableReturns.Suboptimal


