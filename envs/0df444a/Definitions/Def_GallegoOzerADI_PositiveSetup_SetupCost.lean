-- Prove2me | Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost
-- name    : GallegoOzerADI_PositiveSetup_SetupCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:44:37.956375+00:00
-- url     : https://prove2.me/theorems/ebdcba2d-95ae-43fc-b390-53af0fba972a
-- title:
--   Set-up indicator $\delta$, the one-period ordering problem $\min_{y\ge x}\{K\delta(y-x)+V(y)\}$, and $H(x)$
-- statement:
--   Three objects attached to a single ordering decision with a fixed set-up cost $K$ and a cost-to-go function $V : \mathbb{R} \to \mathbb{R}$.
--
--   1. The **set-up indicator** $\delta(z) = 1$ if $z > 0$ and $\delta(z) = 0$ otherwise; an order of size $z$ costs $K\delta(z)$ in set-up.
--   2. The **optimal ordering cost** from the inventory position $x$,
--   $$
--   \min_{y \ge x}\bigl\{K\delta(y - x) + V(y)\bigr\},
--   $$
--   where $y$ is the order-up-to level ($y = x$ means no order). This is the right-hand side of the functional equation (8) of the paper for one period.
--   3. The **reorder gap**
--   $$
--   H(x) = K + \min_{y \ge x} V(y) - V(x).
--   $$
--   If $H(x) \le 0$ it is optimal to order from $x$; if $H(x) > 0$ it is not.
--
--   These objects are shared by the abstract results on the structure of $K$-convex cost-to-go functions (Lemma 2, Corollary 1) and by the dynamic program of the paper.
--
--   **Formalization Note** Both minima are written as infima over the order-up-to levels $y \ge x$. The definitions do not assert that the infima are attained; the theorems that use them state the attainment or the finiteness they need, under hypotheses (a global minimizer of $V$) that make the infima finite.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1347 (δ), p. 1349 Eq. (8), p. 1350 (definition of H_t)

import Mathlib

namespace GallegoOzerADI.PositiveSetup

/-- The set-up indicator `δ(z) = 1` if `z > 0` and `0` otherwise (p. 1347). -/
noncomputable def setupIndicator (z : ℝ) : ℝ := if 0 < z then 1 else 0

/-- The right-hand side of the functional equation (8) for a single period with set-up cost `K`
and cost-to-go `V` (p. 1349): `min_{y ≥ x} {K δ(y - x) + V y}`, written as an infimum over the
order-up-to levels `y ≥ x`. Attainment of the infimum is never part of this definition; it is
asserted by the theorems that use it. -/
noncomputable def orderCost (K : ℝ) (V : ℝ → ℝ) (x : ℝ) : ℝ :=
  ⨅ y : {y : ℝ // x ≤ y}, (K * setupIndicator ((y : ℝ) - x) + V y)

/-- The function `H(x) ≡ K + min_{y ≥ x} V(y) - V(x)` of p. 1350: ordering from `x` is optimal
when `H(x) ≤ 0` and not optimal when `H(x) > 0`. The minimum is written as an infimum over
`y ≥ x`. -/
noncomputable def reorderGap (K : ℝ) (V : ℝ → ℝ) (x : ℝ) : ℝ :=
  K + (⨅ y : {y : ℝ // x ≤ y}, V y) - V x

end GallegoOzerADI.PositiveSetup


