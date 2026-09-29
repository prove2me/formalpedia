-- Prove2me | Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
-- name    : ZhengQR_EOQHeuristic_stochasticModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:38:23.985115+00:00
-- url     : https://prove2.me/theorems/3ee3183e-3d19-4991-915e-b4958d0e991e
-- title:
--   The stochastic $(Q, r)$ model: newsvendor cost $G$, EOQ cost $G_d$, EOQ quantity $Q^*_d$ and the standing assumptions
-- statement:
--   A single item is controlled by a continuous-review $(Q, r)$ policy. Demand arrives at rate $\lambda > 0$, replenishment orders arrive after a fixed leadtime $L > 0$, stockouts are backordered, inventory is held at cost rate $h > 0$ per unit and backorders are penalised at cost rate $p > 0$ per unit. Let $D \ge 0$ be the leadtime demand, with distribution $\mu$ and mean $E(D) = \lambda L$.
--
--   This file defines three objects.
--
--   1. The **newsvendor cost** (the expected inventory-cost rate at inventory position $y$):
--   $$G(y) = E\big[h\,(y - D)^+ + p\,(D - y)^+\big] = \int \big(h\max(y-x,0) + p\max(x-y,0)\big)\,\mu(dx).$$
--   2. The inventory-cost rate of the deterministic (EOQ) model, in which the leadtime demand is the constant $\lambda L$:
--   $$G_d(y) = h\,(y - \lambda L)^+ + p\,(\lambda L - y)^+ .$$
--   3. The **EOQ order quantity with backorders**, for a fixed ordering cost $K$:
--   $$Q^*_d = \sqrt{\frac{2\lambda K (h+p)}{hp}} .$$
--
--   Finally, the predicate `IsQRModel` collects the standing assumptions of the paper: $\lambda, L, h, p > 0$; $\mu$ is a probability measure concentrated on $[0,\infty)$ with finite mean equal to $\lambda L$; and $G$ attains its minimum at a unique point $y^0$ ("For simplicity, we assume that $G(y)$ achieves its minimum at a unique point, say, $y^0$", p. 90).
--
--   These are the primitive data every statement of the mission is phrased in.
--
--   **Formalization Note** No density of $D$ is assumed, so discrete (e.g. Poisson) leadtime demand is covered. The fixed ordering cost $K$ is not part of `IsQRModel`; each statement assumes $K > 0$ separately. Finite mean is stated as integrability of the identity under $\mu$, which also makes the integrand of $G$ integrable.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 88 (model and definition of G), p. 90 (unique minimizer y⁰), p. 94 (G_d, E(D) = λL, Eq. (20))

import Mathlib

open MeasureTheory

namespace ZhengQR.EOQHeuristic

/-- The expected inventory-cost rate `G(y) = E[h (y − D)⁺ + p (D − y)⁺]` (p. 88), where the
leadtime demand `D` has distribution `μ`, `h` is the holding and `p` the backorder cost rate. -/
noncomputable def newsvendorCost (μ : Measure ℝ) (h p y : ℝ) : ℝ :=
  ∫ x, (h * max (y - x) 0 + p * max (x - y) 0) ∂μ

/-- The inventory-cost rate of the deterministic (EOQ) model, p. 94:
`G_d(y) = h (y − λL)⁺ + p (λL − y)⁺`. -/
noncomputable def eoqCost (lam L h p y : ℝ) : ℝ :=
  h * max (y - lam * L) 0 + p * max (lam * L - y) 0

/-- The EOQ order quantity with backorders, Eq. (20), p. 94: `Q*_d = √(2λK(h + p)/(hp))`. -/
noncomputable def eoqQty (lam K h p : ℝ) : ℝ :=
  Real.sqrt (2 * lam * K * (h + p) / (h * p))

/-- The standing assumptions of the stochastic `(Q, r)` model (pp. 88, 90, 94): positive demand
rate `lam`, leadtime `L`, holding cost `h` and backorder cost `p`; a leadtime demand distribution
`μ` that is a probability measure on `[0, ∞)` with finite mean `E(D) = λL`; and a newsvendor cost
`G` that attains its minimum at a unique point `y⁰`. -/
structure IsQRModel (lam L h p : ℝ) (μ : Measure ℝ) : Prop where
  lam_pos : 0 < lam
  L_pos : 0 < L
  h_pos : 0 < h
  p_pos : 0 < p
  isProb : IsProbabilityMeasure μ
  integrable : Integrable (fun x : ℝ => x) μ
  mean : ∫ x, x ∂μ = lam * L
  nonneg : ∀ᵐ x ∂μ, 0 ≤ x
  unique_min : ∃! y : ℝ, ∀ z : ℝ, newsvendorCost μ h p y ≤ newsvendorCost μ h p z

end ZhengQR.EOQHeuristic


