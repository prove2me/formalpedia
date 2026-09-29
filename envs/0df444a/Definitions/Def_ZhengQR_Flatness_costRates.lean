-- Prove2me | Definitions.Def_ZhengQR_Flatness_costRates
-- name    : ZhengQR_Flatness_costRates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T02:02:52.005201+00:00
-- url     : https://prove2.me/theorems/2b0bd4f7-732f-48f0-93a0-076492d152b1
-- title:
--   The inventory cost rates G(y) = E[h(y − D)⁺ + p(D − y)⁺] of the stochastic model and G_d(y) of the EOQ model
-- statement:
--   Consider a single-item continuous-review inventory system with holding cost rate $h$ and backorder penalty rate $p$. Let $D$ be the leadtime demand, with distribution $\mu$ on $\mathbb{R}$. The **inventory cost rate** at inventory position $y$ is the expected holding-plus-backorder cost rate
--
--   $$G(y) = E\big[h(y-D)^+ + p(D-y)^+\big] = \int \big(h\,(y-x)^+ + p\,(x-y)^+\big)\,\mu(dx).$$
--
--   For the deterministic EOQ model with backorders, whose leadtime demand is the constant $\lambda L$ (demand rate $\lambda$, leadtime $L$), the same cost rate is
--
--   $$G_d(y) = h\,(y-\lambda L)^+ + p\,(\lambda L - y)^+ .$$
--
--   These two functions are the only model-specific inputs of the $(Q, r)$ analysis; every later object ($c$, $r(Q)$, $H$, $C$, $A$) is built from a cost rate $G$ in the same way.
--
--   **Formalization Note** $G$ is a Bochner integral, which Lean sets to $0$ for a non-integrable integrand; the model structure `QRModel` requires $\int |x|\,\mu(dx) < \infty$, under which the integrand is integrable for every $y$.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 88 (definition of G) and p. 94 (definition of G_d)

import Mathlib

namespace ZhengQR.Flatness

/-- Zheng (1992), p. 88: the expected inventory cost rate `G(y) = E[h(y - D)⁺ + p(D - y)⁺]`
of the stochastic `(Q, r)` model, where the leadtime demand `D` has distribution `μ`,
`h` is the holding cost rate and `p` the backorder penalty rate. -/
noncomputable def newsvendorCost (h p : ℝ) (μ : MeasureTheory.Measure ℝ) (y : ℝ) : ℝ :=
  ∫ x, (h * max (y - x) 0 + p * max (x - y) 0) ∂μ

/-- Zheng (1992), p. 94: the inventory cost rate of the deterministic EOQ model,
`G_d(y) = h(y - λL)⁺ + p(λL - y)⁺`, i.e. `G` for a leadtime demand constant at `λL`. -/
noncomputable def eoqCost (h p lam L : ℝ) (y : ℝ) : ℝ :=
  h * max (y - lam * L) 0 + p * max (lam * L - y) 0

end ZhengQR.Flatness


