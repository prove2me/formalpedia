-- Prove2me | Definitions.Def_ZhengQR_OrderQty_newsvendorCost
-- name    : ZhengQR_OrderQty_newsvendorCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:48:38.899558+00:00
-- url     : https://prove2.me/theorems/0da1bd86-4abd-4af4-a1ff-08dec718bc45
-- title:
--   The leadtime-demand assumptions, the newsvendor cost $G$, the EOQ cost $G_d$ and the EOQ quantity $Q^*_d$
-- statement:
--   This file fixes the two inventory-cost rates compared throughout Zheng's analysis of the continuous-review $(Q, r)$ inventory system, and the closed-form EOQ order quantity.
--
--   **Leadtime demand.** Let $\lambda > 0$ be the demand rate and $L > 0$ the replenishment leadtime. The leadtime demand $D$ is a random variable with distribution $\mu$ on $\mathbb{R}$. We say that $\mu$ is an admissible *leadtime-demand distribution* for $(\lambda, L)$ when
--
--   1. $\mu$ is a probability measure;
--   2. $D$ is integrable, $\mathbb{E}|D| < \infty$;
--   3. its mean is $\mathbb{E}(D) = \lambda L$;
--   4. $D \ge 0$ almost surely.
--
--   **Newsvendor cost.** With holding cost rate $h$ and backorder penalty rate $p$, the expected rate at which inventory costs accumulate at time $t + L$ when the inventory position at time $t$ is $y$ is
--
--   $$G(y) = \mathbb{E}\big[h\,(y - D)^+ + p\,(D - y)^+\big].$$
--
--   **EOQ cost.** The deterministic EOQ model with backorders is the extreme case in which the leadtime demand equals $\lambda L$; its cost rate is the V-shaped function
--
--   $$G_d(y) = h\,(y - \lambda L)^+ + p\,(\lambda L - y)^+.$$
--
--   **EOQ order quantity.** For a fixed ordering cost $K$,
--
--   $$Q^*_d = \sqrt{\frac{2\lambda K (h + p)}{hp}}.$$
--
--   These are the primitive data of the model: every other object of the mission ($c(Q, r)$, $r(Q)$, $H$, $A$, $H_0$, $Q^*$) is built from $G$ or $G_d$.
--
--   **Formalization Note** The assumptions on $\mu$ are bundled in the proposition `IsLeadtimeDemand lam L μ`. No density is assumed, so discrete demand distributions (e.g. Poisson, as in the paper's own numerical study) are allowed. $Q^*_d$ is given by its closed form (Eq. (20)); that it is the optimal order quantity of the EOQ model is a separate theorem of this mission.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 88 (model, definition of G), p. 94 (E(D) = λL, G_d, Eq. (20))

import Mathlib

namespace ZhengQR.OrderQty

open MeasureTheory

/-- The standing assumptions of Zheng (1992), pp. 88 and 94, on the distribution `μ` of the
leadtime demand `D`: `μ` is a probability measure on `ℝ`, `D` is integrable, its mean is
`E(D) = λL`, and demand is nonnegative. -/
structure IsLeadtimeDemand (lam L : ℝ) (μ : Measure ℝ) : Prop where
  isProb : IsProbabilityMeasure μ
  integrable : Integrable (fun x : ℝ => x) μ
  mean_eq : ∫ x, x ∂μ = lam * L
  nonneg : ∀ᵐ x ∂μ, 0 ≤ x

/-- The expected inventory cost rate of the stochastic model (p. 88):
`G(y) = E[h (y - D)⁺ + p (D - y)⁺]`, where `D ∼ μ` is the leadtime demand, `h` the holding cost
rate and `p` the backorder penalty rate. -/
noncomputable def newsvendorCost (h p : ℝ) (μ : Measure ℝ) (y : ℝ) : ℝ :=
  ∫ x, (h * max (y - x) 0 + p * max (x - y) 0) ∂μ

/-- The inventory cost rate of the deterministic EOQ model (p. 94):
`G_d(y) = h (y - λL)⁺ + p (λL - y)⁺`, i.e. `G` for a leadtime demand equal to `λL`. -/
noncomputable def eoqCost (lam L h p : ℝ) (y : ℝ) : ℝ :=
  h * max (y - lam * L) 0 + p * max (lam * L - y) 0

/-- Eq. (20), p. 94: the EOQ order quantity with backorders, `Q*_d = √(2λK(h + p)/(hp))`. -/
noncomputable def eoqQty (lam K h p : ℝ) : ℝ :=
  Real.sqrt (2 * lam * K * (h + p) / (h * p))

end ZhengQR.OrderQty


