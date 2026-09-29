-- Prove2me | Definitions.Def_ZhengQR_CostBounds_Model
-- name    : ZhengQR_CostBounds_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:55:38.429551+00:00
-- url     : https://prove2.me/theorems/48d02711-c0dc-4123-8560-da39696ba9b1
-- title:
--   The stochastic (Q, r) model: parameters λ, L, K, h, p, leadtime demand D, newsvendor cost G, EOQ cost G_d and Q*_d
-- statement:
--   The continuous-review inventory model of Zheng (1992), §1–§3. Demands arrive at rate $\lambda>0$; replenishment orders arrive after a fixed leadtime $L>0$; each order costs $K>0$; holding and backorder costs accrue at rates $h>0$ and $p>0$ per unit per unit time. The leadtime demand $D$ has distribution $\mu$, a probability measure on $\mathbb R$ concentrated on $[0,\infty)$, with finite mean $E(D)=\lambda L$.
--
--   1. **Newsvendor (inventory) cost rate** (p. 88):
--   $$G(y)=E\big[h(y-D)^+ + p(D-y)^+\big].$$
--   Standing assumption (p. 90): $G$ attains its minimum at a unique point $y^0$.
--   2. **EOQ inventory cost rate** (p. 94), the same cost for demand constant at $\lambda L$:
--   $$G_d(y)=h(y-\lambda L)^+ + p(\lambda L-y)^+.$$
--   3. **EOQ order quantity** (Eq. (20), p. 94):
--   $$Q^*_d=\sqrt{\frac{2\lambda K(h+p)}{hp}}.$$
--
--   The structure `QRModel` bundles the parameters, the demand distribution and every standing assumption, so that each theorem of the mission is stated for an arbitrary model satisfying them.
--
--   **Formalization Note** The paper states positivity of $L$ ("positive fixed leadtime") and uses $K>0$ implicitly. Nonnegativity of demand, integrability of $D$ and $E(D)=\lambda L$ are the paper's conventions (p. 94, and Eq. (3) integrates $F$ from $0$). No density is assumed. $G_d$ and $Q^*_d$ are explicit formulas; that $Q^*_d$ is the EOQ model's optimum is a milestone theorem (Eqs. (18), (20)).
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 88 (model, G), p. 90 (unique minimizer y⁰), p. 94 (E(D) = λL, G_d, Eq. (20))

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery

namespace ZhengQR.CostBounds

open MeasureTheory

/-- p. 88: the expected inventory-cost rate `G(y) = E[h (y − D)⁺ + p (D − y)⁺]` when the leadtime
demand `D` has distribution `μ`. -/
noncomputable def newsvendorCost (μ : Measure ℝ) (h p y : ℝ) : ℝ :=
  ∫ x, (h * max (y - x) 0 + p * max (x - y) 0) ∂μ

/-- p. 94: the inventory-cost rate of the deterministic (EOQ) model,
`G_d(y) = h (y − λL)⁺ + p (λL − y)⁺`. -/
noncomputable def eoqInvCost (lam L h p y : ℝ) : ℝ :=
  h * max (y - lam * L) 0 + p * max (lam * L - y) 0

/-- Eq. (20), p. 94: the EOQ order quantity `Q*_d = √(2λK(h + p)/(hp))`. -/
noncomputable def eoqQty (lam K h p : ℝ) : ℝ :=
  Real.sqrt (2 * lam * K * (h + p) / (h * p))

/-- The standing assumptions of §1–§2 (pp. 88–90): demand rate `λ`, leadtime `L`, fixed ordering
cost `K`, holding and backorder cost rates `h`, `p`, all positive; the leadtime demand `D` has
distribution `μ`, a probability measure on `ℝ` concentrated on `[0, ∞)`, integrable, with mean
`E(D) = λL`; and `G` attains its minimum at a unique point (p. 90). -/
structure QRModel where
  lam : ℝ
  L : ℝ
  K : ℝ
  h : ℝ
  p : ℝ
  μ : Measure ℝ
  lam_pos : 0 < lam
  L_pos : 0 < L
  K_pos : 0 < K
  h_pos : 0 < h
  p_pos : 0 < p
  isProb : IsProbabilityMeasure μ
  integrable_id : Integrable (fun x : ℝ => x) μ
  mean_eq : ∫ x, x ∂μ = lam * L
  demand_nonneg : ∀ᵐ x ∂μ, 0 ≤ x
  unique_min : ∃! y : ℝ, ∀ z : ℝ, newsvendorCost μ h p y ≤ newsvendorCost μ h p z

namespace QRModel

/-- The stochastic model's inventory-cost rate `G`. -/
noncomputable def G (M : QRModel) : ℝ → ℝ := newsvendorCost M.μ M.h M.p

/-- The EOQ model's inventory-cost rate `G_d` (same parameters, demand constant at `λL`). -/
noncomputable def Gd (M : QRModel) : ℝ → ℝ := eoqInvCost M.lam M.L M.h M.p

/-- The EOQ order quantity `Q*_d` of the model. -/
noncomputable def Qd (M : QRModel) : ℝ := eoqQty M.lam M.K M.h M.p

end QRModel

end ZhengQR.CostBounds


