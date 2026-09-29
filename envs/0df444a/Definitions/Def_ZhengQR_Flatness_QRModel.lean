-- Prove2me | Definitions.Def_ZhengQR_Flatness_QRModel
-- name    : ZhengQR_Flatness_QRModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T02:03:49.148562+00:00
-- url     : https://prove2.me/theorems/c1b31763-fccb-4150-bcbe-9e7519b4d846
-- title:
--   The stochastic (Q, r) model of Zheng (1992) with its standing assumptions, and its EOQ counterpart
-- statement:
--   A **$(Q, r)$ model** consists of a demand rate $\lambda>0$, a fixed leadtime $L>0$, a fixed ordering cost $K>0$, a holding cost rate $h>0$, a backorder penalty rate $p>0$, and the distribution $\mu$ of the leadtime demand $D$, subject to:
--
--   1. $\mu$ is a probability measure with finite mean, $D \ge 0$ almost surely, and $E(D) = \lambda L$;
--   2. the inventory cost rate $G(y) = E[h(y-D)^+ + p(D-y)^+]$ achieves its minimum at a unique point $y^0$.
--
--   Given a model, $G$, $c(Q,r)$, $r(Q)$, $y^0$, $H(Q)$, $H_0(Q)$, $C(Q)$ and $A(Q)$ are the objects of the $(Q,r)$ machinery at the cost rate $G$, and $G_d$, $r_d(Q)$, $H_d(Q)$, $A_d(Q)$ are the same objects at the EOQ cost rate $G_d(y) = h(y-\lambda L)^+ + p(\lambda L-y)^+$. An order quantity $Q$ is **optimal** if $Q>0$ and $C(Q)\le C(Q')$ for every $Q'>0$.
--
--   This bundles the paper's standing assumptions so that every theorem of the mission is stated about the same model.
--
--   **Formalization Note** The positivity of $K$ is implicit in the paper (at $K=0$ the optimal order quantity degenerates to $0$). No density is assumed: the paper's proofs differentiate $G$ twice, but none of its statements needs a density, and the Poisson demand of the paper's own numerical study has none. The unique-minimizer assumption is the paper's own ("For simplicity, we assume that $G(y)$ achieves its minimum at a unique point", p. 90).
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 88 (model), p. 90 (unique minimizer y⁰), p. 92 (optimal order quantity Q*), p. 94 (EOQ model, E(D) = λL)

import Mathlib
import Definitions.Def_ZhengQR_Flatness_costRates
import Definitions.Def_ZhengQR_Flatness_QRMachinery

namespace ZhengQR.Flatness

/-- The standing assumptions of Zheng (1992), pp. 88–90 and 94: demand rate `lam`, positive
fixed leadtime `L`, fixed ordering cost `K`, holding and backorder cost rates `h`, `p`, all
positive; a nonnegative, integrable leadtime demand `D ∼ μ` with `E(D) = λL`; and the
assumption that `G` achieves its minimum at a unique point `y⁰`. -/
structure QRModel where
  lam : ℝ
  L : ℝ
  K : ℝ
  h : ℝ
  p : ℝ
  μ : MeasureTheory.Measure ℝ
  isProb : MeasureTheory.IsProbabilityMeasure μ
  lam_pos : 0 < lam
  L_pos : 0 < L
  K_pos : 0 < K
  h_pos : 0 < h
  p_pos : 0 < p
  integrable : MeasureTheory.Integrable (fun x : ℝ => x) μ
  mean_eq : ∫ x, x ∂μ = lam * L
  demand_nonneg : ∀ᵐ x ∂μ, 0 ≤ x
  unique_min : ∃! y : ℝ, ∀ z : ℝ, newsvendorCost h p μ y ≤ newsvendorCost h p μ z

namespace QRModel

variable (M : QRModel)

/-- The stochastic inventory cost rate `G` (p. 88). -/
noncomputable def G : ℝ → ℝ := newsvendorCost M.h M.p M.μ
/-- The EOQ inventory cost rate `G_d` (p. 94). -/
noncomputable def Gd : ℝ → ℝ := eoqCost M.h M.p M.lam M.L
/-- `c(Q, r)`, Eq. (1). -/
noncomputable def c (Q r : ℝ) : ℝ := qrCost M.G M.lam M.K Q r
/-- `r(Q)`, the optimal reorder point for `Q` fixed (p. 90). -/
noncomputable def r (Q : ℝ) : ℝ := optReorder M.G M.lam M.K Q
/-- `y⁰`, the minimizer of `G` (p. 90). -/
noncomputable def y0 : ℝ := minPoint M.G
/-- `H(Q)`, Eq. (6). -/
noncomputable def H (Q : ℝ) : ℝ := Hfun M.G M.lam M.K Q
/-- `H₀(Q) = H(Q) - G(y⁰)` (p. 92). -/
noncomputable def H0 (Q : ℝ) : ℝ := Hzero M.G M.lam M.K Q
/-- `C(Q) = c(Q, r(Q))` (p. 91). -/
noncomputable def C (Q : ℝ) : ℝ := optCost M.G M.lam M.K Q
/-- `A(Q)`, Eq. (9). -/
noncomputable def A (Q : ℝ) : ℝ := Afun M.G M.lam M.K Q
/-- `r_d(Q)`: the optimal reorder point of the EOQ model for `Q` fixed, i.e. `r(Q)` at `G_d`
(p. 94). -/
noncomputable def rd (Q : ℝ) : ℝ := optReorder M.Gd M.lam M.K Q
/-- `H_d(Q)`: `H` of the EOQ model, i.e. Eq. (6) at `G_d` (p. 94). -/
noncomputable def Hd (Q : ℝ) : ℝ := Hfun M.Gd M.lam M.K Q
/-- `A_d(Q)`: `A` of the EOQ model, i.e. Eq. (9) at `G_d` (p. 94). -/
noncomputable def Ad (Q : ℝ) : ℝ := Afun M.Gd M.lam M.K Q

/-- `Q` is an optimal order quantity: `Q > 0` and `C(Q) ≤ C(Q')` for every `Q' > 0` (p. 92). -/
def IsOptQty (Q : ℝ) : Prop := 0 < Q ∧ ∀ Q' : ℝ, 0 < Q' → M.C Q ≤ M.C Q'

end QRModel

end ZhengQR.Flatness


