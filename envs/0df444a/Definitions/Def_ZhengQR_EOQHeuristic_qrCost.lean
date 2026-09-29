-- Prove2me | Definitions.Def_ZhengQR_EOQHeuristic_qrCost
-- name    : ZhengQR_EOQHeuristic_qrCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:38:44.171984+00:00
-- url     : https://prove2.me/theorems/6a094251-53fe-43fa-ad45-392d19d1875f
-- title:
--   Eq. (1): the average cost $c(Q, r) = (\lambda K + \int_r^{r+Q} G(y)dy)/Q$, the optimal reorder point $r(Q)$ and $y^0$
-- statement:
--   Let $G : \mathbb{R} \to \mathbb{R}$ be an inventory-cost rate, $\lambda$ the demand rate and $K$ the fixed ordering cost. The long-run average cost of the $(Q, r)$ policy with order quantity $Q > 0$ and reorder point $r$ is
--
--   $$c(Q, r) = \frac{\lambda K + \int_r^{r+Q} G(y)\,dy}{Q}. \qquad (1)$$
--
--   A reorder point $r$ is **optimal for the fixed order quantity** $Q$ if it minimises $c(Q,\cdot)$ over all of $\mathbb{R}$. The function $r(Q)$ ("an optimal $r$ for $Q$ fixed", p. 90) is a chosen such minimiser, and $y^0$ is a chosen global minimiser of $G$.
--
--   These objects are defined for an arbitrary $G$ so that the same machinery applies both to the stochastic model (the newsvendor cost) and to the EOQ model ($G_d$).
--
--   **Formalization Note** $c(Q,r)$ is meaningful only for $Q > 0$; every statement about it assumes $Q > 0$. $r(Q)$ is defined as a minimiser of $c(Q,\cdot)$, not through the equation $G(r) = G(r+Q)$, which is Lemma 2. When no minimiser exists, $r(Q)$ and $y^0$ take the placeholder value $0$; under the standing assumptions both minimisers exist and are unique, so the placeholder is never used.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 88, Eq. (1); p. 90 (r(Q), y⁰)

import Mathlib

namespace ZhengQR.EOQHeuristic

/-- Eq. (1) of Zheng (1992), p. 88: the long-run average cost of the `(Q, r)` policy with order
quantity `Q` and reorder point `r`, for an inventory-cost rate `G`, demand rate `lam` and fixed
ordering cost `K`: `c(Q, r) = (λK + ∫_r^{r+Q} G(y) dy) / Q`. Meaningful for `Q > 0` only. -/
noncomputable def qrCost (G : ℝ → ℝ) (lam K Q r : ℝ) : ℝ :=
  (lam * K + ∫ y in r..r + Q, G y) / Q

/-- `r` is an optimal reorder point for the fixed order quantity `Q` (p. 90: "an optimal `r` for
`Q` fixed"): it minimizes `c(Q, ·)` over all of `ℝ`. -/
def IsOptReorder (G : ℝ → ℝ) (lam K Q r : ℝ) : Prop :=
  ∀ r' : ℝ, qrCost G lam K Q r ≤ qrCost G lam K Q r'

open Classical in
/-- `r(Q)` (p. 90): a chosen minimizer of `c(Q, ·)`; `0` if no minimizer exists. -/
noncomputable def reorderPt (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  if hr : ∃ r, IsOptReorder G lam K Q r then hr.choose else 0

open Classical in
/-- `y⁰` (p. 90): a chosen global minimizer of `G`; `0` if `G` has no minimizer. -/
noncomputable def minPt (G : ℝ → ℝ) : ℝ :=
  if hy : ∃ y, ∀ z, G y ≤ G z then hy.choose else 0

end ZhengQR.EOQHeuristic


