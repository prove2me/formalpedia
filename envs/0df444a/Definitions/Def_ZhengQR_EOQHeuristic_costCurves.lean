-- Prove2me | Definitions.Def_ZhengQR_EOQHeuristic_costCurves
-- name    : ZhengQR_EOQHeuristic_costCurves
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:39:30.090348+00:00
-- url     : https://prove2.me/theorems/a95d9a75-9e7a-443c-b135-69be4afbb2f1
-- title:
--   Eqs. (6), (9): $H(Q) = G(r(Q))$, $H_0$, $C(Q) = c(Q, r(Q))$, $A(Q)$ and the optimal order quantity $Q^*$
-- statement:
--   Fix an inventory-cost rate $G$, demand rate $\lambda$ and fixed ordering cost $K$, and let $r(Q)$ and $y^0$ be as in Eq. (1)'s definitions. Define, for order quantities $Q \ge 0$,
--
--   $$H(Q) = G(r(Q)) \ (Q > 0), \qquad H(0) = G(y^0), \qquad (6)$$
--
--   $$H_0(Q) = H(Q) - G(y^0), \qquad C(Q) = c(Q, r(Q)), \qquad A(Q) = Q\,H(Q) - \int_0^Q H(y)\,dy. \qquad (9)$$
--
--   $C(Q)$ is the average cost when the reorder point is chosen optimally for $Q$. An order quantity $Q$ is **optimal** ($Q = Q^*$, p. 92) if $Q > 0$ and $C(Q) \le C(Q')$ for every $Q' > 0$.
--
--   These are the cost curves in which all of the paper's comparisons between the stochastic and the EOQ model are phrased.
--
--   **Formalization Note** The paper defines $H(0)$ as $\lim_{Q\to0^+} G(r(Q))$ and asserts that it equals $G(y^0)$; here $H(0) := G(y^0)$ is the definition, and the continuity at $0$ is part of the Lemma 4 milestone. The value of $H$ at $Q < 0$ is a placeholder that no statement uses. $C$ is meaningful only for $Q > 0$.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 91, Eq. (6) and C(Q); p. 92, Eq. (9), H₀ and Q*

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost

namespace ZhengQR.EOQHeuristic

/-- Eq. (6), p. 91: `H(Q) = G(r(Q))` for `Q > 0`, and `H(0) = G(y⁰)` (the value the paper assigns
at `0`). The value for `Q < 0` is a placeholder and is never used. -/
noncomputable def hFun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  if 0 < Q then G (reorderPt G lam K Q) else G (minPt G)

/-- `H₀(Q) = H(Q) − G(y⁰)`, p. 92. -/
noncomputable def h0Fun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  hFun G lam K Q - G (minPt G)

/-- `C(Q) = c(Q, r(Q))`, p. 91: the average cost when the reorder point is chosen optimally for
the order quantity `Q`. Meaningful for `Q > 0` only. -/
noncomputable def optCost (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  qrCost G lam K Q (reorderPt G lam K Q)

/-- Eq. (9), p. 92: `A(Q) = Q H(Q) − ∫_0^Q H(y) dy`. -/
noncomputable def aFun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  Q * hFun G lam K Q - ∫ y in (0 : ℝ)..Q, hFun G lam K y

/-- `Q` is an optimal order quantity (p. 92, `Q*`): `Q > 0` and `C(Q) ≤ C(Q')` for every `Q' > 0`. -/
def IsOptQty (G : ℝ → ℝ) (lam K Q : ℝ) : Prop :=
  0 < Q ∧ ∀ Q' : ℝ, 0 < Q' → optCost G lam K Q ≤ optCost G lam K Q'

end ZhengQR.EOQHeuristic


