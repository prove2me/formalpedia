-- Prove2me | Definitions.Def_WhitinPrice_LotSize_Model
-- name    : WhitinPrice_LotSize_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:32.24101+00:00
-- url     : https://prove2.me/theorems/6a5362db-4213-45dd-8adb-8c56137b71d6
-- title:
--   Section 2, Eqs. (1), (2), (5), (6) — linear demand, variable cost, and annual profit
-- statement:
--   A merchant sells a single item at price $p$ and faces annual demand $D(p)=ap+b$.
--   An order of $Q$ units incurs setup cost $S$; each unit of average inventory incurs
--   annual carrying cost $IC$; each unit demanded incurs operating cost $k$; and annual
--   fixed cost is $f$. The total variable cost and annual profit before choosing the lot
--   size are
--
--   $$
--   \operatorname{TVC}(D,Q)=\frac{Q}{2}IC+\frac{D}{Q}S+kD,
--   \qquad
--   \Pi(p,Q)=D(p)p-\operatorname{TVC}(D(p),Q)-f.
--   $$
--
--   The reduced profit obtained by substituting the economic lot size is
--
--   $$
--   P(p)=ap^2+bp-\sqrt{2SIC(ap+b)}-k(ap+b)-f.
--   $$
--
--   These definitions keep the ordering decision visible in the joint optimization
--   problem and supply the cost and profit functions used by the three milestones.
--
--   **Formalization Note** All quantities are real, as in the paper's continuous lot-size
--   calculation. The published EOQ cost supplies the first two terms of TVC. The functions
--   are total in Lean, but economic statements restrict to $Q>0$ and $D(p)>0$; $S,I,C>0$
--   are stated by the theorems. The paper calls annual profit $P$; `profit` names the
--   two-variable quantity, and `reducedProfit` names $P(p)$ after lot-size optimization.
-- source:
--   Whitin, Inventory Control and Price Theory, Management Sci. 2 (1955), pp. 61–62, Section 2, Eqs. (1), (2), (5), (6)

import Mathlib
import Definitions.Def_InventoryControl_eoq

namespace WhitinPrice.LotSize

/-- Whitin (1955), §2, Eq. (1): annual demand at price `p`. -/
def demand (a b p : ℝ) : ℝ := a * p + b

/-- Whitin (1955), §2, Eq. (2): annual variable cost at demand `D` and lot size `Q`.
The EOQ terms are the published `InventoryControl.eoqCost`. -/
noncomputable def tvc (S I C k D Q : ℝ) : ℝ :=
  InventoryControl.eoqCost S D (I * C) Q + k * D

/-- Annual profit before optimizing the lot size; this is the two-variable model
from which Whitin obtains Eqs. (5) and (6). -/
noncomputable def profit (S I C k f a b p Q : ℝ) : ℝ :=
  demand a b p * p - tvc S I C k (demand a b p) Q - f

/-- Whitin (1955), §2, Eq. (6): annual profit after substituting the EOQ lot size. -/
noncomputable def reducedProfit (S I C k f a b p : ℝ) : ℝ :=
  a * p ^ 2 + b * p - Real.sqrt (2 * S * I * C * (a * p + b))
    - k * (a * p + b) - f

end WhitinPrice.LotSize


