-- Prove2me | Definitions.Def_actuarial_tailRiskSelectedLoss
-- name    : actuarial_tailRiskSelectedLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:52:34.818474+00:00
-- url     : https://prove2.me/theorems/d296eba6-dd3e-45ac-a352-2b44cc53dda1
-- title:
--   Aggregate monetary loss in the worst probability tail
-- statement:
--   The top one-minus-alpha probability of losses includes all payments strictly above quantile q and exactly the required fraction of observations at q. This numerator does not discard or fully include the quantile atom unless the confidence boundary makes that choice correct.
--
--   **Mathematical statement**
--
--   $$
--   A_B(q,\alpha)=\sum_{s>q}sw_s+q\,a_q
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskAtomWeight

namespace ActuarialValuation

noncomputable def tailRiskSelectedLoss
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ) : ℝ :=
  (∑ s ∈ Finset.range (bound + 1),
    if q < s then (s : ℝ) * w s else 0) +
      (q : ℝ) * tailRiskAtomWeight w bound q alpha

end ActuarialValuation


