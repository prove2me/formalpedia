-- Prove2me | Definitions.Def_actuarial_tailRiskTVaR
-- name    : actuarial_tailRiskTVaR
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:53:39.923519+00:00
-- url     : https://prove2.me/theorems/ee9906d9-51eb-4c77-9801-fe02f690db54
-- title:
--   Tie-adjusted finite discrete tail value-at-risk
-- statement:
--   Tail value-at-risk is the monetary mean of the worst one-minus-alpha probability portion of aggregate outcomes, with ties at the quantile fractionally allocated. The numerator is a finite sum, and alpha<1 is required for a positive denominator.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{TVaR}_\alpha=A_B(q,\alpha)/(1-\alpha)
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskSelectedLoss

namespace ActuarialValuation

noncomputable def tailRiskTVaR
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ) : ℝ :=
  tailRiskSelectedLoss w bound q alpha / (1 - alpha)

end ActuarialValuation


