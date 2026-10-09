-- Prove2me | Definitions.Def_actuarial_tailRiskStrictMass
-- name    : actuarial_tailRiskStrictMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:51:17.154881+00:00
-- url     : https://prove2.me/theorems/2497ede2-8a23-4d24-aec7-52928dad0d52
-- title:
--   Strict aggregate-loss tail above a quantile
-- statement:
--   The strict tail contains probability mass at losses strictly greater than the selected quantile q, over the bounded integer loss grid. Any mass at the quantile itself is intentionally excluded because fractional allocation of that atom requires a separate calculation.
--
--   **Mathematical statement**
--
--   $$
--   T_B(q)=\sum_{s=q+1}^{B}w_s
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib

namespace ActuarialValuation

noncomputable def tailRiskStrictMass
  (w : ℕ → ℝ) (bound q : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (bound + 1), if q < s then w s else 0

end ActuarialValuation


