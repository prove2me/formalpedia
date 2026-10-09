-- Prove2me | Definitions.Def_actuarial_tailRiskStopLoss
-- name    : actuarial_tailRiskStopLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:51:33.374393+00:00
-- url     : https://prove2.me/theorems/e2ea3d8e-2161-4c0f-9cc4-8df2b592496e
-- title:
--   Expected excess loss above a chosen integer quantile
-- statement:
--   The net stop-loss transform at attachment q is the finite expected positive part of realised aggregate loss minus q. Natural subtraction is zero below attachment, so the transform precisely captures severity in excess of the quantile.
--
--   **Mathematical statement**
--
--   $$
--   \Pi_B(q)=\sum_{s=0}^{B}(s-q)_+w_s
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib

namespace ActuarialValuation

noncomputable def tailRiskStopLoss
  (w : ℕ → ℝ) (bound q : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (bound + 1),
    ((s - q : ℕ) : ℝ) * w s

end ActuarialValuation


