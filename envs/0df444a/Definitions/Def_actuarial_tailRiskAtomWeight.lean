-- Prove2me | Definitions.Def_actuarial_tailRiskAtomWeight
-- name    : actuarial_tailRiskAtomWeight
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:52:01.446097+00:00
-- url     : https://prove2.me/theorems/393541e4-6db2-4434-85db-c2256307c544
-- title:
--   Fraction of the quantile atom needed to fill the worst tail
-- statement:
--   The target worst tail has probability one minus confidence alpha. Since losses strictly exceeding q may provide less probability than this target, the residual mass must be selected from the observations exactly equal to q. A legitimate fractional atom requires tail≤1−alpha≤tail+w(q).
--
--   **Mathematical statement**
--
--   $$
--   a_q=(1-\alpha)-T_B(q)
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskStrictMass

namespace ActuarialValuation

noncomputable def tailRiskAtomWeight
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ) : ℝ :=
  (1 - alpha) - tailRiskStrictMass w bound q

end ActuarialValuation


