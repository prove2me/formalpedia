-- Prove2me | Definitions.Def_MetricMinTest_IsViolating
-- name    : MetricMinTest_IsViolating
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:48.255615+00:00
-- url     : https://prove2.me/theorems/501c4b64-ffd5-49db-9a2f-0fdb69fb361d
-- title:
--   Violating instance (some mean negative)
-- statement:
--   An instance is **violating** if some mean is negative, $\min_i\mu_i<0$. A valid tester must reject every violating instance of $\mathcal P_d$ with probability at least $1-\delta$. Instances with all means in $[0,\gamma)$ are unconstrained.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 2.1, p.6

import Mathlib
import Definitions.Def_MetricMinTest_Instance_mean

namespace MetricMinTest

/-- **Violating instance**: some mean is negative (`minᵢ µᵢ < 0`). Chen–Fang, *Minimum-Mean
Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb),
Definition 2.1 and the sentence after it, p.6. -/
def IsViolating {ι : Type} (P : Instance ι) : Prop :=
  ∃ i, P.mean i < 0

end MetricMinTest


