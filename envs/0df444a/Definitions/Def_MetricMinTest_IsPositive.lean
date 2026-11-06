-- Prove2me | Definitions.Def_MetricMinTest_IsPositive
-- name    : MetricMinTest_IsPositive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:05.570296+00:00
-- url     : https://prove2.me/theorems/e35a92a8-ac38-4d59-99ac-149bb8925641
-- title:
--   Positive instances $\mathcal P_d^+(\gamma)$
-- statement:
--   For a margin $\gamma$, the **positive** instances are
--   $$\mathcal P_d^+(\gamma)=\{P\in\mathcal P_d : \min_i\mu_i\ge\gamma\}.$$
--   A valid tester must accept them with probability at least $1-\delta$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §2, p.6

import Mathlib
import Definitions.Def_MetricMinTest_InClass

namespace MetricMinTest

/-- **Positive instances `P_d^+(γ)`.** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §2 p.6:
`P_d^+(γ) = {P ∈ P_d : minᵢ µᵢ ≥ γ}`. -/
def IsPositive {ι : Type} (d : ι → ι → ℝ) (γ : ℝ) (P : Instance ι) : Prop :=
  InClass d P ∧ ∀ i, γ ≤ P.mean i

end MetricMinTest


