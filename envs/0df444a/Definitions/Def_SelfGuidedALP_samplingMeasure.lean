-- Prove2me | Definitions.Def_SelfGuidedALP_samplingMeasure
-- name    : SelfGuidedALP_samplingMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:41.464695+00:00
-- url     : https://prove2.me/theorems/23855db3-9a49-4f50-8236-3235e4357e7b
-- title:
--   The sampling distribution with density $\rho$
-- statement:
--   The **sampling distribution** is the measure $\rho(\theta)\,\mathrm d\theta$ on $\Theta$. It is a probability measure because $\int_\Theta\rho=1$.
--
--   All randomness of the mission comes from iid draws from this law.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, §2.2, p.8

import Mathlib
import Definitions.Def_SelfGuidedALP_RBClass

open MeasureTheory

namespace SelfGuidedALP

/-- The sampling distribution with density `ρ` on `Θ`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, §2.2, p.8). -/
noncomputable def samplingMeasure {d : ℕ} (R : RBClass d) : Measure (EuclideanSpace ℝ (Fin (d + 1))) :=
  (volume.restrict R.Θ).withDensity fun θ => ENNReal.ofReal (R.ρ θ)

end SelfGuidedALP


