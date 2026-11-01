-- Prove2me | Definitions.Def_SelfGuidedALP_iidLaw
-- name    : SelfGuidedALP_iidLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:48.144303+00:00
-- url     : https://prove2.me/theorems/78dd6673-7c39-464f-a3cb-e7072df657ee
-- title:
--   The law of $n$ iid samples from $\rho$
-- statement:
--   The law of $n$ iid samples $\theta^1,\dots,\theta^n$ from $\rho$ is the $n$-fold product of the sampling distribution.
--
--   This is the probability space of every high-probability statement of the mission.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, §3.1, p.10

import Mathlib
import Definitions.Def_SelfGuidedALP_samplingMeasure

open MeasureTheory

namespace SelfGuidedALP

/-- The law of `n` iid samples `θ¹, …, θⁿ` from `ρ`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, §3.1, p.10). -/
noncomputable def iidLaw {d : ℕ} (R : RBClass d) (n : ℕ) :
    Measure (Fin n → EuclideanSpace ℝ (Fin (d + 1))) :=
  Measure.pi fun _ => samplingMeasure R

end SelfGuidedALP


