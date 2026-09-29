-- Prove2me | Definitions.Def_EthierKurtz_HasContinuousMartingaleIntegral
-- name    : EthierKurtz_HasContinuousMartingaleIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:45:15.908489+00:00
-- url     : https://prove2.me/theorems/501998e3-8e5b-45cc-8ec8-7efa023d8be9
-- title:
--   Continuous local-martingale integral relation
-- statement:
--   Left dyadic sums converge in probability at each time to a continuous adapted stochastic-integral version.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 2 and Theorem 2.9, printed pp. 280, 286–287 (PDF pp. 289, 295–296).

import Definitions.Def_EthierKurtz_itoStepSum

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The continuous adapted version of the stochastic integral, for the
continuous adapted integrands in Theorem 2.9. Local martingale integrators
need no Brownian or absolute-continuity hypothesis. Left sums converge in
probability at each time; continuity makes the version unique up to
indistinguishability. -/
def HasContinuousMartingaleIntegral (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M H J : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ ω, Continuous (fun t => J t ω)) ∧ Adapted ℱ J ∧
  ∀ t, TendstoInMeasure P
    (fun n => itoStepSum M t n (fun k => H ((k : ℝ≥0) * t / 2 ^ n)))
    atTop (J t)

end EthierKurtz


