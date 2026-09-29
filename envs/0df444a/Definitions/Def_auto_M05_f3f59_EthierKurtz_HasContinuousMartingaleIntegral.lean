-- Prove2me | Definitions.Def_auto_M05_f3f59_EthierKurtz_HasContinuousMartingaleIntegral
-- name    : auto_M05_f3f59_EthierKurtz_HasContinuousMartingaleIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T18:52:19.123661+00:00
-- url     : https://prove2.me/theorems/99e8b990-abc6-467b-abc1-bc55d5da6881
-- title:
--   Continuous local-martingale integral relation
-- statement:
--   The proposed integral is continuous and adapted, and at each time the left dyadic sums converge in probability to its value. For continuous adapted integrands against continuous local martingales this specifies the continuous stochastic-integral version.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 5 §2, Theorem 2.9, printed p.287 (PDF p.296), equations (2.40)–(2.41); conventions pp.279–280,286 (PDF pp.288–289,295). https://doi.org/10.1002/9780470316658.ch5

import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasContinuousStieltjesIntegral

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω]

def HasContinuousMartingaleIntegral (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M H J : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ ω, Continuous (fun t => J t ω)) ∧ Adapted ℱ J ∧
  ∀ t, TendstoInMeasure P
    (fun n => itoStepSum M t n (fun k => H ((k : ℝ≥0) * t / 2 ^ n)))
    atTop (J t)

end EthierKurtz


