-- Prove2me | Definitions.Def_auto_M05_f3f59_EthierKurtz_HasContinuousStieltjesIntegral
-- name    : auto_M05_f3f59_EthierKurtz_HasContinuousStieltjesIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T18:51:28.631805+00:00
-- url     : https://prove2.me/theorems/8f5d7aa5-d8c9-4ebd-a6d9-79c86eea3bce
-- title:
--   Continuous Stieltjes integral relation
-- statement:
--   For each path and time, left dyadic sums converge to the specified integral value. For continuous integrands and continuous locally finite-variation integrators this characterizes the pathwise Stieltjes integral.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 5 §2, Theorem 2.9, printed p.287 (PDF p.296), equations (2.40)–(2.41); conventions pp.279–280,286 (PDF pp.288–289,295). https://doi.org/10.1002/9780470316658.ch5

import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω]

def HasContinuousStieltjesIntegral (A H K : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ ω t, Tendsto
    (fun n => itoStepSum A t n (fun k => H ((k : ℝ≥0) * t / 2 ^ n)) ω)
    atTop (𝓝 (K t ω))

end EthierKurtz


