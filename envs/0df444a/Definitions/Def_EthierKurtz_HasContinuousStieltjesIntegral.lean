-- Prove2me | Definitions.Def_EthierKurtz_HasContinuousStieltjesIntegral
-- name    : EthierKurtz_HasContinuousStieltjesIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:44:33.989925+00:00
-- url     : https://prove2.me/theorems/36f8e605-c45a-4b50-84ed-74c379a05446
-- title:
--   Continuous Stieltjes integral relation
-- statement:
--   A continuous finite-variation integrator and continuous integrand have left dyadic sums converging pathwise to the stated integral process.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 2 and Theorem 2.9, printed pp. 280, 287 (PDF pp. 289, 296).

import Definitions.Def_EthierKurtz_itoStepSum

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω]

/-- For continuous H and a continuous finite-variation integrator A, the
pathwise Stieltjes integral is the limit of left dyadic sums. No default-valued
integral operator and no assumed change-of-variable identity is used. -/
def HasContinuousStieltjesIntegral (A H K : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ ω t, Tendsto
    (fun n => itoStepSum A t n (fun k => H ((k : ℝ≥0) * t / 2 ^ n)) ω)
    atTop (𝓝 (K t ω))

end EthierKurtz


