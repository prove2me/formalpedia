-- Prove2me | Definitions.Def_EthierKurtz_IsStandardBrownian
-- name    : EthierKurtz_IsStandardBrownian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:47:03.903705+00:00
-- url     : https://prove2.me/theorems/a36910ec-fa61-41eb-9372-3f1c14f64ed9
-- title:
--   Standard multidimensional Brownian motion
-- statement:
--   Measurable continuous scalar Brownian coordinates whose coordinate processes are independent.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5 Brownian convention, printed p. 276 (PDF p. 285).

import Definitions.Def_EthierKurtz_SDEState

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Independent scalar Brownian coordinate processes give standard d-dimensional
Brownian motion. Source paths are continuous and time evaluations measurable. -/
def IsStandardBrownian (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d) : Prop :=
  (∀ t, Measurable (W t)) ∧
  (∀ ω, Continuous (fun t => W t ω)) ∧
  (∀ i, IsBrownianReal (fun t ω => W t ω i) P) ∧
  iIndepFun (fun i ω t => W t ω i) P

end EthierKurtz


