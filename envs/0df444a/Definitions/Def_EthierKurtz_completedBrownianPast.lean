-- Prove2me | Definitions.Def_EthierKurtz_completedBrownianPast
-- name    : EthierKurtz_completedBrownianPast
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:47:42.834565+00:00
-- url     : https://prove2.me/theorems/b694e6bd-5f16-46cc-afcb-d56d0b98259a
-- title:
--   Completed Brownian and initial-data past
-- statement:
--   The natural Brownian past joined with the initial variable and completed by subsets of ambient measurable null sets.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 3 solution convention, printed p. 291 (PDF p. 300).

import Definitions.Def_EthierKurtz_SDEState

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The P-completion of the natural Brownian past joined with the initial variable.
Null subsets come from the AMBIENT sigma algebra, as specified on source p. 291. -/
abbrev completedBrownianPast (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (ξ : Ω → SDEState d) (t : ℝ≥0) : MeasurableSpace Ω :=
  (⨆ s : Set.Iic t, MeasurableSpace.comap (W s.val) inferInstance) ⊔
    MeasurableSpace.comap ξ inferInstance ⊔
    MeasurableSpace.generateFrom {A | ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ A ⊆ N}

end EthierKurtz


