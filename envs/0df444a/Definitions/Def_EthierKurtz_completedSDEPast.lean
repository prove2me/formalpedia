-- Prove2me | Definitions.Def_EthierKurtz_completedSDEPast
-- name    : EthierKurtz_completedSDEPast
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:49:37.838987+00:00
-- url     : https://prove2.me/theorems/8bbfbb2d-dd9f-492e-b9c9-b9d9c39bc322
-- title:
--   Completed filtration past
-- statement:
--   An arbitrary filtration augmented by all subsets of ambient measurable null sets.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 3 solution convention, printed p. 291 (PDF p. 300).

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- Source p. 291: augment a filtration by subsets of all ambient measurable
null sets, rather than only the null sets already measurable in the past. -/
abbrev completedSDEPast {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (t : ℝ≥0) : MeasurableSpace Ω :=
  ℱ t ⊔ MeasurableSpace.generateFrom
    {A | ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ A ⊆ N}

end EthierKurtz


