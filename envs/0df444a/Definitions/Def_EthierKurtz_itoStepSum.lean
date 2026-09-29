-- Prove2me | Definitions.Def_EthierKurtz_itoStepSum
-- name    : EthierKurtz_itoStepSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:44:09.789991+00:00
-- url     : https://prove2.me/theorems/9c3db194-2bed-44d0-8134-751fdb144b29
-- title:
--   Left-point dyadic stochastic sum
-- statement:
--   The finite sum of left-endpoint integrand values times scalar increments over a uniform dyadic partition.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 2, stochastic integration conventions, printed pp. 279–280 (PDF pp. 288–289).

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The stochastic integral of the elementary integrand, a finite Itô sum. -/
noncomputable def itoStepSum (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ)
    (a : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), a k ω *
    (W (((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n) ω -
      W ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n) ω)

end EthierKurtz


