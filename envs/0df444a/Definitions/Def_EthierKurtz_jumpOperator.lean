-- Prove2me | Definitions.Def_EthierKurtz_jumpOperator
-- name    : EthierKurtz_jumpOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:27:16.230256+00:00
-- url     : https://prove2.me/theorems/49d7a0e7-15e2-40ca-88a5-ceac7b9bc73e
-- title:
--   Finite-rate jump operator
-- statement:
--   The jump rate times the transition-kernel expectation of the increment f(y) minus f(x).
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, equation (3.1), printed p. 376 (PDF p. 385).

import Mathlib

open MeasureTheory Filter
open scoped Topology ZeroAtInfty

namespace EthierKurtz

/-- Chapter 8 (3.1), the nonlocal jump operator. -/
noncomputable def jumpOperator {E : Type*} [MeasurableSpace E]
    (rate : E → ℝ) (μ : E → ProbabilityMeasure E) (f : E → ℝ) (x : E) : ℝ :=
  rate x * ∫ y, (f y - f x) ∂(μ x : Measure E)

end EthierKurtz


