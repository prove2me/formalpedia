-- Prove2me | Definitions.Def_EthierKurtz_weightedJumpGraph
-- name    : EthierKurtz_weightedJumpGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:27:55.321419+00:00
-- url     : https://prove2.me/theorems/96c0d792-0a9d-4398-8a7e-d652d98a4f90
-- title:
--   Weighted finite-rate jump graph
-- statement:
--   The graph of the jump operator on functions for which the weighted function and operator image belong to C₀.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, equations (3.1)–(3.5) and Theorem 3.1, printed pp. 376–377 (PDF pp. 385–386).

import Definitions.Def_EthierKurtz_jumpOperator

open MeasureTheory Filter
open scoped Topology ZeroAtInfty

namespace EthierKurtz

/-- The weighted graph in C₀ × C₀, including the source's requirement Af ∈ C₀. -/
def weightedJumpGraph {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (rate γ : E → ℝ) (μ : E → ProbabilityMeasure E) :
    Set (C₀(E, ℝ) × C₀(E, ℝ)) :=
  {fg | (∃ h : C₀(E, ℝ), ∀ x, h x = γ x * fg.1 x) ∧
    ∀ x, fg.2 x = jumpOperator rate μ fg.1 x}

end EthierKurtz


