-- Prove2me | Definitions.Def_EthierKurtz_SDEState
-- name    : EthierKurtz_SDEState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:46:26.927319+00:00
-- url     : https://prove2.me/theorems/94f89378-9bfb-4153-956d-d2e81d044420
-- title:
--   Euclidean state space
-- statement:
--   The d-dimensional Euclidean state space indexed by Fin d.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 3, equations (3.1), (3.33)–(3.35), printed pp. 290, 299–300 (PDF pp. 299, 308–309).

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- Euclidean state space with the source's Euclidean norm. -/
abbrev SDEState (d : ℕ) := EuclideanSpace ℝ (Fin d)

end EthierKurtz


