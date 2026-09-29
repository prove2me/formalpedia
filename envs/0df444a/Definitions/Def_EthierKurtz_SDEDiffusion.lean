-- Prove2me | Definitions.Def_EthierKurtz_SDEDiffusion
-- name    : EthierKurtz_SDEDiffusion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:46:36.945848+00:00
-- url     : https://prove2.me/theorems/27065db4-aa51-4131-a56e-28323aa08af9
-- title:
--   Euclidean diffusion matrix space
-- statement:
--   The d by d real diffusion matrix represented with its Euclidean, or Frobenius, norm.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 3, equations (3.1), (3.33)–(3.35), printed pp. 290, 299–300 (PDF pp. 299, 308–309).

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- A d by d matrix, flattened to retain the Euclidean (Frobenius) norm. -/
abbrev SDEDiffusion (d : ℕ) := EuclideanSpace ℝ (Fin d × Fin d)

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end EthierKurtz


