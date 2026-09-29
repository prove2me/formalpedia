-- Prove2me | Definitions.Def_EthierKurtz_diffusionGraph
-- name    : EthierKurtz_diffusionGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:02:27.918213+00:00
-- url     : https://prove2.me/theorems/55e68ae7-a098-4163-bb82-b8ac95212274
-- title:
--   Smooth compactly supported diffusion graph
-- statement:
--   The graph in C₀ × C₀ consisting of every smooth compactly supported function paired with its diffusion-operator image.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 1, equation (1.15) and Theorem 1.6, printed pp. 368, 370 (PDF pp. 377, 379).

import Definitions.Def_EthierKurtz_diffusionOperator

open Filter
open scoped Topology ZeroAtInfty ContDiff

namespace EthierKurtz

/-- The actual smooth compactly supported graph in C₀ × C₀. No arbitrary
extension of G or unproved membership witness is introduced. -/
def diffusionGraph {d : ℕ}
    (a : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Set (C₀(EuclideanSpace ℝ (Fin d), ℝ) × C₀(EuclideanSpace ℝ (Fin d), ℝ)) :=
  {fg | ContDiff ℝ ∞ (fg.1 : EuclideanSpace ℝ (Fin d) → ℝ) ∧
    HasCompactSupport (fg.1 : EuclideanSpace ℝ (Fin d) → ℝ) ∧
    ∀ x, fg.2 x = diffusionOperator a b fg.1 x}

end EthierKurtz


