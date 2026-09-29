-- Prove2me | Definitions.Def_EthierKurtz_sdeTestGenerator
-- name    : EthierKurtz_sdeTestGenerator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:51:49.671461+00:00
-- url     : https://prove2.me/theorems/9cf08e9a-950d-42d3-95a9-f5f753ee6ee6
-- title:
--   Time-dependent diffusion generator
-- statement:
--   The diffusion generator with covariance sigma sigma transpose, one-half the Hessian contraction, and the full drift derivative.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 3, equations (3.3)–(3.5), printed p. 291 (PDF p. 300).

import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace EthierKurtz

/-- Equations (3.3)–(3.5): the time-dependent operator on smooth compactly
supported spatial tests. The covariance is σσᵀ, even when σ is singular. -/
noncomputable def sdeTestGenerator {d : ℕ}
    (σ : ℝ≥0 × SDEState d → SDEDiffusion d)
    (b : ℝ≥0 × SDEState d → SDEState d)
    (f : SDEState d → ℝ) (t : ℝ≥0) (x : SDEState d) : ℝ :=
  (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d,
    (∑ k : Fin d, σ (t, x) (i, k) * σ (t, x) (j, k)) *
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1)) + fderiv ℝ f x (b (t, x))

end EthierKurtz


