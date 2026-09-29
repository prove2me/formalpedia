-- Prove2me | Definitions.Def_EthierKurtz_levyTypeOperator
-- name    : EthierKurtz_levyTypeOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:25:31.792877+00:00
-- url     : https://prove2.me/theorems/ade6afc4-e2c9-4a89-8852-ad82ff72e335
-- title:
--   Compensated nonautonomous Lévy-type operator
-- statement:
--   The diffusion part plus the compensated jump integral with denominator one plus the squared jump norm.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, equation (3.21), printed p. 379 (PDF p. 388).

import Definitions.Def_EthierKurtz_diffusionOperator

open MeasureTheory Filter
open scoped NNReal Topology ContDiff

namespace EthierKurtz

/-- The exact compensated nonlocal operator (3.21); the finite-dimensional
Fréchet differential applied to y is y dot grad f. -/
noncomputable def levyTypeOperator {d : ℕ}
    (a : ℝ≥0 × EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : ℝ≥0 × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ν : ℝ≥0 × EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ≥0)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  diffusionOperator (fun y => a (t, y)) (fun y => b (t, y)) f x +
    ∫ y, (f (x + y) - f x - fderiv ℝ f x y / (1 + ‖y‖ ^ 2)) ∂(ν (t, x))

end EthierKurtz


