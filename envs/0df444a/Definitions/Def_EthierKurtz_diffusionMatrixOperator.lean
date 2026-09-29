-- Prove2me | Definitions.Def_EthierKurtz_diffusionMatrixOperator
-- name    : EthierKurtz_diffusionMatrixOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:56:57.21598+00:00
-- url     : https://prove2.me/theorems/3a84f9d8-f19c-43d1-b3c3-02a8e5bfe0cd
-- title:
--   State-dependent diffusion generator
-- statement:
--   The second-order diffusion operator with one-half the covariance-weighted Hessian plus the drift directional derivative.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 7, Section 4, Theorem 4.1, displayed generator preceding the theorem, printed p. 354 (PDF p. 363).

import Mathlib

set_option autoImplicit true

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- Matrix-coordinate version of the existing `diffusionOperator` (Chapter 8).
No square root of a or ellipticity is imposed. -/
noncomputable def diffusionMatrixOperator {d : ℕ}
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin d, ∑ j : Fin d, a x i j *
    fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
      (EuclideanSpace.single i 1) + fderiv ℝ f x (b x)

end EthierKurtz


